//! Port of the emit parts of Go `compiler/program.go` (`Emit`,
//! `CombineEmitResults`, `HandleNoEmitOnError`, the emit option and result
//! types). The emit host (`program::EmitHost`) and the output paths
//! (`program::get_output_paths_for_source_file`) are in `program.rs`, where
//! the declaration diagnostics use them too.

use crate::prelude::*;

use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::{Arc, Mutex, PoisonError};

use super::emitter::{EmitOnly, Emitter, js_emit_needs_checker};
use crate::sourcemap::generator::RawSourceMap;

// Go: compiler/program.go:1600 WriteFileData
#[derive(Clone, Debug, Default)]
pub struct WriteFileData {
    pub source_map_url_pos: i32,
    // PORT: Go uses `any` to avoid an import cycle. It is `Arc` because the
    // write callback is thread safe. Only the build info write sets it
    // (incremental `emit_build_info`).
    pub build_info: Option<Arc<crate::execute::incremental::BuildInfo>>,
    pub diagnostics: Vec<Diagnostic>,
    pub skipped_dts_write: bool,
}

// Go: compiler/program.go:1607 WriteFile
// PORT: Go `error` is `Result<(), String>`. Emit runs on the checker
// threads and the emit pool, so the callback is shared and thread safe. The
// callback may set `skipped_dts_write`.
pub type WriteFile =
    Arc<dyn Fn(&str, &str, &mut WriteFileData) -> Result<(), String> + Send + Sync>;

// Go: compiler/program.go:1609 EmitOptions
#[derive(Clone, Default)]
pub struct EmitOptions {
    /// Single file to emit. If nil, emits all files
    pub target_source_file: Node,
    pub emit_only: EmitOnly,
    pub write_file: Option<WriteFile>,
}

// Go: compiler/program.go:1615 EmitResult
#[derive(Clone, Debug, Default)]
pub struct EmitResult {
    pub emit_skipped: bool,
    /// Contains declaration emit diagnostics
    pub diagnostics: Vec<Diagnostic>,
    /// Array of files the compiler wrote to disk
    pub emitted_files: Vec<String>,
    /// Array of sourceMapData if compiler emitted sourcemaps
    pub source_maps: Vec<SourceMapEmitResult>,
}

// Go: compiler/program.go:1622 SourceMapEmitResult
#[derive(Clone, Debug, Default)]
pub struct SourceMapEmitResult {
    /// Input source file (which one can use on program to get the file), 1:1 mapping with the sourceMap.sources list
    pub input_source_file_names: Vec<String>,
    pub source_map: RawSourceMap,
    pub generated_file: String,
}

// Go: compiler/program.go:1628 Program.Emit
// PORT: Go queues one emit per file on a work group and takes a writer from
// a pool. Each file's emit runs on the thread of its checker (the emit
// resolver reaches that checker there), and the results combine in file
// order. Each emit makes its own text writer. When the emit pool is on
// (`program::emit_pool_enabled`), the JS part of a file whose transforms
// make no checker call runs on the pool instead (`emit_files_with_pool`).
pub fn emit(options: EmitOptions) -> EmitResult {
    emit_with(options, |emit_file| emit_file())
}

/// `emit` with `wrap` around each file's emit, on the file's checker
/// thread. `goport` uses it to guard each file on its own. When a file's
/// emit is split, `wrap` is around each part: a panic in one part does not
/// stop the other.
pub fn emit_with(
    options: EmitOptions,
    wrap: fn(&dyn Fn() -> EmitResult) -> EmitResult,
) -> EmitResult {
    let _trace = trace_emit();
    if options.emit_only != EmitOnly::ForcedDts {
        if let Some(result) = handle_no_emit_on_error(options.target_source_file) {
            return result;
        }
    }

    let source_files = get_source_files_to_emit(
        options.target_source_file,
        options.emit_only == EmitOnly::ForcedDts,
    );
    let emit_only = options.emit_only;
    let write_file = options.write_file.clone();
    let pooled = emit_files_with_pool(&source_files, |_| (emit_only, write_file.clone()), wrap);
    let results = match pooled {
        Some(results) => results,
        None => run_emit_jobs(source_files, move |source_file| {
            wrap(&|| emit_source_file(source_file, emit_only, write_file.clone()))
        }),
    };

    // collect results from emit, preserving input order
    combine_emit_results(results)
}

/// `emit` for many targets at once, one result per target in input order.
pub fn emit_batch(targets: Vec<EmitOptions>) -> Vec<EmitResult> {
    emit_batch_with(targets, |emit_file| emit_file())
}

/// `emit_with` for many targets at once, one result per target in input
/// order. Each result is the same as `emit_with` of that target alone.
///
/// Go `emitFilesIncremental` calls `Program.Emit` for each pending file
/// inside a work group, so the files emit in parallel. `emit_files_incremental`
/// builds one `EmitOptions` per pending file (one target file each, from
/// `get_emit_options`) and calls this once instead of `emit` per file.
/// Each checker thread runs its files in `targets` order, also with
/// `--singleThreaded`.
///
/// Each target must name one source file, and no file can be in the batch
/// twice. With `noEmitOnError` each target runs through `emit_with`, one at
/// a time, because the diagnostics check must come first.
pub fn emit_batch_with(
    targets: Vec<EmitOptions>,
    wrap: fn(&dyn Fn() -> EmitResult) -> EmitResult,
) -> Vec<EmitResult> {
    if options().no_emit_on_error.is_true() {
        return targets
            .into_iter()
            .map(|target| emit_with(target, wrap))
            .collect();
    }

    // Without `noEmitOnError`, `handle_no_emit_on_error` returns None, so
    // `emit_with` of one target is only the emit of its 0 or 1 file.
    let mut files = Vec::new();
    let mut has_file = Vec::with_capacity(targets.len());
    let mut file_targets: FxHashMap<Node, (EmitOnly, Option<WriteFile>)> = FxHashMap::default();
    for target in targets {
        debug_assert!(
            target.target_source_file.is_some(),
            "emit_batch target without a file"
        );
        let force_dts_emit = target.emit_only == EmitOnly::ForcedDts;
        let file = get_source_files_to_emit(target.target_source_file, force_dts_emit)
            .first()
            .copied();
        has_file.push(file.is_some());
        match file {
            Some(file) => {
                let previous = file_targets.insert(file, (target.emit_only, target.write_file));
                debug_assert!(previous.is_none(), "file is in the emit batch twice");
                files.push(file);
            }
            // Go `Program.Emit` still traces a target that emits no file.
            None => drop(trace_emit()),
        }
    }

    // PORT: the batch runs in `targets` order on each checker thread, also with
    // `--singleThreaded`. Go `emitFilesIncremental` queues the files in SyncMap
    // Range order, which is random, and its single-threaded work group runs them
    // last-queued-first. The port keeps the order of the one-file loop that the
    // batch replaces, so each checker does the same work in the same order.
    // With the pool, no trace is written (`emit_pool_enabled`), so there is
    // no trace event per target.
    let pooled = emit_files_with_pool(&files, |file| file_targets[&file].clone(), wrap);
    let mut results = match pooled {
        Some(results) => results,
        None => {
            // The closure gets only the file, so it finds the file's target here.
            let file_targets = Arc::new(file_targets);
            run_on_checker_threads_for_files(&files, move |source_file| {
                // One Go `Program.Emit` trace event per target, on the emit thread.
                let _trace = trace_emit();
                let (emit_only, write_file) = &file_targets[&source_file];
                wrap(&|| emit_source_file(source_file, *emit_only, write_file.clone()))
            })
        }
    }
    .into_iter();

    // `combine_emit_results` of one result is that result.
    has_file
        .into_iter()
        .map(|has_file| {
            if has_file {
                results.next().expect("one emit result per batch file")
            } else {
                combine_emit_results(Vec::new())
            }
        })
        .collect()
}

/// Go `tr.Push(tracing.PhaseEmit, "emit", nil, true)` at the start of
/// `Program.Emit`. The event ends when the returned value drops.
fn trace_emit() -> Option<crate::tracing::Pop> {
    crate::tracing::get().map(|tr| tr.push(crate::tracing::Phase::Emit, "emit", Vec::new(), true))
}

/// Runs `job(file)` for each file on the file's checker thread and returns
/// the results in file order. Each checker thread runs its jobs in the
/// order they are sent (FIFO).
fn run_emit_jobs(
    files: Vec<Node>,
    job: impl Fn(Node) -> EmitResult + Send + Sync + 'static,
) -> Vec<EmitResult> {
    // Go `core.singleThreadedWorkGroup` runs the queued emits
    // last-queued-first (core/workgroup.go:67). With one checker thread the
    // jobs run in the order they are sent, so send them reversed.
    let last_queued_first = single_threaded();
    let mut queued = files;
    if last_queued_first {
        queued.reverse();
    }
    let mut results = run_on_checker_threads_for_files(&queued, job);
    if last_queued_first {
        results.reverse();
    }
    results
}

/// The `wrap` of `emit_with` and `emit_batch_with`.
type Wrap = fn(&dyn Fn() -> EmitResult) -> EmitResult;

/// Where one file's emit runs when the emit pool is on (`file_emit`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum FileEmit {
    /// All of it on the file's checker thread, as with the pool off.
    OnChecker,
    /// The JS part on the emit pool, the d.ts part on the checker thread.
    Split,
    /// All of it on the emit pool: it has a JS part and no d.ts part.
    OnPool,
}

/// PORT: not in Go. Where the emit of `source_file` with `emit_only` runs.
/// A JS part goes to the emit pool when its transforms make no checker call
/// (`js_emit_needs_checker`). The d.ts part always needs the checker.
fn file_emit(source_file: Node, emit_only: EmitOnly) -> FileEmit {
    let options = options();
    // With `noEmit` the JS part only sets `emit_skipped`: not worth a job.
    let has_js = matches!(emit_only, EmitOnly::All | EmitOnly::Js)
        && !options.emit_declaration_only.is_true()
        && !options.no_emit.is_true();
    if !has_js || js_emit_needs_checker(source_file) {
        return FileEmit::OnChecker;
    }
    // `get_output_paths_for_file` gives a d.ts path only with declarations
    // on, and never to a JSON file.
    let has_dts = emit_only == EmitOnly::All
        && options.get_emit_declarations()
        && !is_json_source_file(source_file);
    if has_dts {
        FileEmit::Split
    } else {
        FileEmit::OnPool
    }
}

/// The part of one file's emit that runs on its checker thread when the
/// emit pool is on (`emit_files_with_pool`).
struct CheckerPart {
    emit_only: EmitOnly,
    write_file: Option<WriteFile>,
    /// The JS part on the emit pool when the file's emit is split; this is
    /// then the d.ts part.
    js_part: Option<EmitPoolJob<EmitResult>>,
}

/// PORT: not in Go. `emit_with` and `emit_batch_with` of `files` (each
/// with its `target`: `emit_only` and `write_file`) with the emit pool, one
/// result per file in file order. None, before any work, when the pool is
/// off (`emit_pool_enabled`) or would get no file: the caller then runs
/// every file on its checker thread as before.
///
/// First the JS part of each file that `file_emit` moves goes to the emit
/// pool, in file order. Then the rest goes to the checker threads exactly
/// as with the pool off: each checker thread gets its files in file order,
/// with the whole emit or the d.ts part, so each checker gets the same
/// checker calls in the same order. The JS part makes no checker call.
/// A d.ts part waits for its JS part before it writes (`Emitter::js_part`),
/// so the outputs of a file are written in Go's order.
fn emit_files_with_pool(
    files: &[Node],
    target: impl Fn(Node) -> (EmitOnly, Option<WriteFile>),
    wrap: Wrap,
) -> Option<Vec<EmitResult>> {
    if files.is_empty() || !emit_pool_enabled() {
        return None;
    }
    // The rule reads the binder data. Sending a job binds too, but the rule
    // runs first.
    bind_all();
    let ways: Vec<FileEmit> = files
        .iter()
        .map(|&file| file_emit(file, target(file).0))
        .collect();
    if ways.iter().all(|&way| way == FileEmit::OnChecker) {
        return None;
    }

    let pool_jobs: Vec<_> = files
        .iter()
        .zip(&ways)
        .filter(|&(_, &way)| way != FileEmit::OnChecker)
        .map(|(&file, &way)| {
            let (emit_only, write_file) = target(file);
            let emit_only = if way == FileEmit::Split {
                EmitOnly::Js
            } else {
                emit_only
            };
            move || wrap(&|| emit_source_file_on_pool(file, emit_only, write_file.clone()))
        })
        .collect();
    let mut pool_jobs = send_emit_pool_jobs(pool_jobs).into_iter();

    let mut checker_files = Vec::new();
    let mut checker_parts = FxHashMap::default();
    let mut on_pool = Vec::new();
    for (index, (&file, &way)) in files.iter().zip(&ways).enumerate() {
        if way == FileEmit::OnPool {
            on_pool.push((index, pool_jobs.next().expect("a pool job per pool file")));
            continue;
        }
        let (emit_only, write_file) = target(file);
        let js_part =
            (way == FileEmit::Split).then(|| pool_jobs.next().expect("a pool job per split file"));
        checker_files.push(file);
        checker_parts.insert(
            file,
            CheckerPart {
                emit_only,
                write_file,
                js_part,
            },
        );
    }

    // The closure gets only the file, so it takes the file's part here.
    let checker_parts = Mutex::new(checker_parts);
    let checker_results = catch_unwind(AssertUnwindSafe(|| {
        run_on_checker_threads_for_files(&checker_files, move |source_file| {
            let part = checker_parts
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .remove(&source_file)
                .expect("one checker part per file");
            match part.js_part {
                Some(js_part) => emit_declaration_part(source_file, part.write_file, js_part, wrap),
                None => {
                    wrap(&|| emit_source_file(source_file, part.emit_only, part.write_file.clone()))
                }
            }
        })
    }));
    // Every pool job ends before a panic goes on.
    let on_pool: Vec<(usize, std::thread::Result<EmitResult>)> = on_pool
        .into_iter()
        .map(|(index, job)| (index, job.join()))
        .collect();
    let mut checker_results = checker_results
        .unwrap_or_else(|payload| resume_unwind(payload))
        .into_iter();
    let mut on_pool = on_pool.into_iter().peekable();
    let results = (0..files.len())
        .map(
            |index| match on_pool.next_if(|(pool_index, _)| *pool_index == index) {
                Some((_, result)) => result.unwrap_or_else(|payload| resume_unwind(payload)),
                None => checker_results.next().expect("one result per checker file"),
            },
        )
        .collect();
    Some(results)
}

/// The JS part of a file's emit when the d.ts part runs on the checker
/// thread (`Emitter::js_part`).
pub struct PoolJsPart {
    job: Option<EmitPoolJob<EmitResult>>,
    result: Option<std::thread::Result<EmitResult>>,
}

impl PoolJsPart {
    /// Waits for the JS part to end. Only the first call waits.
    pub fn wait(&mut self) {
        if let Some(job) = self.job.take() {
            self.result = Some(job.join());
        }
    }

    /// The diagnostics of the JS part, after `wait`. None when it panicked.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        match &self.result {
            Some(Ok(result)) => &result.diagnostics,
            _ => &[],
        }
    }

    /// Waits, then takes the result, or the payload of the JS part's panic.
    fn take_result(&mut self) -> std::thread::Result<EmitResult> {
        self.wait();
        self.result.take().expect("the JS part is taken once")
    }
}

/// The d.ts part of a split file's emit, on its checker thread, merged with
/// the JS part `js_part` from the emit pool. `wrap` is around the d.ts part
/// only (the pool job wraps the JS part). Both parts end before a panic of
/// either goes on.
fn emit_declaration_part(
    source_file: Node,
    write_file: Option<WriteFile>,
    js_part: EmitPoolJob<EmitResult>,
    wrap: Wrap,
) -> EmitResult {
    let js_part = Rc::new(RefCell::new(PoolJsPart {
        job: Some(js_part),
        result: None,
    }));
    let dts = catch_unwind(AssertUnwindSafe(|| {
        wrap(&|| {
            emit_source_file_with(
                new_emit_host(source_file),
                source_file,
                EmitOnly::Dts,
                write_file.clone(),
                Some(js_part.clone()),
            )
        })
    }));
    let js = js_part.borrow_mut().take_result();
    let dts = dts.unwrap_or_else(|payload| resume_unwind(payload));
    let js = js.unwrap_or_else(|payload| resume_unwind(payload));
    merge_emit_parts(js, dts)
}

/// Go `emitter.emit` of one file from its two parts, JS first, as Go runs
/// them. Go keeps the diagnostics of both parts in one collection; each
/// part's are sorted (`get_diagnostics`), and the merge sorts them together.
fn merge_emit_parts(js: EmitResult, dts: EmitResult) -> EmitResult {
    let mut diagnostics = DiagnosticsCollection::default();
    for diagnostic in js.diagnostics.into_iter().chain(dts.diagnostics) {
        diagnostics.add(diagnostic);
    }
    let mut emitted_files = js.emitted_files;
    emitted_files.extend(dts.emitted_files);
    let mut source_maps = js.source_maps;
    source_maps.extend(dts.source_maps);
    EmitResult {
        emit_skipped: js.emit_skipped || dts.emit_skipped,
        diagnostics: diagnostics.get_diagnostics(),
        emitted_files,
        source_maps,
    }
}

/// The JS part of a file's emit on the emit pool (`emit_only` is `Js`), or
/// its whole emit when it has no d.ts part: `emit_source_file` with a host
/// that has no checker.
fn emit_source_file_on_pool(
    source_file: Node,
    emit_only: EmitOnly,
    write_file: Option<WriteFile>,
) -> EmitResult {
    emit_source_file_with(
        new_emit_host_without_checker(),
        source_file,
        emit_only,
        write_file,
        None,
    )
}

/// The body of the Go `wg.Queue` closure in `Program.Emit`.
fn emit_source_file(
    source_file: Node,
    emit_only: EmitOnly,
    write_file: Option<WriteFile>,
) -> EmitResult {
    emit_source_file_with(
        new_emit_host(source_file),
        source_file,
        emit_only,
        write_file,
        None,
    )
}

/// `emit_source_file` with the emit host, and for a d.ts part (`emit_only`
/// is `Dts`) the JS part on the emit pool.
fn emit_source_file_with(
    host: Rc<crate::program::EmitHost>,
    source_file: Node,
    emit_only: EmitOnly,
    write_file: Option<WriteFile>,
    js_part: Option<Rc<RefCell<PoolJsPart>>>,
) -> EmitResult {
    let new_line = options().new_line.get_new_line_character();
    let writer: Rc<RefCell<dyn EmitTextWriter>> =
        Rc::new(RefCell::new(new_text_writer(new_line, 0)));
    writer.borrow_mut().clear();
    let paths = get_output_paths_for_source_file(
        source_file,
        host.as_ref(),
        emit_only == EmitOnly::ForcedDts,
    );
    let mut emitter = Emitter {
        host,
        emit_only,
        emitter_diagnostics: DiagnosticsCollection::default(),
        writer: Some(writer),
        paths,
        source_file,
        emit_result: EmitResult::default(),
        write_file,
        js_part,
    };
    emitter.emit();
    emitter.writer = None;
    emitter.emit_result
}

// Go: compiler/program.go:1690 CombineEmitResults
pub fn combine_emit_results(results: Vec<EmitResult>) -> EmitResult {
    let mut result = EmitResult::default();
    for emit_result in results {
        if emit_result.emit_skipped {
            result.emit_skipped = true;
        }
        result.diagnostics.extend(emit_result.diagnostics);
        result.emitted_files.extend(emit_result.emitted_files);
        result.source_maps.extend(emit_result.source_maps);
    }
    result
}

// Go: compiler/program.go:1728 HandleNoEmitOnError
pub fn handle_no_emit_on_error(file: Node) -> Option<EmitResult> {
    if !options().no_emit_on_error.is_true() {
        return None; // No emit on error is not set, so we can proceed with emitting
    }

    let diagnostics = get_diagnostics_of_any_program(
        file,
        true,
        &mut get_bind_diagnostics,
        &mut get_semantic_diagnostics,
        &mut get_global_diagnostics,
        &mut get_declaration_diagnostics,
    );
    if diagnostics.is_empty() {
        return None; // No diagnostics, so we can proceed with emitting
    }
    Some(EmitResult {
        diagnostics,
        emit_skipped: true,
        ..EmitResult::default()
    })
}
