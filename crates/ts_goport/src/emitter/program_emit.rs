//! Port of the emit parts of Go `compiler/program.go` (`Emit`,
//! `CombineEmitResults`, `HandleNoEmitOnError`, the emit option and result
//! types). The emit host (`program::EmitHost`) and the output paths
//! (`program::get_output_paths_for_source_file`) are in `program.rs`, where
//! the declaration diagnostics use them too.

use crate::prelude::*;

use std::sync::Arc;

use super::emitter::{EmitOnly, Emitter};
use crate::sourcemap::generator::RawSourceMap;

// Go: compiler/program.go:1600 WriteFileData
// PORT: Go `BuildInfo any` is left out: `.tsbuildinfo` is not emitted.
#[derive(Clone, Debug, Default)]
pub struct WriteFileData {
    pub source_map_url_pos: i32,
    pub diagnostics: Vec<Diagnostic>,
    pub skipped_dts_write: bool,
}

// Go: compiler/program.go:1607 WriteFile
// PORT: Go `error` is `Result<(), String>`. Emit runs on the checker
// threads, so the callback is shared and thread safe. The callback may set
// `skipped_dts_write`.
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
// order. Each emit makes its own text writer.
pub fn emit(options: EmitOptions) -> EmitResult {
    emit_with(options, |emit_file| emit_file())
}

/// `emit` with `wrap` around each file's emit, on the file's checker
/// thread. `goport` uses it to guard each file on its own.
pub fn emit_with(
    options: EmitOptions,
    wrap: fn(&dyn Fn() -> EmitResult) -> EmitResult,
) -> EmitResult {
    let _trace = crate::tracing::get()
        .map(|tr| tr.push(crate::tracing::Phase::Emit, "emit", Vec::new(), true));
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
    let results = run_on_checker_threads_for_files(&source_files, move |source_file| {
        wrap(&|| emit_source_file(source_file, emit_only, write_file.clone()))
    });

    // collect results from emit, preserving input order
    combine_emit_results(results)
}

/// The body of the Go `wg.Queue` closure in `Program.Emit`.
fn emit_source_file(
    source_file: Node,
    emit_only: EmitOnly,
    write_file: Option<WriteFile>,
) -> EmitResult {
    let host = new_emit_host(source_file);
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
