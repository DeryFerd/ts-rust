//! Port of execute/incremental/emitfileshandler.go.
//!
//! PORT: Go emits the affected files on a work group; here
//! `emit_files_incremental` sends them as one `emit_batch`, in the order Go
//! queues them. Each emit runs on the file's checker thread, and each
//! checker thread runs its files in that order. The `WriteFile` callback
//! runs on the checker threads, so what it reads from the snapshot is
//! copied into it, and what it records (Go `signatures`, `emitSignatures`,
//! `latestChangedDtsFiles` SyncMaps) goes to `EmitFilesShared` behind a
//! mutex. Go `ctx` is dropped. `start_emit_files` and `finish_emit_files`
//! split the emit of all affected files at the wait for the emit jobs, so
//! `Program::start_check_and_emit` can send them behind the check.

use super::affected_files::collect_all_affected_files;
use super::hash::FileInfo;
use super::hash::*;
use super::program::{Program, SignatureUpdateKind};
use super::snapshot::*;
use crate::emitter::emitter::EmitOnly;
use crate::emitter::program_emit::{
    EmitOptions, EmitResult, PendingEmitBatch, WriteFile, WriteFileData, combine_emit_results,
    emit, start_emit_batch,
};
use crate::frontend::prelude::*;
use crate::program::source_file_may_be_emitted;
use std::sync::{Arc, Mutex};

// Go: incremental/emitfileshandler.go:14 emitUpdate
#[derive(Clone, Debug, Default)]
pub struct EmitUpdate {
    pub pending_kind: FileEmitKind,
    pub result: Option<EmitResult>,
    pub dts_errors_from_cache: bool,
}

/// The Go `emitFilesHandler` SyncMaps that the `WriteFile` callback writes.
#[derive(Debug, Default)]
pub struct EmitFilesShared {
    pub signatures: IndexMap<Path, String>,
    pub emit_signatures: IndexMap<Path, EmitSignature>,
    pub latest_changed_dts_files: IndexMap<Path, String>,
}

/// One file that `emit_files_incremental` emits: its path, its pending
/// emit kind, the kind it emits now, and the file.
type QueuedEmit = (Path, FileEmitKind, FileEmitKind, Node);

// Go: incremental/emitfileshandler.go:20 emitFilesHandler
pub struct EmitFilesHandler<'a> {
    program: &'a Program,
    is_for_dts_errors: bool,
    shared: Arc<Mutex<EmitFilesShared>>,
    deleted_pending_kinds: IndexSet<Path>,
    emit_updates: IndexMap<Path, EmitUpdate>,
    has_emit_diagnostics: bool,
}

/// Go `file.Path()` as a `tspath.Path`.
fn path_of(file: Node) -> Path {
    Path(source_file_info(file).path.clone())
}

/// Go `err.Error()` of a file system error.
// PORT: Go prints the `*os.PathError` as "op path: err".
pub(crate) fn fs_error_text(err: &FsError) -> String {
    match err {
        FsError::Path { op, path, err } => format!("{op} {path}: {err}"),
        FsError::Other(message) => message.clone(),
        other => format!("{other:?}"),
    }
}

impl<'a> EmitFilesHandler<'a> {
    #[must_use]
    pub fn new(program: &'a Program, is_for_dts_errors: bool) -> Self {
        EmitFilesHandler {
            program,
            is_for_dts_errors,
            shared: Arc::new(Mutex::new(EmitFilesShared::default())),
            deleted_pending_kinds: IndexSet::default(),
            emit_updates: IndexMap::default(),
            has_emit_diagnostics: false,
        }
    }

    // Go: incremental/emitfileshandler.go:33 getPendingEmitKindForEmitOptions
    // Determining what all is pending to be emitted based on previous options or previous file emit flags
    fn get_pending_emit_kind_for_emit_options(
        &self,
        emit_kind: FileEmitKind,
        options: &EmitOptions,
    ) -> FileEmitKind {
        let mut pending_kind = get_pending_emit_kind(emit_kind, FileEmitKind::NONE);
        if options.emit_only == EmitOnly::Dts {
            pending_kind &= FileEmitKind::ALL_DTS;
        }
        if self.is_for_dts_errors {
            pending_kind &= FileEmitKind::DTS_ERRORS;
        }
        pending_kind
    }

    // Go: incremental/emitfileshandler.go:47 emitAllAffectedFiles
    // Emits the next affected file's emit result (EmitResult and sourceFiles emitted) or returns undefined if iteration is complete
    // The first of writeFile if provided, writeFile of BuilderProgramHost if provided, writeFile of compiler host
    // in that order would be used to write the files
    fn emit_all_affected_files(&mut self, options: EmitOptions) -> EmitResult {
        // Emit all affected files
        if self.program.snapshot.borrow().can_use_incremental_state() {
            let results = self.emit_files_incremental(&options);
            if self.is_for_dts_errors {
                if options.target_source_file.is_some() {
                    // Result from cache
                    let diagnostics = self
                        .program
                        .snapshot
                        .borrow_mut()
                        .emit_diagnostics_per_file
                        .get_mut(&path_of(options.target_source_file))
                        .expect("emit diagnostics of the target file")
                        .get_diagnostics(options.target_source_file);
                    let result = EmitResult {
                        emit_skipped: true,
                        diagnostics,
                        ..EmitResult::default()
                    };
                    self.update_has_emit_diagnostics(Some(&result));
                    return result;
                }
                for result in &results {
                    self.update_has_emit_diagnostics(Some(result));
                }
                combine_emit_results(results)
            } else {
                self.combine_results_and_emit_build_info(results, &options)
            }
        } else if !self.is_for_dts_errors {
            let emit_options = self.get_emit_options(options.clone());
            let mut result = emit(emit_options);
            self.update_has_emit_diagnostics(Some(&result));
            self.update_snapshot();
            self.emit_build_info(&options, &mut result);
            result
        } else {
            let result = EmitResult {
                emit_skipped: true,
                diagnostics: get_declaration_diagnostics(options.target_source_file),
                ..EmitResult::default()
            };
            if !result.diagnostics.is_empty() {
                self.update_has_emit_diagnostics(Some(&result));
                self.program.snapshot.borrow_mut().has_emit_diagnostics = true;
            }
            result
        }
    }

    /// The end of `emitAllAffectedFiles` with the incremental state, not
    /// for d.ts errors.
    fn combine_results_and_emit_build_info(
        &mut self,
        results: Vec<EmitResult>,
        options: &EmitOptions,
    ) -> EmitResult {
        // Combine results and update buildInfo
        let mut result = combine_emit_results(results);
        self.update_has_emit_diagnostics(Some(&result));
        self.emit_build_info(options, &mut result);
        result
    }

    // Go: incremental/emitfileshandler.go:91 updateHasEmitDiagnostics
    fn update_has_emit_diagnostics(&mut self, result: Option<&EmitResult>) {
        if result.is_some_and(|result| !result.diagnostics.is_empty()) {
            self.has_emit_diagnostics = true;
        }
    }

    // Go: incremental/emitfileshandler.go:97 emitBuildInfo
    fn emit_build_info(&self, options: &EmitOptions, result: &mut EmitResult) {
        if let Some(build_info_result) = self.program.emit_build_info(options) {
            result.diagnostics.extend(build_info_result.diagnostics);
            result.emitted_files.extend(build_info_result.emitted_files);
        }
    }

    // Go: incremental/emitfileshandler.go:105 emitFilesIncremental
    // PORT: perf. Go queues one job per file on a WorkGroup. Pass 1 is the
    // loop body before `wg.Queue`, in the order Go queues
    // (`queue_affected_files`). Pass 2 runs all jobs at once (`emit_batch`,
    // or one declaration diagnostics job per file); each checker thread runs
    // its files in pass 1 order, as the old one-file-at-a-time loop did.
    // Pass 3 is the job tail, in the same order
    // (`finish_emit_files_incremental`). `start_emit_files` runs pass 1 and
    // sends pass 2 early; `finish_emit_files` does the rest.
    fn emit_files_incremental(&mut self, options: &EmitOptions) -> Vec<EmitResult> {
        let queued = self.queue_affected_files(options);
        let results: Vec<EmitResult> = if !self.is_for_dts_errors {
            self.send_emit_batch(&queued, options).wait()
        } else {
            // Go `GetDeclarationDiagnostics(ctx, affectedFile)`. Send every
            // job first, then wait for each in order.
            let jobs: Vec<_> = queued
                .iter()
                .map(|&(.., affected_file)| send_declaration_diagnostics_job(affected_file))
                .collect();
            jobs.into_iter()
                .map(|job| EmitResult {
                    emit_skipped: true,
                    diagnostics: sort_and_deduplicate_diagnostics(job.wait()),
                    ..EmitResult::default()
                })
                .collect()
        };
        self.finish_emit_files_incremental(queued, results)
    }

    /// Pass 1 of `emit_files_incremental`: handles the affected files and
    /// returns the files to emit, in the order Go queues them.
    fn queue_affected_files(&mut self, options: &EmitOptions) -> Vec<QueuedEmit> {
        // Get all affected files
        collect_all_affected_files(self.program);

        let pending: Vec<(Path, FileEmitKind)> = self
            .program
            .snapshot
            .borrow()
            .affected_files_pending_emit
            .iter()
            .map(|(path, kind)| (path.clone(), *kind))
            .collect();

        let mut queued: Vec<QueuedEmit> = Vec::new();
        for (path, emit_kind) in pending {
            let affected_file = get_source_file_by_path(&path);
            if affected_file.is_nil() || !source_file_may_be_emitted(affected_file, false) {
                self.deleted_pending_kinds.insert(path);
                continue;
            }
            let pending_kind = self.get_pending_emit_kind_for_emit_options(emit_kind, options);
            if !pending_kind.is_empty() {
                queued.push((path, emit_kind, pending_kind, affected_file));
            }
        }
        queued
    }

    /// Pass 2 of `emit_files_incremental` (not for d.ts errors) without the
    /// wait: sends the emit of the `queued` files.
    fn send_emit_batch(&self, queued: &[QueuedEmit], options: &EmitOptions) -> PendingEmitBatch {
        let targets = queued
            .iter()
            .map(|&(_, _, pending_kind, affected_file)| {
                // Determine if we can do partial emit
                let mut emit_only = EmitOnly::All;
                if pending_kind.intersects(FileEmitKind::ALL_JS) {
                    emit_only = EmitOnly::Js;
                }
                if pending_kind.intersects(FileEmitKind::ALL_DTS) {
                    if emit_only == EmitOnly::Js {
                        emit_only = EmitOnly::All;
                    } else {
                        emit_only = EmitOnly::Dts;
                    }
                }
                self.get_emit_options(EmitOptions {
                    target_source_file: affected_file,
                    emit_only,
                    write_file: options.write_file.clone(),
                })
            })
            .collect();
        start_emit_batch(targets)
    }

    /// Pass 3 of `emit_files_incremental` with the pass 2 `results` of the
    /// `queued` files, then the rest of Go `emitFilesIncremental`.
    fn finish_emit_files_incremental(
        &mut self,
        queued: Vec<QueuedEmit>,
        results: Vec<EmitResult>,
    ) -> Vec<EmitResult> {
        debug_assert_eq!(results.len(), queued.len(), "one result per queued file");
        for ((path, emit_kind, pending_kind, _), result) in queued.into_iter().zip(results) {
            self.update_has_emit_diagnostics(Some(&result));

            // Update the pendingEmit for the file
            self.emit_updates.insert(
                path,
                EmitUpdate {
                    pending_kind: get_pending_emit_kind(emit_kind, pending_kind),
                    result: Some(result),
                    dts_errors_from_cache: false,
                },
            );
        }

        // Get updated errors that were not included in affected files emit
        let emit_diagnostic_paths: Vec<Path> = self
            .program
            .snapshot
            .borrow()
            .emit_diagnostics_per_file
            .keys()
            .cloned()
            .collect();
        for path in emit_diagnostic_paths {
            if !self.emit_updates.contains_key(&path) {
                let affected_file = get_source_file_by_path(&path);
                if affected_file.is_nil() || !source_file_may_be_emitted(affected_file, false) {
                    self.deleted_pending_kinds.insert(path);
                    continue;
                }
                let mut snapshot = self.program.snapshot.borrow_mut();
                let pending_kind = snapshot
                    .affected_files_pending_emit
                    .get(&path)
                    .copied()
                    .unwrap_or_default();
                let diagnostics = snapshot
                    .emit_diagnostics_per_file
                    .get_mut(&path)
                    .expect("emit diagnostics entry")
                    .get_diagnostics(affected_file);
                drop(snapshot);
                self.emit_updates.insert(
                    path,
                    EmitUpdate {
                        pending_kind,
                        result: Some(EmitResult {
                            emit_skipped: true,
                            diagnostics,
                            ..EmitResult::default()
                        }),
                        dts_errors_from_cache: true,
                    },
                );
            }
        }

        self.update_snapshot()
    }

    // Go: incremental/emitfileshandler.go:176 getEmitOptions
    // PORT: the callback runs on the checker thread of the target file. It
    // gets copies of the target's file info and old emit signature (Go reads
    // them from the snapshot, which does not change during emit). Go
    // `h.program.host.GetMTime`/`SetMTime` go through the compiler host file
    // system; the incremental `Host` is not thread-safe, so the callback
    // uses this thread's OS file system (`osvfs_fs`), which is what the
    // compiler host wraps. Without `options.WriteFile`, Go writes with the
    // compiler host file system; the port follows `program::EmitHost`,
    // whose write fails without a callback.
    fn get_emit_options(&self, options: EmitOptions) -> EmitOptions {
        let snapshot = self.program.snapshot.borrow();
        if !snapshot.options.get_emit_declarations() {
            return options;
        }
        let can_use_incremental_state = snapshot.can_use_incremental_state();
        let target_source_file = options.target_source_file;
        let target_path = if target_source_file.is_some() {
            path_of(target_source_file)
        } else {
            Path::default()
        };
        let context = DtsWriteContext {
            composite: snapshot.options.composite.is_true(),
            build: snapshot.options.build.is_true(),
            hash_with_text: snapshot.hash_with_text,
            old_emit_signature: snapshot.emit_signatures.get(&target_path).cloned(),
            file_info: snapshot.file_infos.get(&target_path).cloned(),
            path: target_path,
            shared: Arc::clone(&self.shared),
        };
        drop(snapshot);
        let user_write_file = options.write_file.clone();
        let write_file: WriteFile = Arc::new(
            move |file_name: &str, text: &str, data: &mut WriteFileData| {
                let mut differs_only_in_map = false;
                if is_declaration_file_name(file_name) && can_use_incremental_state {
                    let mut emit_signature = String::new();
                    let info = context
                        .file_info
                        .as_ref()
                        .expect("file info of the emitted file");
                    if info.signature == info.version {
                        let signature = compute_signature_with_diagnostics(
                            target_source_file,
                            text,
                            data,
                            context.hash_with_text,
                        );
                        // With d.ts diagnostics they are also part of the signature so emitSignature will be different from it since its just hash of d.ts
                        if data.diagnostics.is_empty() {
                            emit_signature = signature.clone();
                        }
                        if signature != info.version {
                            // Update it
                            context
                                .shared
                                .lock()
                                .expect("emit files lock")
                                .signatures
                                .insert(context.path.clone(), signature);
                        }
                    }

                    // Store d.ts emit hash so later can be compared to check if d.ts has changed.
                    // Currently we do this only for composite projects since these are the only projects that can be referenced by other projects
                    // and would need their d.ts change time in --build mode
                    if skip_dts_output_of_composite(
                        &context,
                        file_name,
                        text,
                        data,
                        emit_signature,
                        &mut differs_only_in_map,
                    ) {
                        return Ok(());
                    }
                }

                let mut a_time = None;
                if differs_only_in_map {
                    a_time = osvfs_fs().stat(file_name).and_then(|info| info.mod_time());
                }
                let mut err = match &user_write_file {
                    Some(write_file) => write_file(file_name, text, data),
                    None => Err(format!("no WriteFile callback for {file_name}")),
                };
                if err.is_ok() && differs_only_in_map {
                    // Revert the time to original one
                    err = osvfs_fs()
                        .chtimes(file_name, None, a_time)
                        .map_err(|err| fs_error_text(&err));
                }
                err
            },
        );
        EmitOptions {
            target_source_file,
            emit_only: options.emit_only,
            write_file: Some(write_file),
        }
    }

    // Go: incremental/emitfileshandler.go:274 updateSnapshot
    fn update_snapshot(&mut self) -> Vec<EmitResult> {
        let mut snapshot = self.program.snapshot.borrow_mut();
        if snapshot.can_use_incremental_state() {
            let shared = std::mem::take(&mut *self.shared.lock().expect("emit files lock"));
            for (file, signature) in shared.signatures {
                let info = snapshot
                    .file_infos
                    .get_mut(&file)
                    .expect("updateSnapshot: file info");
                info.signature = signature;
                if let Some(testing_data) = &self.program.testing_data {
                    testing_data
                        .borrow_mut()
                        .updated_signature_kinds
                        .insert(file.clone(), SignatureUpdateKind::StoredAtEmit);
                }
                snapshot.build_info_emit_pending = true;
            }
            for (file, signature) in shared.emit_signatures {
                snapshot.emit_signatures.insert(file, signature);
                snapshot.build_info_emit_pending = true;
            }
            for file in &self.deleted_pending_kinds {
                snapshot.affected_files_pending_emit.shift_remove(file);
                snapshot.build_info_emit_pending = true;
            }
            // Always use correct order when to collect the result
            let mut results = Vec::new();
            for file in source_files() {
                let path = path_of(file);
                if let Some(latest_changed_dts_file) = shared.latest_changed_dts_files.get(&path) {
                    snapshot.latest_changed_dts_file = latest_changed_dts_file.clone();
                    snapshot.build_info_emit_pending = true;
                    snapshot.has_changed_dts_file = true;
                }
                if let Some(update) = self.emit_updates.get(&path) {
                    if !update.dts_errors_from_cache {
                        if update.pending_kind.is_empty() {
                            snapshot.affected_files_pending_emit.shift_remove(&path);
                        } else {
                            snapshot
                                .affected_files_pending_emit
                                .insert(path.clone(), update.pending_kind);
                        }
                        snapshot.build_info_emit_pending = true;
                    }
                    if let Some(result) = &update.result {
                        results.push(result.clone());
                        if !result.diagnostics.is_empty() {
                            snapshot.emit_diagnostics_per_file.insert(
                                path.clone(),
                                DiagnosticsOrBuildInfoDiagnosticsWithFileName {
                                    diagnostics: Some(result.diagnostics.clone()),
                                    ..Default::default()
                                },
                            );
                        }
                    }
                }
            }
            return results;
        } else if self.has_emit_diagnostics {
            snapshot.has_emit_diagnostics = true;
        }
        Vec::new()
    }
}

/// What Go `getEmitOptions`' `WriteFile` closure and
/// `skipDtsOutputOfComposite` read through `h`, copied for the target file.
struct DtsWriteContext {
    composite: bool,
    build: bool,
    hash_with_text: bool,
    old_emit_signature: Option<EmitSignature>,
    file_info: Option<FileInfo>,
    path: Path,
    shared: Arc<Mutex<EmitFilesShared>>,
}

// Go: incremental/emitfileshandler.go:236 skipDtsOutputOfComposite
// Compare to existing computed signature and store it or handle the changes in d.ts map option from before
// returning undefined means that, we dont need to emit this d.ts file since its contents didnt change
fn skip_dts_output_of_composite(
    context: &DtsWriteContext,
    output_file_name: &str,
    text: &str,
    data: &mut WriteFileData,
    mut new_signature: String,
    differs_only_in_map: &mut bool,
) -> bool {
    if !context.composite {
        return false;
    }
    let mut old_signature = String::new();
    let old_signature_format = context.old_emit_signature.as_ref();
    if let Some(format) = old_signature_format {
        if !format.signature.is_empty() {
            old_signature = format.signature.clone();
        } else {
            old_signature = format
                .signature_with_different_options
                .as_ref()
                .expect("signatureWithDifferentOptions")[0]
                .clone();
        }
    }
    if new_signature.is_empty() {
        new_signature = compute_hash(
            get_text_handling_source_map_for_signature(text, data),
            context.hash_with_text,
        );
    }
    let mut shared = context.shared.lock().expect("emit files lock");
    // Dont write dts files if they didn't change
    if new_signature == old_signature {
        // If the signature was encoded as string the dts map options match so nothing to do
        if old_signature_format.is_some_and(|format| format.signature == old_signature) {
            data.skipped_dts_write = true;
            return true;
        } else {
            // Mark as differsOnlyInMap so that we can reverse the timestamp with --build so that
            // the downstream projects dont detect this as change in d.ts file
            *differs_only_in_map = context.build;
        }
    } else {
        shared
            .latest_changed_dts_files
            .insert(context.path.clone(), output_file_name.to_string());
    }
    shared.emit_signatures.insert(
        context.path.clone(),
        EmitSignature {
            signature: new_signature,
            signature_with_different_options: None,
        },
    );
    false
}

// Go: incremental/emitfileshandler.go:327 emitFiles
#[must_use]
pub fn emit_files(program: &Program, options: EmitOptions, is_for_dts_errors: bool) -> EmitResult {
    let mut emit_handler = EmitFilesHandler::new(program, is_for_dts_errors);

    // Single file emit - do direct from program
    if !is_for_dts_errors && options.target_source_file.is_some() {
        let emit_options = emit_handler.get_emit_options(options);
        let result = emit(emit_options);
        emit_handler.update_has_emit_diagnostics(Some(&result));
        emit_handler.update_snapshot();
        return result;
    }

    // Emit only affected files if using builder for emit
    emit_handler.emit_all_affected_files(options)
}

/// PORT: not in Go (perf). The emit that `start_emit_files` sent:
/// `emit_files` of all affected files (no target file, `EmitOnly::All`)
/// up to the wait for the emit jobs, and the handler state that the rest
/// needs.
pub(crate) struct StartedEmit {
    shared: Arc<Mutex<EmitFilesShared>>,
    deleted_pending_kinds: IndexSet<Path>,
    queued: Vec<QueuedEmit>,
    batch: PendingEmitBatch,
    /// The `WriteFile` of the start. `finish_emit_files` must get the same.
    write_file: Option<WriteFile>,
    /// `program::bind_thread_fingerprint` of this thread after the start.
    /// The emit pool starts from a copy of this thread's state, so between
    /// the start and the finish this thread must not change it, else the
    /// pool would start from other state than without the early start.
    fingerprint: (usize, (u64, u64), usize),
}

/// PORT: not in Go (perf). The first half of `emit_files(program, options,
/// false)` for `Program::start_check_and_emit`: pass 1 of
/// `emit_files_incremental`, then the emit jobs are sent without a wait.
/// Each checker thread runs them after the jobs sent to it before (the
/// check and the second global diagnostics read). The caller has the
/// incremental state (`can_use_incremental_state`), and `options` name no
/// target file and emit all.
///
/// Pass 1 reads the pending emit set, the file infos, the emit signatures
/// and the options, and `get_emit_options` copies them into the write
/// callbacks. The check commit (`Program::commit_semantic_diagnostics`)
/// changes none of them, and the affected-file walk has already run in
/// `start_check` (its second run here is a no-op), so the jobs are the
/// jobs that `emit_files` would send after the check.
pub(crate) fn start_emit_files(program: &Program, options: EmitOptions) -> StartedEmit {
    debug_assert!(
        program.snapshot.borrow().can_use_incremental_state()
            && options.target_source_file.is_nil()
            && options.emit_only == EmitOnly::All,
        "start_emit_files: only the emit of all affected files starts early"
    );
    let mut handler = EmitFilesHandler::new(program, false);
    let queued = handler.queue_affected_files(&options);
    let batch = handler.send_emit_batch(&queued, &options);
    StartedEmit {
        shared: handler.shared,
        deleted_pending_kinds: handler.deleted_pending_kinds,
        queued,
        batch,
        write_file: options.write_file,
        fingerprint: crate::program::bind_thread_fingerprint(),
    }
}

/// PORT: not in Go (perf). The second half of `emit_files(program,
/// options, false)` for the emit that `start_emit_files` sent: waits for
/// the emit jobs, then does the rest of `emit_files_incremental` and
/// `emitAllAffectedFiles` (the snapshot update and the build info).
/// `options` must be the options of the start.
pub(crate) fn finish_emit_files(
    program: &Program,
    started: StartedEmit,
    options: &EmitOptions,
) -> EmitResult {
    debug_assert!(
        options.target_source_file.is_nil()
            && options.emit_only == EmitOnly::All
            && match (&options.write_file, &started.write_file) {
                (Some(write_file), Some(started_write_file)) => {
                    Arc::ptr_eq(write_file, started_write_file)
                }
                (None, None) => true,
                _ => false,
            },
        "finish_emit_files: the emit options differ from the started ones"
    );
    debug_assert_eq!(
        crate::program::bind_thread_fingerprint(),
        started.fingerprint,
        "the loading thread changed its synthetic nodes, ids or lazy JSDoc during the early emit"
    );
    let mut handler = EmitFilesHandler {
        program,
        is_for_dts_errors: false,
        shared: started.shared,
        deleted_pending_kinds: started.deleted_pending_kinds,
        emit_updates: IndexMap::default(),
        has_emit_diagnostics: false,
    };
    let results = started.batch.wait();
    let results = handler.finish_emit_files_incremental(started.queued, results);
    handler.combine_results_and_emit_build_info(results, options)
}
