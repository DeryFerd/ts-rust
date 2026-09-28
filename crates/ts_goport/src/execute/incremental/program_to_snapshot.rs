//! Port of execute/incremental/programtosnapshot.go.
//!
//! PORT: Go `*compiler.Program` is the installed program (plan D1), read
//! through the `program.rs` free functions. Go runs the per-file work of
//! `computeProgramFileChanges` on a work group; here it runs in file order.
//! Checker calls run on the file's checker thread (`checker_access.rs`).

use super::checker_access::*;
use super::hash::FileInfo;
use super::hash::*;
use super::program::Program;
use super::snapshot::*;
use crate::frontend::prelude::*;
use std::sync::Arc;

// Go: incremental/programtosnapshot.go:16 programToSnapshot
#[must_use]
pub fn program_to_snapshot(
    old_program: Option<&Program>,
    hash_with_text: bool,
) -> Rc<RefCell<Snapshot>> {
    let program = prog();
    if let Some(old_program) = old_program {
        if old_program
            .program
            .is_some_and(|old| std::ptr::eq(old, program))
        {
            return old_program.snapshot.clone();
        }
    }
    let mut snapshot = Snapshot::new(options());
    snapshot.hash_with_text = hash_with_text;
    snapshot.check_pending = options().no_check.is_true();
    let mut to = ToProgramSnapshot {
        old_program,
        snapshot,
        global_file_removed: false,
    };

    if to.snapshot.can_use_incremental_state() {
        to.reuse_from_old_program();
        to.compute_program_file_changes();
        to.handle_file_delete();
        to.handle_pending_emit();
        to.handle_pending_check();
    }
    Rc::new(RefCell::new(to.snapshot))
}

// Go: incremental/programtosnapshot.go:40 toProgramSnapshot
// PORT: Go `program` is the installed program and is not a field.
struct ToProgramSnapshot<'a> {
    old_program: Option<&'a Program>,
    snapshot: Snapshot,
    global_file_removed: bool,
}

impl ToProgramSnapshot<'_> {
    // Go: incremental/programtosnapshot.go:47 reuseFromOldProgram
    fn reuse_from_old_program(&mut self) {
        if let Some(old_program) = self.old_program {
            let old_snapshot = old_program.snapshot.borrow();
            if self.snapshot.options.composite.is_true() {
                self.snapshot.latest_changed_dts_file =
                    old_snapshot.latest_changed_dts_file.clone();
            }
            // Copy old snapshot's changed files set
            for key in &old_snapshot.changed_files_set {
                self.snapshot.changed_files_set.insert(key.clone());
            }
            for (key, emit_kind) in &old_snapshot.affected_files_pending_emit {
                self.snapshot
                    .affected_files_pending_emit
                    .insert(key.clone(), *emit_kind);
            }
            self.snapshot.build_info_emit_pending = old_snapshot.build_info_emit_pending;
            self.snapshot.has_errors_from_old_state = old_snapshot.has_errors;
            self.snapshot.has_semantic_errors_from_old_state = old_snapshot.has_semantic_errors;
            self.snapshot.package_jsons_from_old_state =
                old_snapshot.package_jsons.clone().unwrap_or_default();
            self.snapshot.missing_package_jsons_from_old_state = old_snapshot
                .missing_package_jsons
                .clone()
                .unwrap_or_default();
        } else {
            self.snapshot.build_info_emit_pending = self.snapshot.options.is_incremental();
        }
    }

    // Go: incremental/programtosnapshot.go:67 computeProgramFileChanges
    fn compute_program_file_changes(&mut self) {
        let old_snapshot_ref = self.old_program.map(|old| old.snapshot.borrow());
        let old_snapshot = old_snapshot_ref.as_deref();
        let can_copy_semantic_diagnostics = old_snapshot.is_some_and(|old| {
            !compiler_options_affect_semantic_diagnostics(Some(old.options), Some(options()))
        });
        // We can only reuse emit signatures (i.e. .d.ts signatures) if the .d.ts file is unchanged,
        // which will eg be depedent on change in options like declarationDir and outDir options are unchanged.
        // We need to look in oldState.compilerOptions, rather than oldCompilerOptions (i.e.we need to disregard useOldState) because
        // oldCompilerOptions can be undefined if there was change in say module from None to some other option
        // which would make useOldState as false since we can now use reference maps that are needed to track what to emit, what to check etc
        // but that option change does not affect d.ts file name so emitSignatures should still be reused.
        let can_copy_emit_signatures = self.snapshot.options.composite.is_true()
            && old_snapshot.is_some_and(|old| {
                !compiler_options_affect_declaration_path(Some(old.options), Some(options()))
            });
        let copy_declaration_file_diagnostics = can_copy_semantic_diagnostics
            && old_snapshot.is_some_and(|old| {
                self.snapshot.options.skip_lib_check.is_true()
                    == old.options.skip_lib_check.is_true()
            });
        let copy_lib_file_diagnostics = copy_declaration_file_diagnostics
            && old_snapshot.is_some_and(|old| {
                self.snapshot.options.skip_default_lib_check.is_true()
                    == old.options.skip_default_lib_check.is_true()
            });

        let files = source_files();
        // PORT: perf. Go hashes each file text in the file's WorkGroup job.
        // Here another thread hashes the texts while the files bind and the
        // checkers start (`start_text_hashes`), and the loop takes each hash
        // in file order. The hash values do not depend on the thread.
        let versions = start_text_hashes(&files, self.snapshot.hash_with_text);
        // PORT: perf. Go runs this loop in a WorkGroup. `getReferencedFiles`
        // runs on the file's checker thread (`start_referenced_files_job`),
        // so the jobs of every file are sent first and run in parallel; the
        // loop takes each result in file order. Each checker still gets its files in
        // the same order. Binding comes first, as in the first iteration of
        // the loop (`file_affects_global_scope`).
        bind_all();
        let mut reference_jobs: std::collections::VecDeque<_> = files
            .iter()
            .map(|&file| start_referenced_files_job(file))
            .collect();
        for file in files {
            let file_path = Path(source_file_info(file).path.clone());
            let version = versions.recv().expect("one text hash per file");
            let implied_node_format = get_source_file_meta_data(&file_path).implied_node_format;
            let affects_global_scope = file_affects_global_scope(file);
            let mut signature = String::new();
            // PORT: Go stores the `newReferences` pointer and still reads it
            // below. `Arc` shares the set in the same way, without a copy.
            let new_references = reference_jobs
                .pop_front()
                .expect("one referenced files job per file")
                .wait()
                .map(Arc::new);
            if let Some(new_references) = &new_references {
                self.snapshot
                    .referenced_map
                    .store_references(file_path.clone(), Arc::clone(new_references));
            }
            if let Some(old_snapshot) = old_snapshot {
                if let Some(old_file_info) = old_snapshot.file_infos.get(&file_path) {
                    signature = old_file_info.signature.clone();
                    if old_file_info.version != version
                        || old_file_info.affects_global_scope != affects_global_scope
                        || old_file_info.implied_node_format != implied_node_format
                    {
                        self.snapshot.add_file_to_change_set(file_path.clone());
                    } else if new_references.as_deref()
                        != old_snapshot.referenced_map.get_references(&file_path)
                    {
                        // Referenced files changed
                        self.snapshot.add_file_to_change_set(file_path.clone());
                    } else if let Some(new_references) = &new_references {
                        for ref_path in new_references.iter() {
                            if get_source_file_by_path(ref_path).is_nil()
                                && old_snapshot.file_infos.contains_key(ref_path)
                            {
                                // Referenced file was deleted in the new program
                                self.snapshot.add_file_to_change_set(file_path.clone());
                                break;
                            }
                        }
                    }
                } else {
                    self.snapshot.add_file_to_change_set(file_path.clone());
                }
                if !self.snapshot.changed_files_set.contains(&file_path) {
                    if let Some(emit_diagnostics) =
                        old_snapshot.emit_diagnostics_per_file.get(&file_path)
                    {
                        self.snapshot.emit_diagnostics_per_file.insert(
                            file_path.clone(),
                            repopulate_diagnostics_of_file(emit_diagnostics, file),
                        );
                    }
                    if can_copy_semantic_diagnostics
                        && (!source_file_info(file).is_declaration_file
                            || copy_declaration_file_diagnostics)
                        && (!is_source_file_default_library(&file_path)
                            || copy_lib_file_diagnostics)
                    {
                        // Unchanged file copy diagnostics
                        if let Some(diagnostics) =
                            old_snapshot.semantic_diagnostics_per_file.get(&file_path)
                        {
                            self.snapshot.semantic_diagnostics_per_file.insert(
                                file_path.clone(),
                                repopulate_diagnostics_of_file(diagnostics, file),
                            );
                        }
                    }
                }
                if can_copy_emit_signatures {
                    if let Some(old_emit_signature) = old_snapshot.emit_signatures.get(&file_path) {
                        self.snapshot.emit_signatures.insert(
                            file_path.clone(),
                            old_emit_signature.get_new_emit_signature(
                                old_snapshot.options,
                                self.snapshot.options,
                            ),
                        );
                    }
                }
            } else {
                let emit_kind = get_file_emit_kind(self.snapshot.options);
                self.snapshot
                    .add_file_to_affected_files_pending_emit(file_path.clone(), emit_kind);
                signature = version.clone();
            }
            self.snapshot.file_infos.insert(
                file_path,
                FileInfo {
                    version,
                    signature,
                    affects_global_scope,
                    implied_node_format,
                },
            );
        }
    }

    // Go: incremental/programtosnapshot.go:152 handleFileDelete
    fn handle_file_delete(&mut self) {
        if let Some(old_program) = self.old_program {
            let old_snapshot = old_program.snapshot.borrow();
            // If the global file is removed, add all files as changed
            for (file_path, old_info) in &old_snapshot.file_infos {
                if !self.snapshot.file_infos.contains_key(file_path) {
                    if old_info.affects_global_scope {
                        let files = self
                            .snapshot
                            .get_all_files_excluding_default_library_file(Node::NIL)
                            .to_vec();
                        for file in files {
                            self.snapshot
                                .add_file_to_change_set(Path(source_file_info(file).path.clone()));
                        }
                        self.global_file_removed = true;
                    } else {
                        self.snapshot.build_info_emit_pending = true;
                    }
                    break;
                }
            }
        }
    }

    // Go: incremental/programtosnapshot.go:172 handlePendingEmit
    fn handle_pending_emit(&mut self) {
        if let Some(old_program) = self.old_program {
            if self.global_file_removed {
                return;
            }
            let old_options = old_program.snapshot.borrow().options;
            // If options affect emit, then we need to do complete emit per compiler options
            // otherwise only the js or dts that needs to emitted because its different from previously emitted options
            let pending_emit_kind =
                if compiler_options_affect_emit(Some(old_options), Some(self.snapshot.options)) {
                    get_file_emit_kind(self.snapshot.options)
                } else {
                    get_pending_emit_kind_with_options(self.snapshot.options, old_options)
                };
            if pending_emit_kind != FileEmitKind::NONE {
                // Add all files to affectedFilesPendingEmit since emit changed
                for file in source_files() {
                    let file_path = Path(source_file_info(file).path.clone());
                    // Add to affectedFilesPending emit only if not changed since any changed file will do full emit
                    if !self.snapshot.changed_files_set.contains(&file_path) {
                        self.snapshot
                            .add_file_to_affected_files_pending_emit(file_path, pending_emit_kind);
                    }
                }
                self.snapshot.build_info_emit_pending = true;
            }
        }
    }

    // Go: incremental/programtosnapshot.go:195 handlePendingCheck
    fn handle_pending_check(&mut self) {
        if let Some(old_program) = self.old_program {
            if self.snapshot.semantic_diagnostics_per_file.len() != source_files().len()
                && old_program.snapshot.borrow().check_pending != self.snapshot.check_pending
            {
                self.snapshot.build_info_emit_pending = true;
            }
        }
    }
}

/// Starts the Go `t.snapshot.computeHash(file.Text())` of each file in
/// `files`. The receiver gives the hashes in file order as they are ready.
// PORT: perf. The hashes run on one new thread, so that they overlap the
// bind and the checker start in `compute_program_file_changes` (the texts
// are `'static`). With `--singleThreaded` they run here, before the bind.
// One thread is enough: it reads each text once (about 16 MB for Effect),
// which takes much less time than the bind.
fn start_text_hashes(files: &[Node], hash_with_text: bool) -> std::sync::mpsc::Receiver<String> {
    let texts: Vec<&'static str> = files.iter().map(|&file| source_file_text(file)).collect();
    let (sender, receiver) = std::sync::mpsc::channel();
    let hash_texts = move || {
        for text in texts {
            // A send fails only when the loop stopped (it panicked).
            if sender.send(compute_hash(text, hash_with_text)).is_err() {
                return;
            }
        }
    };
    if single_threaded() {
        hash_texts();
    } else {
        std::thread::Builder::new()
            .name("goport-text-hash".to_string())
            .spawn(hash_texts)
            .expect("start the text hash thread");
    }
    receiver
}

// Go: incremental/programtosnapshot.go:203 fileAffectsGlobalScope
#[must_use]
pub fn file_affects_global_scope(file: Node) -> bool {
    // PORT: Go `binder.BindSourceFile(file)`. The port binds every file
    // at once; `bind_all` does nothing when they are bound.
    bind_all();
    // if file contains anything that augments to global scope we need to build them as if
    // they are global files as well as module
    if source_file_info(file)
        .module_augmentations
        .iter()
        .any(|augmentation| is_global_scope_augmentation(augmentation.parent()))
    {
        return true;
    }

    if is_external_or_common_js_module(file) || is_json_source_file(file) {
        return false;
    }

    // For script files that contains only ambient external modules, although they are not actually external module files,
    // they can only be consumed via importing elements from them. Regular script files cannot consume them. Therefore,
    // there are no point to rebuild all script files if these special files have changed. However, if any statement
    // in the file is not ambient external module, we treat it as a regular script file.
    file.statements()
        .iter()
        .any(|stmt| !is_module_with_string_literal_name(stmt))
}

// Go: incremental/programtosnapshot.go:227 addReferencedFilesFromSymbol
// PORT: the symbol belongs to the checker, so its arena is a parameter.
fn add_referenced_files_from_symbol(
    checker: &Checker,
    file: Node,
    referenced_files: &mut IndexSet<Path>,
    symbol: SymbolId,
) {
    if symbol.is_nil() {
        return;
    }
    for &declaration in checker.sym(symbol).declarations.iter() {
        let file_of_decl = get_source_file_of_node(declaration);
        if file_of_decl.is_nil() {
            continue;
        }
        if file != file_of_decl {
            referenced_files.insert(Path(source_file_info(file_of_decl).path.clone()));
        }
    }
}

// Go: incremental/programtosnapshot.go:243 addReferencedFilesFromImportLiteral
// Get the module source file and all augmenting files from the import name node from file
fn add_referenced_files_from_import_literal(
    file: Node,
    referenced_files: &mut IndexSet<Path>,
    checker: &mut Checker,
    import_name: Node,
) {
    let symbol = checker.get_symbol_at_location_exported(import_name);
    add_referenced_files_from_symbol(checker, file, referenced_files, symbol);
}

// Go: incremental/programtosnapshot.go:249 addReferencedFileFromFileName
// Gets the path to reference file from file name, it could be resolvedPath if present otherwise path
// PORT: the paths are pushed in Go order; the checker job adds them to the
// set (see `start_referenced_files_job`).
fn add_referenced_file_from_file_name(
    file_name: &str,
    referenced_files: &mut Vec<Path>,
    source_file_directory: &str,
) {
    let redirect = get_parse_file_redirect(file_name);
    if !redirect.is_empty() {
        referenced_files.push(to_path(
            &redirect,
            get_current_directory(),
            use_case_sensitive_file_names(),
        ));
    } else {
        referenced_files.push(to_path(
            file_name,
            source_file_directory,
            use_case_sensitive_file_names(),
        ));
    }
}

// Go: incremental/programtosnapshot.go:258 getReferencedFiles
// Gets the referenced files for a file from the program with values for the keys as referenced file's path to be true
#[must_use]
pub fn get_referenced_files(file: Node) -> Option<IndexSet<Path>> {
    start_referenced_files_job(file).wait()
}

/// The result of `get_referenced_files`, computed on the file's checker
/// thread.
pub type ReferencedFilesJob = CheckerJob<Option<IndexSet<Path>>>;

/// Sends `get_referenced_files` for `file` to its checker thread without
/// waiting (see `compute_program_file_changes`).
// PORT: perf. The whole set is built in the job, on the checker thread, in
// Go order, so the checkers build the sets in parallel. Only the triple
// slash and type reference paths are found here first, because they read
// the Go frontend program, which works on the loading thread only. The set
// work is large: in Hono, the ambient module part tries about 110 paths for
// each file (the `@types/node` modules).
pub fn start_referenced_files_job(file: Node) -> ReferencedFilesJob {
    // We need to use a set here since the code can contain the same import twice,
    // but that will only be one dependency.
    // To avoid invernal conversion, the key of the referencedFiles map must be of type Path
    let imports = source_file_info(file).imports.clone();
    let module_augmentations = source_file_info(file).module_augmentations.clone();
    let file_name_paths = referenced_file_name_paths(file);
    send_type_checker_job_for_file(file, move |checker| {
        let mut referenced_files: IndexSet<Path> = IndexSet::default();
        for import_name in imports {
            add_referenced_files_from_import_literal(
                file,
                &mut referenced_files,
                checker,
                import_name,
            );
        }
        referenced_files.extend(file_name_paths);
        // Add module augmentation as references
        for module_name in module_augmentations {
            if !is_string_literal(module_name) {
                continue;
            }
            add_referenced_files_from_import_literal(
                file,
                &mut referenced_files,
                checker,
                module_name,
            );
        }
        // From ambient modules
        for ambient_module in checker.get_ambient_modules() {
            add_referenced_files_from_symbol(checker, file, &mut referenced_files, ambient_module);
        }
        if referenced_files.is_empty() {
            None
        } else {
            Some(referenced_files)
        }
    })
}

/// The triple slash and type reference parts of `get_referenced_files`, in
/// Go order.
fn referenced_file_name_paths(file: Node) -> Vec<Path> {
    let mut referenced_files = Vec::new();
    let source_file_directory = get_directory_path(source_file_file_name(file));
    // Handle triple slash references
    for referenced_file in &source_file_info(file).referenced_files {
        add_referenced_file_from_file_name(
            &referenced_file.file_name,
            &mut referenced_files,
            &source_file_directory,
        );
    }

    // Handle type reference directives
    // PORT: perf. The map key is a `Path`; `Borrow<str>` looks it up without
    // a copy of the path.
    if let Some(type_refs_in_file) =
        get_resolved_type_reference_directives().get(source_file_info(file).path.as_str())
    {
        for type_ref in type_refs_in_file.values() {
            if !type_ref.resolved_file_name.is_empty() {
                add_referenced_file_from_file_name(
                    &type_ref.resolved_file_name,
                    &mut referenced_files,
                    &source_file_directory,
                );
            }
        }
    }
    referenced_files
}

// Go: incremental/programtosnapshot.go:302 repopulateDiagnosticsOfFile
// repopulateDiagnosticsOfFile repopulates diagnostic chains that depend on program state.
// When diagnostics are copied from a previous build, their message chains may reference
// stale program state (e.g., resolved module alternate results, package.json scope).
// This function recomputes those chains using the current program's state.
// PORT: testing. `diags.clone()` keeps the entry id (Go returns the same
// pointer), and the new entry gets a new id (see
// `DiagnosticsOrBuildInfoDiagnosticsWithFileName`).
#[must_use]
pub fn repopulate_diagnostics_of_file(
    diags: &DiagnosticsOrBuildInfoDiagnosticsWithFileName,
    file: Node,
) -> DiagnosticsOrBuildInfoDiagnosticsWithFileName {
    if let Some(diagnostics) = &diags.diagnostics {
        let Some(repopulated) = repopulate_diagnostics_list(diagnostics, file) else {
            return diags.clone();
        };
        return DiagnosticsOrBuildInfoDiagnosticsWithFileName {
            diagnostics: Some(repopulated),
            ..Default::default()
        };
    }
    // buildInfoDiagnostics will be repopulated via toDiagnostic's repopulateInfo handling
    diags.clone()
}

// Go: incremental/programtosnapshot.go:317 repopulateDiagnosticsList
// repopulateDiagnosticsList repopulates diagnostic chains in a list of diagnostics.
// Returns nil if no diagnostics needed repopulation (i.e., no changes were made).
#[must_use]
pub fn repopulate_diagnostics_list(diags: &[Diagnostic], file: Node) -> Option<Vec<Diagnostic>> {
    let mut changed = false;
    let mut result = Vec::with_capacity(diags.len());
    for d in diags {
        if let Some(repopulated) = repopulate_diagnostic_message_chain(d.message_chain(), file) {
            let mut clone = d.clone();
            clone.set_message_chain(repopulated);
            result.push(clone);
            changed = true;
        } else {
            result.push(d.clone());
        }
    }
    if !changed {
        return None;
    }
    Some(result)
}

// Go: incremental/programtosnapshot.go:337 repopulateDiagnosticMessageChain
// repopulateDiagnosticMessageChain repopulates chains that have repopulate info.
// Returns nil if no changes were made.
#[must_use]
pub fn repopulate_diagnostic_message_chain(
    chain: &[Diagnostic],
    file: Node,
) -> Option<Vec<Diagnostic>> {
    if chain.is_empty() {
        return None;
    }
    let mut changed = false;
    let mut result = Vec::with_capacity(chain.len());
    for c in chain {
        if let Some(repopulate_info) = c.repopulate_info() {
            // Convert to buildInfoDiagnosticWithFileName and repopulate
            // PORT: `repopulate_diagnostic_chain` reads the Go offsets in `file`.
            let (pos, end) = go_text_range(file, c.loc());
            let mut b = BuildInfoDiagnosticWithFileName {
                pos,
                end,
                code: c.code(),
                category: c.category() as i32,
                message_key: c.message_key().to_string(),
                message_args: c.message_args().to_vec(),
                repopulate_info: Some(repopulate_info),
                ..Default::default()
            };
            // Recursively handle nested chains
            for nested in c.message_chain() {
                b.message_chain.push(ast_diag_to_build_info_diag(nested));
            }
            result.push(repopulate_diagnostic_chain(&b, file));
            changed = true;
        } else {
            // Check nested chains
            if let Some(nested) = repopulate_diagnostic_message_chain(c.message_chain(), file) {
                let mut clone = c.clone();
                clone.set_message_chain(nested);
                result.push(clone);
                changed = true;
            } else {
                result.push(c.clone());
            }
        }
    }
    if !changed {
        return None;
    }
    Some(result)
}

// Go: incremental/programtosnapshot.go:382 astDiagToBuildInfoDiag
#[must_use]
pub fn ast_diag_to_build_info_diag(d: &Diagnostic) -> BuildInfoDiagnosticWithFileName {
    // PORT: Go byte offsets (see `go_text_range`).
    let (pos, end) = go_text_range(d.file(), d.loc());
    let mut b = BuildInfoDiagnosticWithFileName {
        pos,
        end,
        code: d.code(),
        category: d.category() as i32,
        message_key: d.message_key().to_string(),
        message_args: d.message_args().to_vec(),
        repopulate_info: d.repopulate_info(),
        ..Default::default()
    };
    for nested in d.message_chain() {
        b.message_chain.push(ast_diag_to_build_info_diag(nested));
    }
    b
}
