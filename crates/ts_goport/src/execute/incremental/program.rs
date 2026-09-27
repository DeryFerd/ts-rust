//! Port of execute/incremental/program.go, plus `ReadBuildInfoProgram`
//! (incremental.go:43), which builds a `Program` from a snapshot.
//!
//! PORT: Go `Program.program` is the current `&'static GoProgram`
//! (`prog()`, nil for a program read from build info), and its methods are
//! the `program.rs` free functions, which read `prog()`. A caller with
//! several programs (the build task) makes the program current while it
//! uses this one. Go passes a context; the port has none. The
//! `ProgramLike` methods take `&self`, so the snapshot is behind a
//! `RefCell`; it is an `Rc` because Go `programToSnapshot` can reuse the
//! old program's snapshot.

use super::build_info::*;
use super::build_info_to_snapshot::build_info_to_snapshot;
use super::checker_access::*;
use super::emit_files::{emit_files, fs_error_text};
use super::hash::FileInfo;
use super::incremental::{BuildInfoReader, Host, marshal_build_info};
use super::program_to_snapshot::program_to_snapshot;
use super::snapshot::*;
use super::snapshot_to_build_info::snapshot_to_build_info;
use crate::emitter::program_emit::{EmitOptions, EmitResult, WriteFileData};
use crate::execute::tsc::emit::ProgramLike;
use crate::frontend::prelude::*;
use std::sync::Arc;

// Go: incremental/program.go:20 SignatureUpdateKind
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum SignatureUpdateKind {
    #[default]
    ComputedDts = 0,
    StoredAtEmit = 1,
    UsedVersion = 2,
}

// Go: incremental/program.go:28 Program
// PORT: Go `host` is nil for a program read from build info.
pub struct Program {
    pub(crate) snapshot: Rc<RefCell<Snapshot>>,
    pub(crate) program: Option<&'static GoProgram>,
    pub(crate) host: Option<Rc<dyn Host>>,

    // Testing data
    pub(crate) testing_data: Option<RefCell<TestingData>>,

    // PORT: not in Go. What `start_check` read and started (see there).
    started: RefCell<StartedCheck>,
}

/// The work of `tsc.EmitFilesAndReportErrors` that `Program::start_check`
/// did before the caller asks for it.
#[derive(Default)]
struct StartedCheck {
    /// The first `GetGlobalDiagnostics` result. The next
    /// `get_global_diagnostics` call takes it.
    global_diagnostics: Option<Vec<Diagnostic>>,
    /// The check of the affected files. `get_semantic_diagnostics` takes it.
    check: Option<PendingSemanticDiagnostics>,
}

// Go: incremental/program.go:38 NewProgram
// PORT: Go `program` is the current program (`prog()`), so it is not a
// parameter.
#[must_use]
pub fn new_program(old_program: Option<&Program>, host: Rc<dyn Host>, testing: bool) -> Program {
    let mut incremental_program = Program {
        snapshot: program_to_snapshot(old_program, testing),
        program: Some(prog()),
        host: Some(host),
        testing_data: None,
        started: RefCell::default(),
    };

    if testing {
        // PORT: testing. Go keeps pointers to the new snapshot's and the old
        // program's `semanticDiagnosticsPerFile` (see `TestingData`).
        let old_semantic_diagnostics_ids = match old_program {
            Some(old_program) => old_program
                .snapshot
                .borrow()
                .semantic_diagnostics_per_file
                .iter()
                .map(|(path, diagnostics)| (path.clone(), diagnostics.id))
                .collect(),
            None => FxHashMap::default(),
        };
        incremental_program.testing_data = Some(RefCell::new(TestingData {
            old_semantic_diagnostics_ids,
            ..TestingData::default()
        }));
    }
    incremental_program
}

// Go: incremental/incremental.go:43 ReadBuildInfoProgram
#[must_use]
pub fn read_build_info_program(
    config: &ParsedCommandLine,
    reader: &dyn BuildInfoReader,
    host: &dyn CompilerHost,
) -> Option<Program> {
    // Read buildInfo file
    let build_info = reader.read_build_info(config)?;
    if !build_info.is_valid_version() || !build_info.is_incremental() {
        return None;
    }

    // Convert to information that can be used to create incremental program
    Some(Program {
        snapshot: Rc::new(RefCell::new(build_info_to_snapshot(
            &build_info,
            config,
            host,
        ))),
        program: None,
        host: None,
        testing_data: None,
        started: RefCell::default(),
    })
}

// Go: incremental/program.go:58 TestingData
// PORT: testing. Go keeps pointers to the new snapshot's and the old
// program's `semanticDiagnosticsPerFile`, and the Go test harness compares
// the entry pointers. The entry identity is its `id` (see
// `DiagnosticsOrBuildInfoDiagnosticsWithFileName`). Go
// `SemanticDiagnosticsPerFile` is `Program::semantic_diagnostics_id`,
// which reads the current snapshot as the Go pointer does. Go
// `OldProgramSemanticDiagnosticsPerFile` is `old_semantic_diagnostics_ids`,
// the old map's ids when `new_program` ran (empty without an old program).
// Nothing changes the old map after that, except when Go
// `programToSnapshot` reuses the old snapshot (same program). Then Go
// compares one map with itself; only watch mode (not on this branch) makes
// that case, and it must read the ids live.
#[derive(Clone, Debug, Default)]
pub struct TestingData {
    pub updated_signature_kinds: FxHashMap<Path, SignatureUpdateKind>,
    pub old_semantic_diagnostics_ids: FxHashMap<Path, u64>,
}

impl Program {
    // Go: incremental/program.go:64 GetTestingData
    #[must_use]
    pub fn get_testing_data(&self) -> Option<std::cell::Ref<'_, TestingData>> {
        self.testing_data.as_ref().map(RefCell::borrow)
    }

    // PORT: testing. Go `testingData.SemanticDiagnosticsPerFile.Load(path)`,
    // as the entry identity (see `TestingData`).
    #[must_use]
    pub fn semantic_diagnostics_id(&self, path: &Path) -> Option<u64> {
        self.snapshot
            .borrow()
            .semantic_diagnostics_per_file
            .get(path)
            .map(|diagnostics| diagnostics.id)
    }

    // Go: incremental/program.go:68 panicIfNoProgram
    fn panic_if_no_program(&self, method: &str) {
        if self.program.is_none() {
            panic!("{method}: should not be called without program");
        }
    }

    // Go: incremental/program.go:74 GetProgram
    #[must_use]
    pub fn get_program(&self) -> &'static GoProgram {
        self.panic_if_no_program("GetProgram");
        self.program.expect("program")
    }

    // Go: incremental/program.go:79 HasChangedDtsFile
    #[must_use]
    pub fn has_changed_dts_file(&self) -> bool {
        self.snapshot.borrow().has_changed_dts_file
    }

    // Go: incremental/program.go:84 Options
    // Options implements compiler.AnyProgram interface.
    #[must_use]
    pub fn options(&self) -> &'static CompilerOptions {
        self.snapshot.borrow().options
    }

    // Go: incremental/program.go:89 CommonSourceDirectory
    // CommonSourceDirectory implements compiler.AnyProgram interface.
    #[must_use]
    pub fn common_source_directory(&self) -> &'static str {
        self.panic_if_no_program("CommonSourceDirectory");
        common_source_directory()
    }

    // Go: incremental/program.go:95 Program
    // Program implements compiler.AnyProgram interface.
    #[must_use]
    pub fn program(&self) -> &'static GoProgram {
        self.panic_if_no_program("Program");
        self.program.expect("program")
    }

    // Go: incremental/program.go:101 IsSourceFileDefaultLibrary
    // IsSourceFileDefaultLibrary implements compiler.AnyProgram interface.
    #[must_use]
    pub fn is_source_file_default_library(&self, path: &Path) -> bool {
        self.panic_if_no_program("IsSourceFileDefaultLibrary");
        is_source_file_default_library(path)
    }

    // Go: incremental/program.go:107 GetSourceFiles
    // GetSourceFiles implements compiler.AnyProgram interface.
    #[must_use]
    pub fn get_source_files(&self) -> Vec<Node> {
        self.panic_if_no_program("GetSourceFiles");
        source_files()
    }

    // Go: incremental/program.go:113 GetSourceFile
    // GetSourceFile implements compiler.AnyProgram interface.
    #[must_use]
    pub fn get_source_file(&self, path: &str) -> Node {
        self.panic_if_no_program("GetSourceFile");
        get_source_file(path)
    }

    // Go: incremental/program.go:119 GetConfigFileParsingDiagnostics
    // GetConfigFileParsingDiagnostics implements compiler.AnyProgram interface.
    #[must_use]
    pub fn get_config_file_parsing_diagnostics(&self) -> Vec<Diagnostic> {
        self.panic_if_no_program("GetConfigFileParsingDiagnostics");
        get_config_file_parsing_diagnostics()
    }

    // Go: incremental/program.go:125 GetSyntacticDiagnostics
    // GetSyntacticDiagnostics implements compiler.AnyProgram interface.
    #[must_use]
    pub fn get_syntactic_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        self.panic_if_no_program("GetSyntacticDiagnostics");
        get_syntactic_diagnostics(file)
    }

    // Go: incremental/program.go:131 GetBindDiagnostics
    // GetBindDiagnostics implements compiler.AnyProgram interface.
    #[must_use]
    pub fn get_bind_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        self.panic_if_no_program("GetBindDiagnostics");
        get_bind_diagnostics(file)
    }

    // Go: incremental/program.go:136 GetProgramDiagnostics
    #[must_use]
    pub fn get_program_diagnostics(&self) -> Vec<Diagnostic> {
        self.panic_if_no_program("GetProgramDiagnostics");
        get_program_diagnostics()
    }

    // Go: incremental/program.go:141 GetGlobalDiagnostics
    // PORT: the first call returns what `start_check` read, if it ran.
    #[must_use]
    pub fn get_global_diagnostics(&self) -> Vec<Diagnostic> {
        self.panic_if_no_program("GetGlobalDiagnostics");
        if let Some(diagnostics) = self.started.borrow_mut().global_diagnostics.take() {
            return diagnostics;
        }
        get_global_diagnostics()
    }

    /// PORT: not in Go. Starts the semantic check that
    /// `tsc.EmitFilesAndReportErrors` asks for, and returns without waiting
    /// for it. `tsc -b` calls it when the program is made: Go builds up to 4
    /// projects on goroutines at the same time, and here each project's
    /// checkers check while the loading thread makes the next program or
    /// emits an earlier one.
    ///
    /// It does what `EmitFilesAndReportErrors` (through
    /// `GetDiagnosticsOfAnyProgram`) does before the check, with the same
    /// checker jobs in the same order. When the syntactic and program
    /// diagnostics are empty (and not `--listFilesOnly` or `--noCheck`), it
    /// reads the global diagnostics. When those are empty too, it handles
    /// the affected files (`collectAllAffectedFiles`) and sends the check of
    /// the files that `get_semantic_diagnostics` would check. The next
    /// `get_global_diagnostics` call returns the global diagnostics read
    /// here, and `get_semantic_diagnostics` waits for the check. The caller
    /// must use this program only through those calls, in that order, as
    /// `EmitFilesAndReportErrors` does (`start_check_used` checks it).
    pub fn start_check(&self) {
        self.panic_if_no_program("StartCheck");
        if self.snapshot.borrow().options.no_check.is_true()
            || options().list_files_only.is_true()
            || !get_syntactic_diagnostics(Node::NIL).is_empty()
            || !get_program_diagnostics().is_empty()
        {
            return;
        }
        let global_diagnostics = get_global_diagnostics();
        let has_global_diagnostics = !global_diagnostics.is_empty();
        self.started.borrow_mut().global_diagnostics = Some(global_diagnostics);
        if has_global_diagnostics {
            return;
        }
        if let Some(affected_files) = self.semantic_diagnostics_files_to_check(Node::NIL) {
            self.started.borrow_mut().check = Some(
                start_semantic_diagnostics_without_no_emit_filtering(&affected_files),
            );
        }
    }

    /// PORT: not in Go. True when the caller used everything that
    /// `start_check` read and started. `tsc -b` asserts it after the emit:
    /// a result left over means the calls did not follow
    /// `EmitFilesAndReportErrors`.
    #[must_use]
    pub fn start_check_used(&self) -> bool {
        let started = self.started.borrow();
        started.global_diagnostics.is_none() && started.check.is_none()
    }

    // Go: incremental/program.go:147 GetSemanticDiagnostics
    // GetSemanticDiagnostics implements compiler.AnyProgram interface.
    #[must_use]
    pub fn get_semantic_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        self.panic_if_no_program("GetSemanticDiagnostics");
        if self.snapshot.borrow().options.no_check.is_true() {
            return Vec::new();
        }

        // Ensure all the diagnsotics are cached
        self.collect_semantic_diagnostics_of_affected_files(file);

        // Return result from cache
        if file.is_some() {
            return self.get_semantic_diagnostics_of_file(file);
        }

        let mut diagnostics = Vec::new();
        for file in source_files() {
            diagnostics.extend(self.get_semantic_diagnostics_of_file(file));
        }
        diagnostics
    }

    // Go: incremental/program.go:171 getSemanticDiagnosticsOfFile
    fn get_semantic_diagnostics_of_file(&self, file: Node) -> Vec<Diagnostic> {
        let mut snapshot = self.snapshot.borrow_mut();
        let options = snapshot.options;
        let path = Path(source_file_info(file).path.clone());
        let Some(cached_diagnostics) = snapshot.semantic_diagnostics_per_file.get_mut(&path) else {
            panic!("After handling all the affected files, there shouldnt be more changes");
        };
        let diagnostics = cached_diagnostics.get_diagnostics(file);
        drop(snapshot);
        let mut result = filter_no_emit_semantic_diagnostics(diagnostics, options);
        result.extend(get_include_processor_diagnostics(file));
        result
    }

    // Go: incremental/program.go:183 GetDeclarationDiagnostics
    // GetDeclarationDiagnostics implements compiler.AnyProgram interface.
    #[must_use]
    pub fn get_declaration_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        self.panic_if_no_program("GetDeclarationDiagnostics");
        let result = emit_files(
            self,
            EmitOptions {
                target_source_file: file,
                ..EmitOptions::default()
            },
            true,
        );
        result.diagnostics
    }

    // Go: incremental/program.go:196 GetSuggestionDiagnostics
    // GetSuggestionDiagnostics implements compiler.AnyProgram interface.
    #[must_use]
    pub fn get_suggestion_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        self.panic_if_no_program("GetSuggestionDiagnostics");
        get_suggestion_diagnostics(file) // TODO: incremental suggestion diagnostics (only relevant in editor incremental builder?)
    }

    // Go: incremental/program.go:202 Emit
    // GetModeForUsageLocation implements compiler.AnyProgram interface.
    pub fn emit(&self, options: EmitOptions) -> EmitResult {
        self.panic_if_no_program("Emit");

        let result = if self.snapshot.borrow().options.no_emit.is_true() {
            Some(EmitResult {
                emit_skipped: true,
                ..EmitResult::default()
            })
        } else {
            handle_no_emit_on_error(self, options.target_source_file)
        };
        if let Some(mut result) = result {
            if options.target_source_file.is_some() {
                return result;
            }

            // Emit buildInfo and combine result
            if let Some(build_info_result) = self.emit_build_info(&options) {
                result.diagnostics.extend(build_info_result.diagnostics);
                result.emitted_files.extend(build_info_result.emitted_files);
            }
            return result;
        }
        emit_files(self, options, false)
    }

    // Go: incremental/program.go:229 collectSemanticDiagnosticsOfAffectedFiles
    // Handle affected files and cache the semantic diagnostics for all of them or the file asked for
    // PORT: split in two (`semantic_diagnostics_files_to_check` and
    // `commit_semantic_diagnostics`), so `start_check` can send the check
    // early. A check that `start_check` sent is committed here first.
    fn collect_semantic_diagnostics_of_affected_files(&self, file: Node) {
        let started = self.started.borrow_mut().check.take();
        if let Some(started) = started {
            let affected_files = started.files().to_vec();
            self.commit_semantic_diagnostics(&affected_files, started.wait());
            if file.is_nil() {
                return;
            }
        }
        let Some(affected_files) = self.semantic_diagnostics_files_to_check(file) else {
            return;
        };

        // Get their diagnostics and cache them
        let diagnostics_per_file =
            get_semantic_diagnostics_without_no_emit_filtering(&affected_files);
        self.commit_semantic_diagnostics(&affected_files, diagnostics_per_file);
    }

    /// The first half of `collectSemanticDiagnosticsOfAffectedFiles`: it
    /// handles the affected files and returns the files to check, or `None`
    /// where Go returns before the check.
    fn semantic_diagnostics_files_to_check(&self, file: Node) -> Option<Vec<Node>> {
        if self.snapshot.borrow().can_use_incremental_state() {
            // Get all affected files
            super::affected_files::collect_all_affected_files(self);

            if self.snapshot.borrow().semantic_diagnostics_per_file.len() == source_files().len() {
                // If we have all the files,
                return None;
            }
        }

        if file.is_some() {
            let path = Path(source_file_info(file).path.clone());
            if self
                .snapshot
                .borrow()
                .semantic_diagnostics_per_file
                .contains_key(&path)
            {
                return None;
            }
            return Some(vec![file]);
        }
        let snapshot = self.snapshot.borrow();
        Some(
            source_files()
                .into_iter()
                .filter(|&file| {
                    !snapshot
                        .semantic_diagnostics_per_file
                        .contains_key(source_file_info(file).path.as_str())
                })
                .collect(),
        )
    }

    /// The second half of `collectSemanticDiagnosticsOfAffectedFiles`: it
    /// caches the check result of `affected_files` in the snapshot.
    fn commit_semantic_diagnostics(
        &self,
        affected_files: &[Node],
        mut diagnostics_per_file: FxHashMap<Node, Vec<Diagnostic>>,
    ) {
        // Commit changes to snapshot
        let mut snapshot = self.snapshot.borrow_mut();
        for file in affected_files {
            if let Some(diagnostics) = diagnostics_per_file.remove(file) {
                snapshot.semantic_diagnostics_per_file.insert(
                    Path(source_file_info(*file).path.clone()),
                    DiagnosticsOrBuildInfoDiagnosticsWithFileName {
                        diagnostics: Some(diagnostics),
                        ..Default::default()
                    },
                );
            }
        }
        if snapshot.semantic_diagnostics_per_file.len() == source_files().len()
            && snapshot.check_pending
            && !snapshot.options.no_check.is_true()
        {
            snapshot.check_pending = false;
        }
        snapshot.build_info_emit_pending = true;
    }

    // Go: incremental/program.go:278 emitBuildInfo
    pub(crate) fn emit_build_info(&self, options: &EmitOptions) -> Option<EmitResult> {
        let _trace = crate::tracing::get().map(|tr| {
            tr.push(
                crate::tracing::Phase::Emit,
                "emitBuildInfo",
                Vec::new(),
                true,
            )
        });
        let build_info_file_name = get_build_info_file_name(
            self.snapshot.borrow().options,
            &ComparePathsOptions {
                current_directory: get_current_directory().to_string(),
                use_case_sensitive_file_names: use_case_sensitive_file_names(),
            },
        );
        if build_info_file_name.is_empty() || is_emit_blocked(&build_info_file_name) {
            return None;
        }
        if self.snapshot.borrow().has_errors == Tristate::Unknown {
            self.ensure_has_errors_for_state();
            let mut snapshot = self.snapshot.borrow_mut();
            if snapshot.has_errors != snapshot.has_errors_from_old_state
                || snapshot.has_semantic_errors != snapshot.has_semantic_errors_from_old_state
            {
                snapshot.build_info_emit_pending = true;
            }
        }
        if !self.snapshot.borrow().build_info_emit_pending {
            return None;
        }
        let build_info = snapshot_to_build_info(&self.snapshot.borrow(), &build_info_file_name);
        let text = match marshal_build_info(&build_info) {
            Ok(text) => text,
            Err(err) => panic!("Failed to marshal build info: {err}"),
        };
        let err = if let Some(write_file) = &options.write_file {
            write_file(
                &build_info_file_name,
                &text,
                &mut WriteFileData {
                    build_info: Some(Arc::new(build_info)),
                    ..WriteFileData::default()
                },
            )
        } else {
            host()
                .fs()
                .write_file(&build_info_file_name, &text)
                .map_err(|err| fs_error_text(&err))
        };
        if let Err(err) = err {
            return Some(EmitResult {
                emit_skipped: true,
                diagnostics: vec![new_compiler_diagnostic(
                    diag::Could_not_write_file_0_Colon_1,
                    args![build_info_file_name, err],
                )],
                ..EmitResult::default()
            });
        }
        self.snapshot.borrow_mut().build_info_emit_pending = false;
        Some(EmitResult {
            emit_skipped: false,
            emitted_files: vec![build_info_file_name],
            ..EmitResult::default()
        })
    }

    // Go: incremental/program.go:320 ensureHasErrorsForState
    // PORT: Go `program` is the current program.
    fn ensure_has_errors_for_state(&self) {
        let files = source_files();
        let has_include_processing_diagnostics: Box<dyn Fn() -> bool>;
        let mut has_emit_diagnostics = false;
        let (can_use_incremental_state, is_incremental) = {
            let snapshot = self.snapshot.borrow();
            (
                snapshot.can_use_incremental_state(),
                snapshot.options.is_incremental(),
            )
        };
        if can_use_incremental_state {
            let mut found_include_processing_diagnostics: Option<bool> = None;
            {
                let snapshot = self.snapshot.borrow();
                if files.iter().any(|&file| {
                    if snapshot
                        .emit_diagnostics_per_file
                        .contains_key(source_file_info(file).path.as_str())
                    {
                        // emit diagnostics will be encoded in buildInfo;
                        return true;
                    }
                    if found_include_processing_diagnostics.is_none()
                        && !get_include_processor_diagnostics(file).is_empty()
                    {
                        found_include_processing_diagnostics = Some(true);
                    }
                    false
                }) {
                    has_emit_diagnostics = true;
                }
            }
            let value = found_include_processing_diagnostics.unwrap_or(false);
            has_include_processing_diagnostics = Box::new(move || value);
        } else {
            has_emit_diagnostics = self.snapshot.borrow().has_emit_diagnostics;
            let files = files.clone();
            has_include_processing_diagnostics = Box::new(move || {
                files
                    .iter()
                    .any(|&file| !get_include_processor_diagnostics(file).is_empty())
            });
        }

        if has_emit_diagnostics {
            let mut snapshot = self.snapshot.borrow_mut();
            // Record this for only non incremental build info
            snapshot.has_errors = if is_incremental {
                Tristate::False
            } else {
                Tristate::True
            };
            // Dont need to encode semantic errors state since the emit diagnostics are encoded
            snapshot.has_semantic_errors = false;
            return;
        }

        if has_include_processing_diagnostics()
            || !get_config_file_parsing_diagnostics().is_empty()
            || !get_syntactic_diagnostics(Node::NIL).is_empty()
            || !get_program_diagnostics().is_empty()
            || !get_global_diagnostics().is_empty()
        {
            let mut snapshot = self.snapshot.borrow_mut();
            snapshot.has_errors = Tristate::True;
            // Dont need to encode semantic errors state since the syntax and program diagnostics are encoded as present
            snapshot.has_semantic_errors = false;
            return;
        }

        let mut snapshot = self.snapshot.borrow_mut();
        snapshot.has_errors = Tristate::False;
        // Check semantic and emit diagnostics first as we dont need to ask program about it
        let has_semantic_diagnostics = files.iter().any(|&file| {
            match snapshot
                .semantic_diagnostics_per_file
                .get(source_file_info(file).path.as_str())
            {
                // Missing semantic diagnostics in cache will be encoded in incremental buildInfo
                None => is_incremental,
                Some(semantic_diagnostics) => {
                    // cached semantic diagnostics will be encoded in buildInfo
                    semantic_diagnostics
                        .diagnostics
                        .as_ref()
                        .is_some_and(|diagnostics| !diagnostics.is_empty())
                        || !semantic_diagnostics.build_info_diagnostics.is_empty()
                }
            }
        });
        if has_semantic_diagnostics {
            // Because semantic diagnostics are recorded in buildInfo, we dont need to encode hasErrors in incremental buildInfo
            // But encode as errors in non incremental buildInfo
            snapshot.has_semantic_errors = !is_incremental;
        }
    }
}

// Go: compiler/program.go:1728 HandleNoEmitOnError
// PORT: `emitter::program_emit::handle_no_emit_on_error` reads the plain
// program. Go passes the `ProgramLike`, whose bind and semantic
// diagnostics are the incremental ones here, so this is the same body over
// `ProgramLike`.
#[must_use]
pub fn handle_no_emit_on_error(program: &dyn ProgramLike, file: Node) -> Option<EmitResult> {
    if !program.options().no_emit_on_error.is_true() {
        return None; // No emit on error is not set, so we can proceed with emitting
    }

    let diagnostics = get_diagnostics_of_any_program(
        file,
        true,
        &mut |file| program.get_bind_diagnostics(file),
        &mut |file| program.get_semantic_diagnostics(file),
        &mut || program.get_global_diagnostics(),
        &mut |file| program.get_declaration_diagnostics(file),
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

// Go: compiler/program.go:1710 ProgramLike (var _ compiler.ProgramLike = (*Program)(nil))
impl ProgramLike for Program {
    fn options(&self) -> &'static CompilerOptions {
        Program::options(self)
    }
    fn get_bind_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        Program::get_bind_diagnostics(self, file)
    }
    fn get_global_diagnostics(&self) -> Vec<Diagnostic> {
        Program::get_global_diagnostics(self)
    }
    fn get_semantic_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        Program::get_semantic_diagnostics(self, file)
    }
    fn get_declaration_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        Program::get_declaration_diagnostics(self, file)
    }
    fn emit(&self, options: EmitOptions) -> EmitResult {
        Program::emit(self, options)
    }
}
