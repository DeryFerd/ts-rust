use crate::execute::build::command_line::ParsedBuildCommandLine;
use crate::execute::build::up_to_date_status::*;
use crate::execute::incremental::{BuildInfo, compute_hash};
use crate::execute::tsc::ExitStatus;
use crate::frontend::prelude::*;
use std::time::SystemTime;

// This file ports execute/build/buildtask.go.
//
// PORT: design decision D1 (build-mode plan): the program state is
// process-wide, so the Go `compileAndEmit` body that needs a program
// (ReadBuildInfoProgram, NewProgram, incremental.NewProgram,
// EmitAndReportStatistics, writeFile) runs in a worker process. The
// orchestrator side calls it through
// `BuildTaskOrchestrator::compile_and_emit_in_worker` and applies the
// returned `WorkerCompileResult` here, in the same order as Go.
//
// PORT: concurrency. `ParsedCommandLine` is not `Send`, so tasks are
// `Rc<RefCell<BuildTask>>` and run on one thread. Go `done` and
// `reportDone` channels, `prevReporter`, and the mutexes are dropped: the
// orchestrator must run `build_project` in `order` (every upstream task is
// done first) and call `report` in `order`. Workers can still run in
// parallel by using `build_project_start` / `build_project_finish` around
// `compile_and_emit_in_worker`.
//
// PORT: watch mode is out of scope. `updateWatch` and `resetConfig` are
// not ported; `downStream`, `isInitialCycle`, `dirty` and
// `updateDownstream` are kept because `buildProject` uses them.
//
// PORT: `--extendedDiagnostics` statistics and `CompileTimes` are out of
// scope and are not collected. `opts.Testing` is always nil.
//
// PORT: Go `time.Time` is `Option<SystemTime>` (`None` = zero), as in
// up_to_date_status.rs.

// Go: build/buildtask.go:21 buildKind
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BuildKind {
    #[default]
    None,
    Pseudo,
    Program,
}

// Go: build/buildtask.go:28 upstreamTask
// PORT: Go `int` index into `ProjectReferences()` is `usize`.
pub struct UpstreamTask {
    pub task: Rc<RefCell<BuildTask>>,
    pub ref_index: usize,
}

// Go: build/buildtask.go:32 buildInfoEntry
// PORT: Go `*time.Time` is `Option<Option<SystemTime>>` (nil pointer vs a
// pointer to a possibly zero time). Go `*incremental.BuildInfo` is
// `Option<Rc<BuildInfo>>`.
#[derive(Clone)]
pub struct BuildInfoEntry {
    pub build_info: Option<Rc<BuildInfo>>,
    pub path: Path,
    pub m_time: Option<SystemTime>,
    pub dts_time: Option<Option<SystemTime>>,
}

// Go: tsc/diagnostics.go:26 DiagnosticReporter, bound to the task's writer.
// PORT: Go reporters capture `&t.result.builder` as their `io.Writer`. A
// Rust closure cannot hold that borrow while the task also writes to the
// builder, so the reporter takes the writer as its first argument. The
// orchestrator wraps the tsc reporters (`CreateBuilderStatusReporter`,
// `CreateDiagnosticReporter`) into this shape.
pub type TaskDiagnosticReporter = Box<dyn Fn(&mut String, &Diagnostic)>;

// Go: build/buildtask.go:39 taskResult
// PORT: Go `program *incremental.Program` is only read for
// `HasChangedDtsFile()` (and `Testing.OnProgram`), so only that bool is
// kept; the program lives in the worker. `statistics` is dropped (see top).
pub struct TaskResult {
    pub builder: String,
    pub report_status: TaskDiagnosticReporter,
    pub diagnostic_reporter: TaskDiagnosticReporter,
    pub exit_status: ExitStatus,
    pub has_changed_dts_file: bool,
    pub build_kind: BuildKind,
    pub files_to_delete: Vec<String>,
}

impl TaskResult {
    // PORT: Go `&taskResult{}` plus the two reporters that
    // `buildOrCleanProject` (orchestrator.go:575) sets right after.
    pub fn new(
        report_status: TaskDiagnosticReporter,
        diagnostic_reporter: TaskDiagnosticReporter,
    ) -> Self {
        TaskResult {
            builder: String::new(),
            report_status,
            diagnostic_reporter,
            exit_status: ExitStatus::Success,
            has_changed_dts_file: false,
            build_kind: BuildKind::None,
            files_to_delete: Vec::new(),
        }
    }
}

// The result of Go `compileAndEmit`'s program part, computed in a
// `--build-worker` process (plan D1).
// - `exit_status`: `result.Status` of `tsc.EmitAndReportStatistics`.
// - `output`: everything the worker wrote to the task writer (diagnostics
//   through the task diagnostic reporter, listFiles, traces), in order.
// - `diagnostics_count`: `len(result.Diagnostics)`.
// - `emitted_files`: `result.EmitResult.EmittedFiles`.
// - `has_changed_dts_file`: `incremental.Program.HasChangedDtsFile()`.
// - `build_info_file_name`: the file name that `writeFile` wrote with
//   `data.BuildInfo != nil`, or `None` when no build info was written.
#[derive(Clone, Debug)]
pub struct WorkerCompileResult {
    pub exit_status: ExitStatus,
    pub output: String,
    pub diagnostics_count: usize,
    pub emitted_files: Vec<String>,
    pub has_changed_dts_file: bool,
    pub build_info_file_name: Option<String>,
}

// The parts of Go `*Orchestrator` (and its `host`) that a build task uses.
// The orchestrator (orchestrator.rs) implements this.
pub trait BuildTaskOrchestrator {
    // Go: `o.opts.Command`
    fn command(&self) -> &ParsedBuildCommandLine;
    // Go: `o.comparePathsOptions`
    fn compare_paths_options(&self) -> &ComparePathsOptions;
    // Go: orchestrator.go:83 (*Orchestrator).relativeFileName
    fn relative_file_name(&self, file_name: &str) -> String;
    // Go: orchestrator.go:87 (*Orchestrator).toPath
    fn to_path(&self, file_name: &str) -> Path;
    // Go: `o.opts.Sys.Now()`
    fn now(&self) -> SystemTime;
    // Go: `o.host.FS()`
    fn fs(&self) -> Rc<dyn Fs>;
    // Go: build/host.go (*host).GetMTime (cached)
    fn get_m_time(&self, file: &str) -> Option<SystemTime>;
    // Go: build/host.go (*host).SetMTime
    fn set_m_time(&self, file: &str, m_time: SystemTime) -> Result<(), FsError>;
    // Go: build/host.go (*host).storeMTime
    fn store_m_time(&self, file: &str, m_time: SystemTime);
    // Go: `incremental.NewBuildInfoReader(o.host).ReadBuildInfo(config)`
    // (uncached read from disk).
    fn read_build_info_file(&self, config: &ParsedCommandLine) -> Option<Rc<BuildInfo>>;
    // Runs the program part of Go `compileAndEmit` for `config` in a worker
    // process and returns its result (plan D1).
    fn compile_and_emit_in_worker(&self, config: &str, config_path: &Path) -> WorkerCompileResult;
}

// Go: build/buildtask.go:50 BuildTask
// PORT: Go `*tsoptions.ParsedCommandLine` shared with the host cache is
// `Option<Rc<ParsedCommandLine>>`. Go `*upToDateStatus` is
// `Option<UpToDateStatus>`. `pending` is a plain bool (see top).
pub struct BuildTask {
    pub config: String,
    pub resolved: Option<Rc<ParsedCommandLine>>,
    pub up_stream: Vec<UpstreamTask>,
    pub down_stream: Vec<Rc<RefCell<BuildTask>>>, // Only set and used in watch mode
    pub status: Option<UpToDateStatus>,

    // task reporting
    pub result: Option<TaskResult>,

    pub build_info_entry: Option<BuildInfoEntry>,

    pub errors: Vec<Diagnostic>,
    pub pending: bool,
    pub is_initial_cycle: bool,
    pub dirty: bool,
}

impl BuildTask {
    // PORT: Go `&BuildTask{config: config, isInitialCycle: ...}` followed by
    // `task.pending.Store(true)` in createBuildTasks (orchestrator.go:139).
    pub fn new(config: String, is_initial_cycle: bool) -> Self {
        BuildTask {
            config,
            resolved: None,
            up_stream: Vec::new(),
            down_stream: Vec::new(),
            status: None,
            result: None,
            build_info_entry: None,
            errors: Vec::new(),
            pending: true,
            is_initial_cycle,
            dirty: false,
        }
    }

    fn result_mut(&mut self) -> &mut TaskResult {
        self.result.as_mut().expect("task result is set")
    }

    fn resolved(&self) -> &Rc<ParsedCommandLine> {
        self.resolved.as_ref().expect("resolved config")
    }

    fn status(&self) -> &UpToDateStatus {
        self.status.as_ref().expect("status is set")
    }

    // Go: `t.result.reportStatus(diagnostic)`
    fn report_status(&mut self, diagnostic: Diagnostic) {
        let result = self.result_mut();
        (result.report_status)(&mut result.builder, &diagnostic);
    }

    // Go: build/buildtask.go:73 (*BuildTask).waitOnUpstream
    // PORT: no-op. The orchestrator runs tasks in build order on one thread,
    // so every upstream task is done already (see top).
    pub fn wait_on_upstream(&self) {}

    // Go: build/buildtask.go:79 (*BuildTask).unblockDownstream
    pub fn unblock_downstream(&mut self) {
        self.pending = false;
        self.is_initial_cycle = false;
    }

    // Go: build/buildtask.go:85 (*BuildTask).reportDiagnostic
    pub fn report_diagnostic(&mut self, err: Diagnostic) {
        self.errors.push(err.clone());
        let result = self.result_mut();
        (result.diagnostic_reporter)(&mut result.builder, &err);
    }

    // Go: build/buildtask.go:90 (*BuildTask).report
    // PORT: Go writes the buffered output to `Sys.Writer()` and merges into
    // the orchestrator's `orchestratorResult`. That type belongs to the
    // orchestrator, so this takes the task result and errors and returns
    // them; the orchestrator must, in build order:
    //   - append `errors` to `buildResult.errors` when not empty,
    //   - write `result.builder` to the writer,
    //   - raise `buildResult.result.Status` to `result.exit_status` if higher,
    //   - count `result.build_kind` (ProjectsBuilt / TimestampUpdates),
    //   - append `result.files_to_delete` to `buildResult.filesToDelete`.
    pub fn report(&mut self) -> (TaskResult, Vec<Diagnostic>) {
        let result = self.result.take().expect("task result is set");
        (result, self.errors.clone())
    }

    // Go: build/buildtask.go:119 (*BuildTask).buildProject
    pub fn build_project(&mut self, orchestrator: &dyn BuildTaskOrchestrator, path: &Path) {
        if self.build_project_start(orchestrator, path) {
            let result = orchestrator.compile_and_emit_in_worker(&self.config, path);
            self.build_project_finish(orchestrator, path, result);
        }
    }

    // First part of Go `buildProject`, up to the worker call.
    // Returns true when the project needs `compileAndEmit`: the caller must
    // then run `compile_and_emit_in_worker` and call `build_project_finish`.
    // When it returns false the task is done (downstream unblocked).
    pub fn build_project_start(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        path: &Path,
    ) -> bool {
        // Wait on upstream tasks to complete
        self.wait_on_upstream();
        if self.pending {
            self.status = Some(self.get_up_to_date_status(orchestrator, path));
            self.report_up_to_date_status(orchestrator);
            if !self.handle_status_that_doesnt_require_build(orchestrator) {
                self.compile_and_emit_start(orchestrator);
                return true;
            } else {
                if let Some(resolved) = self.resolved.clone() {
                    for diagnostic in resolved.get_config_file_parsing_diagnostics() {
                        self.report_diagnostic(diagnostic);
                    }
                }
                if !self.errors.is_empty() {
                    self.result_mut().exit_status = ExitStatus::DiagnosticsPresentOutputsSkipped;
                }
            }
        } else if !self.errors.is_empty() {
            self.report_up_to_date_status(orchestrator);
            for err in self.errors.clone() {
                // Should not add the diagnostics so just reporting
                let result = self.result_mut();
                (result.diagnostic_reporter)(&mut result.builder, &err);
            }
        }
        self.unblock_downstream();
        false
    }

    // Last part of Go `buildProject`, after the worker call.
    pub fn build_project_finish(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        path: &Path,
        worker_result: WorkerCompileResult,
    ) {
        self.compile_and_emit_finish(orchestrator, worker_result);
        self.update_downstream(orchestrator, path);
        self.unblock_downstream();
    }

    // Go: build/buildtask.go:146 (*BuildTask).updateDownstream
    pub fn update_downstream(&mut self, orchestrator: &dyn BuildTaskOrchestrator, path: &Path) {
        if self.is_initial_cycle {
            return;
        }
        if orchestrator
            .command()
            .build_options
            .stop_build_on_errors
            .is_true()
            && self.status().is_error()
        {
            return;
        }

        let has_changed_dts_file = self.result_mut().has_changed_dts_file;
        for down_stream in &self.down_stream {
            let mut down_stream = down_stream.borrow_mut();
            if let Some(status) = down_stream.status.clone() {
                // PORT: the Go `fallthrough` from UpToDate into the
                // pseudo-build case is written out.
                match status.kind {
                    UpToDateStatusType::UpToDate
                    | UpToDateStatusType::UpToDateWithUpstreamTypes
                    | UpToDateStatusType::UpToDateWithInputFileText => {
                        if status.kind == UpToDateStatusType::UpToDate && !has_changed_dts_file {
                            down_stream.status = Some(UpToDateStatus::with_data(
                                UpToDateStatusType::UpToDateWithUpstreamTypes,
                                status.data.clone(),
                            ));
                        } else if has_changed_dts_file {
                            down_stream.status = Some(UpToDateStatus::with_data(
                                UpToDateStatusType::InputFileNewer,
                                UpToDateStatusData::InputOutputName(InputOutputName {
                                    input: self.config.clone(),
                                    output: status.oldest_output_file_name(),
                                }),
                            ));
                        }
                    }
                    UpToDateStatusType::UpstreamErrors => {
                        let upstream_errors = status.upstream_errors();
                        let ref_config =
                            resolve_config_file_name_of_project_reference(&upstream_errors.ref_);
                        if orchestrator.to_path(&ref_config) == *path {
                            down_stream.reset_status();
                        }
                    }
                    _ => {}
                }
            }
            down_stream.pending = true;
        }
    }

    // Go: build/buildtask.go:179 (*BuildTask).compileAndEmit
    // PORT: split into `compile_and_emit_start`, the worker call and
    // `compile_and_emit_finish` (plan D1).
    pub fn compile_and_emit(&mut self, orchestrator: &dyn BuildTaskOrchestrator, path: &Path) {
        self.compile_and_emit_start(orchestrator);
        let result = orchestrator.compile_and_emit_in_worker(&self.config, path);
        self.compile_and_emit_finish(orchestrator, result);
    }

    // Go: build/buildtask.go:179 compileAndEmit, up to NewProgram.
    pub fn compile_and_emit_start(&mut self, orchestrator: &dyn BuildTaskOrchestrator) {
        self.errors = Vec::new();
        if orchestrator.command().build_options.verbose.is_true() {
            self.report_status(new_compiler_diagnostic(
                diag::Building_project_0,
                args![orchestrator.relative_file_name(&self.config)],
            ));
        }

        // Real build
        // PORT: ReadBuildInfoProgram (skipped with --force), NewProgram,
        // incremental.NewProgram and EmitAndReportStatistics run in the
        // worker. The worker's `writeFile` writes the files; the build info
        // part of `t.writeFile` (onBuildInfoEmit) runs in
        // `compile_and_emit_finish`.
    }

    // Go: build/buildtask.go:179 compileAndEmit, from `t.result.exitStatus =
    // result.Status` on.
    // PORT: worker diagnostics reach the output through `output`, but are
    // not added to `t.errors`. `t.errors` only feeds the pretty error
    // summary and watch mode, which are out of scope.
    pub fn compile_and_emit_finish(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        worker_result: WorkerCompileResult,
    ) {
        {
            let result = self.result_mut();
            result.builder.push_str(&worker_result.output);
            result.has_changed_dts_file = worker_result.has_changed_dts_file;
        }
        // Go: build/buildtask.go:785 (*BuildTask).writeFile, build info part.
        // PORT: Go passes the in-memory BuildInfo that was just written; it
        // is read back from the written file here, which has the same
        // content.
        if let Some(build_info_file_name) = &worker_result.build_info_file_name {
            let build_info = orchestrator.read_build_info_file(self.resolved());
            self.on_build_info_emit(
                orchestrator,
                build_info_file_name,
                build_info,
                worker_result.has_changed_dts_file,
            );
        }

        self.result_mut().exit_status = worker_result.exit_status;
        if (!self
            .resolved()
            .compiler_options()
            .no_emit_on_error
            .is_true()
            || worker_result.diagnostics_count == 0)
            && (!worker_result.emitted_files.is_empty()
                || self.status().kind != UpToDateStatusType::OutOfDateBuildInfoWithErrors)
        {
            // Update time stamps for rest of the outputs
            self.update_time_stamps(
                orchestrator,
                &worker_result.emitted_files,
                diag::Updating_unchanged_output_timestamps_of_project_0,
            );
        }
        self.result_mut().build_kind = BuildKind::Program;
        if worker_result.exit_status == ExitStatus::DiagnosticsPresentOutputsSkipped
            || worker_result.exit_status == ExitStatus::DiagnosticsPresentOutputsGenerated
        {
            self.status = Some(UpToDateStatus::new(UpToDateStatusType::BuildErrors));
        } else {
            let oldest_output_file_name = if !worker_result.emitted_files.is_empty() {
                worker_result.emitted_files[0].clone()
            } else {
                self.resolved()
                    .get_output_file_names()
                    .into_iter()
                    .next()
                    .unwrap_or_default()
            };
            self.status = Some(UpToDateStatus::with_data(
                UpToDateStatusType::UpToDate,
                UpToDateStatusData::String(oldest_output_file_name),
            ));
        }
    }

    // Go: build/buildtask.go:253 (*BuildTask).handleStatusThatDoesntRequireBuild
    pub fn handle_status_that_doesnt_require_build(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
    ) -> bool {
        let build_options = &orchestrator.command().build_options;
        match self.status().kind {
            UpToDateStatusType::UpToDate => {
                if build_options.dry.is_true() {
                    let config = self.config.clone();
                    self.report_status(new_compiler_diagnostic(
                        diag::Project_0_is_up_to_date,
                        args![config],
                    ));
                }
                return true;
            }
            UpToDateStatusType::UpstreamErrors => {
                let upstream_status = self.status().upstream_errors().clone();
                if build_options.verbose.is_true() {
                    let message = if upstream_status.ref_has_upstream_errors {
                        diag::Skipping_build_of_project_0_because_its_dependency_1_was_not_built
                    } else {
                        diag::Skipping_build_of_project_0_because_its_dependency_1_has_errors
                    };
                    self.report_status(new_compiler_diagnostic(
                        message,
                        args![
                            orchestrator.relative_file_name(&self.config),
                            orchestrator.relative_file_name(&upstream_status.ref_)
                        ],
                    ));
                }
                return true;
            }
            UpToDateStatusType::Solution => return true,
            UpToDateStatusType::ConfigFileNotFound => {
                let config = self.config.clone();
                self.report_diagnostic(new_compiler_diagnostic(
                    diag::File_0_not_found,
                    args![config],
                ));
                return true;
            }
            _ => {}
        }

        // update timestamps
        if self.status().is_pseudo_build() {
            if build_options.dry.is_true() {
                let config = self.config.clone();
                self.report_status(new_compiler_diagnostic(
                    diag::A_non_dry_build_would_update_timestamps_for_output_of_project_0,
                    args![config],
                ));
                self.status = Some(UpToDateStatus::new(UpToDateStatusType::UpToDate));
                return true;
            }

            self.update_time_stamps(
                orchestrator,
                &[],
                diag::Updating_output_timestamps_of_project_0,
            );
            let data = self.status().data.clone();
            self.status = Some(UpToDateStatus::with_data(
                UpToDateStatusType::UpToDate,
                data,
            ));
            self.result_mut().build_kind = BuildKind::Pseudo;
            return true;
        }

        if build_options.dry.is_true() {
            let config = self.config.clone();
            self.report_status(new_compiler_diagnostic(
                diag::A_non_dry_build_would_build_project_0,
                args![config],
            ));
            self.status = Some(UpToDateStatus::new(UpToDateStatusType::UpToDate));
            return true;
        }
        false
    }

    // Go: build/buildtask.go:303 (*BuildTask).getUpToDateStatus
    pub fn get_up_to_date_status(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        config_path: &Path,
    ) -> UpToDateStatus {
        if let Some(status) = &self.status {
            return status.clone();
        }
        // Config file not found
        let Some(resolved) = self.resolved.clone() else {
            return UpToDateStatus::new(UpToDateStatusType::ConfigFileNotFound);
        };

        // Solution - nothing to build
        // PORT: Go checks `ProjectReferences() != nil`. The Rust field is a
        // `Vec`, which has no nil state, so an empty list counts as nil.
        if resolved.file_names().is_empty() && !resolved.project_references().is_empty() {
            return UpToDateStatus::new(UpToDateStatusType::Solution);
        }

        let build_options = &orchestrator.command().build_options;
        for upstream in &self.up_stream {
            let upstream_task = upstream.task.borrow();
            let upstream_status = upstream_task.status();
            if build_options.stop_build_on_errors.is_true() && upstream_status.is_error() {
                // Upstream project has errors, so we cannot build this project
                return UpToDateStatus::with_data(
                    UpToDateStatusType::UpstreamErrors,
                    UpToDateStatusData::UpstreamErrors(UpstreamErrors {
                        ref_: resolved.project_references()[upstream.ref_index]
                            .path
                            .clone(),
                        ref_has_upstream_errors: upstream_status.kind
                            == UpToDateStatusType::UpstreamErrors,
                    }),
                );
            }
        }

        if build_options.force.is_true() {
            return UpToDateStatus::new(UpToDateStatusType::ForceBuild);
        }

        // Check the build info
        let build_info_path = resolved.get_build_info_file_name();
        let (build_info, build_info_time) =
            self.load_or_store_build_info(orchestrator, config_path, &build_info_path);
        let Some(build_info) = build_info else {
            return UpToDateStatus::with_data(
                UpToDateStatusType::OutputMissing,
                UpToDateStatusData::String(build_info_path),
            );
        };

        // build info version
        if !build_info.is_valid_version() {
            return UpToDateStatus::with_data(
                UpToDateStatusType::TsVersionOutputOfDate,
                UpToDateStatusData::String(build_info.version.clone()),
            );
        }

        let options = resolved.compiler_options();
        // Report errors if build info indicates errors
        if build_info.errors || // Errors that need to be reported irrespective of "--noCheck"
            (!options.no_check.is_true() && (build_info.semantic_errors || build_info.check_pending))
        {
            // Errors without --noCheck
            return UpToDateStatus::with_data(
                UpToDateStatusType::OutOfDateBuildInfoWithErrors,
                UpToDateStatusData::String(build_info_path),
            );
        }

        let build_info_directory = get_directory_path(&get_normalized_absolute_path(
            &build_info_path,
            &orchestrator.compare_paths_options().current_directory,
        ));
        if options.is_incremental() {
            if !build_info.is_incremental() {
                // Program options out of date
                return UpToDateStatus::with_data(
                    UpToDateStatusType::OutOfDateOptions,
                    UpToDateStatusData::String(build_info_path),
                );
            }

            // Errors need to be reported if build info has errors
            // PORT: Go `!= nil` on these slices is `is_some()`. Go json
            // leaves them nil when the key is absent (`omitzero`).
            if (options.get_emit_declarations() && build_info.emit_diagnostics_per_file.is_some()) || // Always reported errors
                (!options.no_check.is_true() && // Semantic errors if not --noCheck
                    (build_info.change_file_set.is_some()
                        || build_info.semantic_diagnostics_per_file.is_some()))
            {
                return UpToDateStatus::with_data(
                    UpToDateStatusType::OutOfDateBuildInfoWithErrors,
                    UpToDateStatusData::String(build_info_path),
                );
            }

            // Pending emit files
            if !options.no_emit.is_true()
                && (build_info.change_file_set.is_some()
                    || build_info.affected_files_pending_emit.is_some())
            {
                return UpToDateStatus::with_data(
                    UpToDateStatusType::OutOfDateBuildInfoWithPendingEmit,
                    UpToDateStatusData::String(build_info_path),
                );
            }

            // Some of the emit files like source map or dts etc are not yet done
            if build_info.is_emit_pending(&resolved, &build_info_directory) {
                return UpToDateStatus::with_data(
                    UpToDateStatusType::OutOfDateOptions,
                    UpToDateStatusData::String(build_info_path),
                );
            }
        }
        let mut input_text_unchanged = false;
        let mut oldest_output_file_and_time = FileAndTime {
            file: build_info_path.clone(),
            time: build_info_time,
        };
        let mut newest_input_file_and_time = FileAndTime::default();
        let mut seen_roots: FxHashSet<Path> = FxHashSet::default();
        let mut build_info_root_info_reader = None;
        for input_file in resolved.file_names() {
            let input_time = orchestrator.get_m_time(input_file);
            if input_time.is_none() {
                return UpToDateStatus::with_data(
                    UpToDateStatusType::InputFileMissing,
                    UpToDateStatusData::String(input_file.clone()),
                );
            }
            let input_path = orchestrator.to_path(input_file);
            if input_time > oldest_output_file_and_time.time {
                let mut version = String::new();
                let mut current_version = String::new();
                if build_info.is_incremental() {
                    let reader = build_info_root_info_reader.get_or_insert_with(|| {
                        build_info.get_build_info_root_info_reader(
                            &build_info_directory,
                            orchestrator.compare_paths_options(),
                        )
                    });
                    let (build_info_file_info, resolved_input_path) =
                        reader.get_build_info_file_info(&input_path);
                    if let Some(file_info) = build_info_file_info.map(|b| b.get_file_info()) {
                        if !file_info.version().is_empty() {
                            version = file_info.version().to_string();
                            let (text, ok) =
                                orchestrator.fs().read_file(resolved_input_path.as_str());
                            if ok {
                                current_version =
                                    compute_hash(&text, false /*opts.Testing != nil*/);
                                if version == current_version {
                                    input_text_unchanged = true;
                                }
                            }
                        }
                    }
                }

                if version.is_empty() || version != current_version {
                    return UpToDateStatus::with_data(
                        UpToDateStatusType::InputFileNewer,
                        UpToDateStatusData::InputOutputName(InputOutputName {
                            input: input_file.clone(),
                            output: build_info_path,
                        }),
                    );
                }
            }
            if input_time > newest_input_file_and_time.time {
                newest_input_file_and_time = FileAndTime {
                    file: input_file.clone(),
                    time: input_time,
                };
            }
            seen_roots.insert(input_path);
        }

        let reader = build_info_root_info_reader.get_or_insert_with(|| {
            build_info.get_build_info_root_info_reader(
                &build_info_directory,
                orchestrator.compare_paths_options(),
            )
        });
        for root in reader.roots() {
            let root: &Path = &root;
            if !seen_roots.contains(root) {
                // File was root file when project was built but its not any more
                return UpToDateStatus::with_data(
                    UpToDateStatusType::OutOfDateRoots,
                    UpToDateStatusData::InputOutputName(InputOutputName {
                        input: root.as_str().to_string(),
                        output: build_info_path,
                    }),
                );
            }
        }

        if !options.is_incremental() {
            // Check output file stamps
            for output_file in resolved.get_output_file_names() {
                let output_time = orchestrator.get_m_time(&output_file);
                if output_time.is_none() {
                    // Output file missing
                    return UpToDateStatus::with_data(
                        UpToDateStatusType::OutputMissing,
                        UpToDateStatusData::String(output_file),
                    );
                }

                if output_time < newest_input_file_and_time.time {
                    // Output file is older than input file
                    return UpToDateStatus::with_data(
                        UpToDateStatusType::InputFileNewer,
                        UpToDateStatusData::InputOutputName(InputOutputName {
                            input: newest_input_file_and_time.file.clone(),
                            output: output_file,
                        }),
                    );
                }

                if output_time < oldest_output_file_and_time.time {
                    oldest_output_file_and_time = FileAndTime {
                        file: output_file,
                        time: output_time,
                    };
                }
            }
        }

        let mut ref_dts_unchanged = false;
        for upstream in &self.up_stream {
            let upstream_kind = upstream.task.borrow().status().kind;
            if upstream_kind == UpToDateStatusType::Solution {
                // Not dependent on the status or this upstream project
                // (eg: expected cycle was detected and hence skipped, or is solution)
                continue;
            }

            // If the upstream project's newest file is older than our oldest output,
            // we can't be out of date because of it
            // inputTime will not be present if we just built this project or updated timestamps
            // - in that case we do want to either build or update timestamps
            let skip = match upstream.task.borrow().status().input_output_file_and_time() {
                Some(ref_input_output_file_and_time) => {
                    ref_input_output_file_and_time.input.time.is_some()
                        && ref_input_output_file_and_time.input.time
                            < oldest_output_file_and_time.time
                }
                None => false,
            };
            if skip {
                continue;
            }

            // Check if tsbuildinfo path is shared, then we need to rebuild
            if self.has_conflicting_build_info(orchestrator, &upstream.task.borrow()) {
                // We have an output older than an upstream output - we are out of date
                return UpToDateStatus::with_data(
                    UpToDateStatusType::InputFileNewer,
                    UpToDateStatusData::InputOutputName(InputOutputName {
                        input: resolved.project_references()[upstream.ref_index]
                            .path
                            .clone(),
                        output: oldest_output_file_and_time.file.clone(),
                    }),
                );
            }

            // If the upstream project has only change .d.ts files, and we've built
            // *after* those files, then we're "pseudo up to date" and eligible for a fast rebuild
            let newest_dts_change_time = upstream
                .task
                .borrow_mut()
                .get_latest_changed_dts_m_time(orchestrator);
            if newest_dts_change_time.is_some()
                && newest_dts_change_time < oldest_output_file_and_time.time
            {
                ref_dts_unchanged = true;
                continue;
            }

            // We have an output older than an upstream output - we are out of date
            return UpToDateStatus::with_data(
                UpToDateStatusType::InputFileNewer,
                UpToDateStatusData::InputOutputName(InputOutputName {
                    input: resolved.project_references()[upstream.ref_index]
                        .path
                        .clone(),
                    output: oldest_output_file_and_time.file.clone(),
                }),
            );
        }

        let check_input_file_time = |input_file: &str| -> Option<UpToDateStatus> {
            let input_time = orchestrator.get_m_time(input_file);
            if input_time > oldest_output_file_and_time.time {
                // Output file is older than input file
                return Some(UpToDateStatus::with_data(
                    UpToDateStatusType::InputFileNewer,
                    UpToDateStatusData::InputOutputName(InputOutputName {
                        input: input_file.to_string(),
                        output: oldest_output_file_and_time.file.clone(),
                    }),
                ));
            }
            None
        };

        if let Some(config_status) = check_input_file_time(&self.config) {
            return config_status;
        }

        for extended_config in resolved.extended_source_files() {
            if let Some(extended_config_status) = check_input_file_time(extended_config) {
                return extended_config_status;
            }
        }

        // !!! sheetal TODO : watch??
        // // Check package file time
        // const packageJsonLookups = state.lastCachedPackageJsonLookups.get(resolvedPath);
        // const dependentPackageFileStatus = packageJsonLookups && forEachKey(
        //     packageJsonLookups,
        //     path => checkConfigFileUpToDateStatus(state, path, oldestOutputFileTime, oldestOutputFileName),
        // );
        // if (dependentPackageFileStatus) return dependentPackageFileStatus;

        UpToDateStatus::with_data(
            if ref_dts_unchanged {
                UpToDateStatusType::UpToDateWithUpstreamTypes
            } else if input_text_unchanged {
                UpToDateStatusType::UpToDateWithInputFileText
            } else {
                UpToDateStatusType::UpToDate
            },
            UpToDateStatusData::InputOutputFileAndTime(InputOutputFileAndTime {
                input: newest_input_file_and_time,
                output: oldest_output_file_and_time,
                build_info: build_info_path,
            }),
        )
    }

    // Go: build/buildtask.go:520 (*BuildTask).reportUpToDateStatus
    pub fn report_up_to_date_status(&mut self, orchestrator: &dyn BuildTaskOrchestrator) {
        if !orchestrator.command().build_options.verbose.is_true() {
            return;
        }
        let o = orchestrator;
        let config = o.relative_file_name(&self.config);
        let status = self.status().clone();
        let diagnostic = match status.kind {
            UpToDateStatusType::ConfigFileNotFound => new_compiler_diagnostic(
                diag::Project_0_is_out_of_date_because_config_file_does_not_exist,
                args![config],
            ),
            UpToDateStatusType::UpstreamErrors => {
                let upstream_status = status.upstream_errors();
                new_compiler_diagnostic(
                    if upstream_status.ref_has_upstream_errors {
                        diag::Project_0_can_t_be_built_because_its_dependency_1_was_not_built
                    } else {
                        diag::Project_0_can_t_be_built_because_its_dependency_1_has_errors
                    },
                    args![config, o.relative_file_name(&upstream_status.ref_)],
                )
            }
            UpToDateStatusType::BuildErrors => new_compiler_diagnostic(
                diag::Project_0_is_out_of_date_because_it_has_errors,
                args![config],
            ),
            UpToDateStatusType::UpToDate => {
                // This is to ensure skipping verbose log for projects that were built,
                // and then some other package changed but this package doesnt need update
                let Some(input_output_file_and_time) = status.input_output_file_and_time() else {
                    return;
                };
                new_compiler_diagnostic(
                    diag::Project_0_is_up_to_date_because_newest_input_1_is_older_than_output_2,
                    args![
                        config,
                        o.relative_file_name(&input_output_file_and_time.input.file),
                        o.relative_file_name(&input_output_file_and_time.output.file)
                    ],
                )
            }
            UpToDateStatusType::UpToDateWithUpstreamTypes => new_compiler_diagnostic(
                diag::Project_0_is_up_to_date_with_d_ts_files_from_its_dependencies,
                args![config],
            ),
            UpToDateStatusType::UpToDateWithInputFileText => new_compiler_diagnostic(
                diag::Project_0_is_up_to_date_but_needs_to_update_timestamps_of_output_files_that_are_older_than_input_files,
                args![config],
            ),
            UpToDateStatusType::InputFileMissing => new_compiler_diagnostic(
                diag::Project_0_is_out_of_date_because_input_1_does_not_exist,
                args![config, o.relative_file_name(status.data_string())],
            ),
            UpToDateStatusType::OutputMissing => new_compiler_diagnostic(
                diag::Project_0_is_out_of_date_because_output_file_1_does_not_exist,
                args![config, o.relative_file_name(status.data_string())],
            ),
            UpToDateStatusType::InputFileNewer => {
                let input_output = status.input_output_name().expect("inputOutputName");
                new_compiler_diagnostic(
                    diag::Project_0_is_out_of_date_because_output_1_is_older_than_input_2,
                    args![
                        config,
                        o.relative_file_name(&input_output.output),
                        o.relative_file_name(&input_output.input)
                    ],
                )
            }
            UpToDateStatusType::OutOfDateBuildInfoWithPendingEmit => new_compiler_diagnostic(
                diag::Project_0_is_out_of_date_because_buildinfo_file_1_indicates_that_some_of_the_changes_were_not_emitted,
                args![config, o.relative_file_name(status.data_string())],
            ),
            UpToDateStatusType::OutOfDateBuildInfoWithErrors => new_compiler_diagnostic(
                diag::Project_0_is_out_of_date_because_buildinfo_file_1_indicates_that_program_needs_to_report_errors,
                args![config, o.relative_file_name(status.data_string())],
            ),
            UpToDateStatusType::OutOfDateOptions => new_compiler_diagnostic(
                diag::Project_0_is_out_of_date_because_buildinfo_file_1_indicates_there_is_change_in_compilerOptions,
                args![config, o.relative_file_name(status.data_string())],
            ),
            UpToDateStatusType::OutOfDateRoots => {
                let input_output = status.input_output_name().expect("inputOutputName");
                new_compiler_diagnostic(
                    diag::Project_0_is_out_of_date_because_buildinfo_file_1_indicates_that_file_2_was_root_file_of_compilation_but_not_any_more,
                    args![
                        config,
                        o.relative_file_name(&input_output.output),
                        o.relative_file_name(&input_output.input)
                    ],
                )
            }
            UpToDateStatusType::TsVersionOutputOfDate => new_compiler_diagnostic(
                diag::Project_0_is_out_of_date_because_output_for_it_was_generated_with_version_1_that_differs_with_current_version_2,
                args![config, o.relative_file_name(status.data_string()), version()],
            ),
            UpToDateStatusType::ForceBuild => new_compiler_diagnostic(
                diag::Project_0_is_being_forcibly_rebuilt,
                args![config],
            ),
            UpToDateStatusType::Solution => {
                // Does not need to report status
                return;
            }
        };
        self.report_status(diagnostic);
    }

    // Go: build/buildtask.go:627 (*BuildTask).canUpdateJsDtsOutputTimestamps
    pub fn can_update_js_dts_output_timestamps(&self) -> bool {
        let options = self.resolved().compiler_options();
        !options.no_emit.is_true() && !options.is_incremental()
    }

    // Go: build/buildtask.go:631 (*BuildTask).updateTimeStamps
    pub fn update_time_stamps(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        emitted_files: &[String],
        verbose_message: &'static Message,
    ) {
        let emitted: FxHashSet<&str> = emitted_files.iter().map(String::as_str).collect();
        let mut verbose_message_reported = false;
        let build_info_name = self.resolved().get_build_info_file_name();
        let now = orchestrator.now();
        let mut update_time_stamp = |this: &mut BuildTask, file: &str| {
            if emitted.contains(file) {
                return;
            }
            if !verbose_message_reported && orchestrator.command().build_options.verbose.is_true() {
                let config = orchestrator.relative_file_name(&this.config);
                this.report_status(new_compiler_diagnostic(verbose_message, args![config]));
                verbose_message_reported = true;
            }
            let err = orchestrator.set_m_time(file, now);
            if err.is_ok() {
                if file == build_info_name {
                    if let Some(entry) = &mut this.build_info_entry {
                        entry.m_time = Some(now);
                    }
                } else if this.store_output_time_stamp(orchestrator) {
                    orchestrator.store_m_time(file, now);
                }
            }
        };

        if self.can_update_js_dts_output_timestamps() {
            for output_file in self.resolved().get_output_file_names() {
                update_time_stamp(self, &output_file);
            }
        }
        let build_info_file_name = self.resolved().get_build_info_file_name();
        update_time_stamp(self, &build_info_file_name);
    }

    // Go: build/buildtask.go:668 (*BuildTask).cleanProject
    pub fn clean_project(&mut self, orchestrator: &dyn BuildTaskOrchestrator, path: &Path) {
        let Some(resolved) = self.resolved.clone() else {
            let config = self.config.clone();
            self.report_diagnostic(new_compiler_diagnostic(
                diag::File_0_not_found,
                args![config],
            ));
            self.result_mut().exit_status = ExitStatus::DiagnosticsPresentOutputsSkipped;
            return;
        };

        let inputs: FxHashSet<Path> = resolved
            .file_names()
            .iter()
            .map(|file_name| orchestrator.to_path(file_name))
            .collect();
        for output_file in resolved.get_output_file_names() {
            self.clean_project_output(orchestrator, &output_file, &inputs);
        }
        self.clean_project_output(orchestrator, &resolved.get_build_info_file_name(), &inputs);
    }

    // Go: build/buildtask.go:681 (*BuildTask).cleanProjectOutput
    pub fn clean_project_output(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        output_file: &str,
        inputs: &FxHashSet<Path>,
    ) {
        let output_path = orchestrator.to_path(output_file);
        // If output name is same as input file name, do not delete and ignore the error
        if inputs.contains(&output_path) {
            return;
        }
        let fs = orchestrator.fs();
        if fs.file_exists(output_file) {
            if !orchestrator.command().build_options.dry.is_true() {
                let err = fs.remove(output_file);
                if err.is_err() {
                    self.report_diagnostic(new_compiler_diagnostic(
                        diag::Failed_to_delete_file_0,
                        args![output_file],
                    ));
                }
            } else {
                self.result_mut()
                    .files_to_delete
                    .push(output_file.to_string());
            }
        }
    }

    // Go: build/buildtask.go:700 (*BuildTask).updateWatch
    // PORT: watch mode only; not ported (see top).

    // Go: build/buildtask.go:710 (*BuildTask).resetStatus
    pub fn reset_status(&mut self) {
        self.status = None;
        self.pending = true;
        self.errors = Vec::new();
    }

    // Go: build/buildtask.go:716 (*BuildTask).resetConfig
    // PORT: watch mode only; not ported (see top).

    // Go: build/buildtask.go:721 (*BuildTask).loadOrStoreBuildInfo
    pub fn load_or_store_build_info(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        config_path: &Path,
        build_info_file_name: &str,
    ) -> (Option<Rc<BuildInfo>>, Option<SystemTime>) {
        let path = orchestrator.to_path(build_info_file_name);
        if let Some(entry) = &self.build_info_entry {
            if entry.path == path {
                return (entry.build_info.clone(), entry.m_time);
            }
        }
        let build_info = orchestrator.read_build_info_file(self.resolved());
        let mut m_time = None;
        if build_info.is_some() {
            m_time = orchestrator.get_m_time(build_info_file_name);
        }
        self.build_info_entry = Some(BuildInfoEntry {
            build_info: build_info.clone(),
            path,
            m_time,
            dts_time: None,
        });
        (build_info, m_time)
    }

    // Go: build/buildtask.go:741 (*BuildTask).onBuildInfoEmit
    pub fn on_build_info_emit(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        build_info_file_name: &str,
        build_info: Option<Rc<BuildInfo>>,
        has_changed_dts_file: bool,
    ) {
        let m_time = orchestrator.now();
        let dts_time = if has_changed_dts_file {
            Some(Some(m_time))
        } else if let Some(entry) = &self.build_info_entry {
            entry.dts_time
        } else {
            None
        };
        self.build_info_entry = Some(BuildInfoEntry {
            build_info,
            path: orchestrator.to_path(build_info_file_name),
            m_time: Some(m_time),
            dts_time,
        });
    }

    // Go: build/buildtask.go:759 (*BuildTask).hasConflictingBuildInfo
    pub fn has_conflicting_build_info(
        &self,
        orchestrator: &dyn BuildTaskOrchestrator,
        upstream: &BuildTask,
    ) -> bool {
        if let (Some(entry), Some(upstream_entry)) =
            (&self.build_info_entry, &upstream.build_info_entry)
        {
            return entry.path == upstream_entry.path;
        }
        false
    }

    // Go: build/buildtask.go:766 (*BuildTask).getLatestChangedDtsMTime
    pub fn get_latest_changed_dts_m_time(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
    ) -> Option<SystemTime> {
        let entry = self
            .build_info_entry
            .as_mut()
            .expect("buildInfoEntry is set");
        if let Some(dts_time) = entry.dts_time {
            return dts_time;
        }
        // PORT: Go reads `t.buildInfoEntry.buildInfo.LatestChangedDtsFile` and
        // panics on a nil build info.
        let build_info = entry.build_info.as_ref().expect("buildInfo is set");
        let dts_time = orchestrator.get_m_time(&get_normalized_absolute_path(
            &build_info.latest_changed_dts_file,
            &get_directory_path(entry.path.as_str()),
        ));
        entry.dts_time = Some(dts_time);
        dts_time
    }

    // Go: build/buildtask.go:781 (*BuildTask).storeOutputTimeStamp
    pub fn store_output_time_stamp(&self, orchestrator: &dyn BuildTaskOrchestrator) -> bool {
        orchestrator.command().compiler_options.watch.is_true()
            && !self.resolved().compiler_options().is_incremental()
    }

    // Go: build/buildtask.go:785 (*BuildTask).writeFile
    // PORT: runs in the worker (plan D1). Its build info branch is
    // `on_build_info_emit` in `compile_and_emit_finish`; its watch-only
    // `storeMTime` branch is never taken without watch mode.
}
