use crate::emitter::program_emit::{WriteFile, WriteFileData};
use crate::execute::build::command_line::ParsedBuildCommandLine;
use crate::execute::build::host::{BuildCompilerHost, BuildHost};
use crate::execute::build::up_to_date_status::*;
use crate::execute::incremental::emit_files::fs_error_text;
use crate::execute::incremental::incremental::{BuildInfoReader, Host as IncrementalHost};
use crate::execute::incremental::program::{
    Program as IncrementalProgram, new_program as new_incremental_program, read_build_info_program,
};
use crate::execute::incremental::{BuildInfo, compute_hash};
use crate::execute::tsc::compile::{CompileTimes, System, Writer};
use crate::execute::tsc::diagnostics::{
    DiagnosticReporter, create_diagnostic_reporter, quiet_diagnostics_reporter,
};
use crate::execute::tsc::emit::{
    EmitInput, emit_and_report_statistics, get_trace_with_writer_from_sys,
};
use crate::execute::tsc::{ExitStatus, Statistics};
use crate::frontend::prelude::*;
// PORT: testing
use crate::execute::tsc::CommandLineTesting;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::SystemTime;

// This file ports execute/build/buildtask.go.
//
// PORT: concurrency. `ParsedCommandLine` and the frontend program are not
// `Send`, so tasks are `Rc<RefCell<BuildTask>>` and run on one thread, the
// orchestrator thread. It is the loading thread of every program of the
// build. Go `done` and `reportDone` channels, `prevReporter`, and the
// mutexes are dropped. `buildProject` is split where `compileAndEmit` has
// made the program (`build_project_start`) and the rest
// (`build_project_finish`). The orchestrator starts a task after its
// upstream tasks are done, finishes it later, and calls `report` in
// `order` (see orchestrator.rs).
//
// PORT: the watch-only `updateWatch` and `resetConfig` are in
// orchestrator_watch.rs, with the orchestrator watch code.
//
// PORT: the task keeps the statistics of `tsc.EmitAndReportStatistics` for
// the build aggregate, as Go does. `opts.Testing` is
// `BuildTaskOrchestrator::testing` (`None` outside tests).
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
// PORT: Go `program *incremental.Program` is `program` (`None` = nil). The
// task keeps it until it reports, for `Testing.OnProgram`, and the
// orchestrator releases it there (`release_task_program`), where Go drops
// `t.result`. `has_changed_dts_file` is its `HasChangedDtsFile()` after the
// emit, which `updateDownstream` reads. Go `*tsc.Statistics` is an `Option`
// (nil = `None`).
pub struct TaskResult {
    pub builder: String,
    pub report_status: TaskDiagnosticReporter,
    pub diagnostic_reporter: TaskDiagnosticReporter,
    pub exit_status: ExitStatus,
    pub statistics: Option<Statistics>,
    pub program: Option<IncrementalProgram>,
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
            statistics: None,
            program: None,
            has_changed_dts_file: false,
            build_kind: BuildKind::None,
            files_to_delete: Vec::new(),
        }
    }
}

/// Go drops `t.result` after `report`, and with it the task's program.
/// This frees the checker pool and the frontend of the program
/// (`program::release_program`). Its files stay published, so the
/// diagnostics in `t.errors` can still be written.
pub fn release_task_program(program: IncrementalProgram) {
    let go_program = program.get_program();
    drop(program);
    crate::program::release_program(go_program);
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
    // Go: `o.opts.Sys`
    fn sys(&self) -> Rc<dyn System>;
    // Go: `o.host`
    fn host(&self) -> Rc<BuildHost>;
    // Go: `o.opts.Testing`
    // PORT: testing. `None` outside tests.
    fn testing(&self) -> Option<Rc<dyn CommandLineTesting>> {
        None
    }
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

    // PORT: not in Go. The compile between `build_project_start` and
    // `build_project_finish`.
    compile: Option<PendingCompile>,
}

// The state of Go `compileAndEmit` from `NewProgram` to
// `EmitAndReportStatistics`: the program is made and not emitted yet.
struct PendingCompile {
    program: &'static GoProgram,
    incremental_program: IncrementalProgram,
    // Go `&t.result.builder` as the compile writer (see
    // `compile_and_emit_start`).
    builder: Rc<RefCell<Vec<u8>>>,
    writer: Writer,
    // Go `t.reportDiagnostic`, and what it appends to `t.errors`.
    report_diagnostic: DiagnosticReporter,
    errors: Rc<RefCell<Vec<Diagnostic>>>,
    compile_times: Rc<RefCell<CompileTimes>>,
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
            compile: None,
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
    // PORT: no-op. The orchestrator starts a task only when its upstream
    // tasks are done (see top).
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
    //   - aggregate `result.statistics` into `buildResult.statistics` when set,
    //   - count `result.build_kind` (ProjectsBuilt / TimestampUpdates),
    //   - append `result.files_to_delete` to `buildResult.filesToDelete`.
    pub fn report(&mut self) -> (TaskResult, Vec<Diagnostic>) {
        let result = self.result.take().expect("task result is set");
        (result, self.errors.clone())
    }

    // Go: build/buildtask.go:119 (*BuildTask).buildProject, up to the
    // program that `compileAndEmit` makes (`compile_and_emit_start`).
    // PORT: Go runs up to `numRoutines` tasks at the same time, and a task
    // that runs beside others makes its program before they write their
    // outputs. The orchestrator keeps that order on one thread (see
    // orchestrator.rs), so `buildProject` is split here. It returns true
    // when the task compiles: then the caller must call
    // `build_project_finish`. When it returns false the task is done
    // (downstream unblocked).
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
                self.compile_and_emit_start(orchestrator, path);
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

    // Go: build/buildtask.go:119 (*BuildTask).buildProject, from the emit
    // of `compileAndEmit` on (see `build_project_start`).
    pub fn build_project_finish(&mut self, orchestrator: &dyn BuildTaskOrchestrator, path: &Path) {
        self.compile_and_emit_finish(orchestrator);
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

    // Go: build/buildtask.go:179 (*BuildTask).compileAndEmit, up to
    // `incremental.NewProgram` (see `build_project_start`).
    // PORT: the program is a program version of this multi-program process
    // (`program::new_program_version`), made on this thread, the loading
    // thread of every program of the build. It is current
    // (`core::enter_program`) while it is used, because the `program.rs`
    // functions read `prog()`.
    // PORT: Go `EmitInput.Writer`, the trace writer and
    // `t.result.diagnosticReporter` write to `&t.result.builder`. The task
    // reporters take the builder per call (`TaskDiagnosticReporter`) and
    // the tsc code takes a `Writer`, so the compile writes to its own
    // buffer, which `compile_and_emit_finish` appends to the builder.
    // Nothing else writes to the builder meanwhile, so the order is Go's.
    pub fn compile_and_emit_start(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        path: &Path,
    ) {
        self.errors = Vec::new();
        let command = orchestrator.command();
        if command.build_options.verbose.is_true() {
            self.report_status(new_compiler_diagnostic(
                diag::Building_project_0,
                args![orchestrator.relative_file_name(&self.config)],
            ));
        }

        let sys = orchestrator.sys();
        let host = orchestrator.host();
        let testing = orchestrator.testing();
        let resolved = self.resolved().clone();
        let builder: Rc<RefCell<Vec<u8>>> = Rc::default();
        let writer: Writer = builder.clone();
        // Go: build/buildtask.go:85 (*BuildTask).reportDiagnostic. The
        // diagnostics go to `t.errors` in `compile_and_emit_finish`.
        let errors: Rc<RefCell<Vec<Diagnostic>>> = Rc::default();
        let report_diagnostic: DiagnosticReporter = {
            let errors = errors.clone();
            // Go `t.result.diagnosticReporter` (orchestrator.go:597
            // createDiagnosticReporter(task)).
            let report = create_diagnostic_reporter(
                &*sys,
                writer.clone(),
                &command.locale(),
                &command.compiler_options,
            );
            Rc::new(move |err: &Diagnostic| {
                errors.borrow_mut().push(err.clone());
                report(err);
            })
        };

        // Real build
        let compile_times = Rc::new(RefCell::new(CompileTimes::default()));
        let config_time = host
            .config_times
            .borrow()
            .get(path)
            .copied()
            .unwrap_or_default();
        compile_times.borrow_mut().config_time = config_time;
        let build_info_read_start = sys.now();
        let mut old_program = None;
        if !command.build_options.force.is_true() {
            // Go: `ReadBuildInfoProgram(t.resolved, o.host, o.host)`. Its
            // `o.host.ReadBuildInfo(t.resolved)` (build/host.go:77) is this
            // task's `loadOrStoreBuildInfo`.
            let config_path = orchestrator.to_path(resolved.config_name());
            let (build_info, _) = self.load_or_store_build_info(
                orchestrator,
                &config_path,
                &resolved.get_build_info_file_name(),
            );
            old_program = read_build_info_program(&resolved, &TaskBuildInfo(build_info), &*host);
        }
        compile_times.borrow_mut().build_info_read_time = elapsed(&*sys, build_info_read_start);
        let parse_start = sys.now();
        // Go: compiler.NewProgram(compiler.ProgramOptions{Config, Host})
        let program = crate::execute::execute_tsc::new_program_version(
            Rc::new(BuildCompilerHost {
                host: host.clone(),
                trace: get_trace_with_writer_from_sys(
                    writer.clone(),
                    command.locale(),
                    testing.clone(),
                ),
            }),
            resolved,
        );
        compile_times.borrow_mut().parse_time = elapsed(&*sys, parse_start);
        let changes_compute_start = sys.now();
        let incremental_program = {
            let _scope = crate::core::enter_program(Some(program));
            new_incremental_program(
                old_program.as_ref(),
                host as Rc<dyn IncrementalHost>,
                testing.is_some(),
            )
        };
        compile_times.borrow_mut().changes_compute_time = elapsed(&*sys, changes_compute_start);
        self.compile = Some(PendingCompile {
            program,
            incremental_program,
            builder,
            writer,
            report_diagnostic,
            errors,
            compile_times,
        });
    }

    // Go: build/buildtask.go:179 (*BuildTask).compileAndEmit, from
    // `EmitAndReportStatistics` on (see `compile_and_emit_start`).
    pub fn compile_and_emit_finish(&mut self, orchestrator: &dyn BuildTaskOrchestrator) {
        let PendingCompile {
            program,
            incremental_program,
            builder,
            writer,
            report_diagnostic,
            errors,
            compile_times,
        } = self.compile.take().expect("compile_and_emit_start ran");
        let sys = orchestrator.sys();
        let host = orchestrator.host();
        let resolved = self.resolved().clone();
        let written_build_info: WrittenBuildInfo = Arc::default();
        let write_file = new_task_write_file(
            written_build_info.clone(),
            self.store_output_time_stamp(orchestrator),
            host.m_times.clone(),
            orchestrator.compare_paths_options().clone(),
        );
        let (result, statistics) = {
            let _scope = crate::core::enter_program(Some(program));
            WRITE_FILE_SYS.with(|write_file_sys| *write_file_sys.borrow_mut() = Some(sys.clone()));
            let emitted = emit_and_report_statistics(&EmitInput {
                sys: &*sys,
                program_like: &incremental_program,
                config: Some(&resolved),
                report_diagnostic,
                report_error_summary: quiet_diagnostics_reporter(),
                writer,
                write_file: Some(write_file),
                compile_times,
                testing: orchestrator.testing(),
                testing_m_times_cache: Some(&*host.m_times),
            });
            WRITE_FILE_SYS.with(|write_file_sys| *write_file_sys.borrow_mut() = None);
            emitted
        };
        let has_changed_dts_file = incremental_program.has_changed_dts_file();
        // Go appends to `t.errors` while `EmitAndReportStatistics` reports.
        self.errors.extend(errors.take());
        {
            let task_result = self.result_mut();
            task_result
                .builder
                .push_str(&String::from_utf8_lossy(&builder.borrow()));
            task_result.has_changed_dts_file = has_changed_dts_file;
            task_result.program = Some(incremental_program);
        }
        // Go: build/buildtask.go:785 (*BuildTask).writeFile, the build info
        // part (`onBuildInfoEmit`), with the time of the write.
        // PORT: it runs when the emit is done (see `new_task_write_file`).
        // The build info is the last file that the emit writes, so
        // `HasChangedDtsFile()` has its final value in Go too.
        let written = written_build_info
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        if let Some((build_info_file_name, build_info, m_time)) = written {
            let build_info = Arc::try_unwrap(build_info).unwrap_or_else(|shared| (*shared).clone());
            self.on_build_info_emit(
                orchestrator,
                &build_info_file_name,
                Some(Rc::new(build_info)),
                has_changed_dts_file,
                m_time,
            );
        }

        self.result_mut().exit_status = result.status;
        self.result_mut().statistics = statistics;
        let emitted_files = &result.emit_result.emitted_files;
        if (!resolved.compiler_options().no_emit_on_error.is_true()
            || result.diagnostics.is_empty())
            && (!emitted_files.is_empty()
                || self.status().kind != UpToDateStatusType::OutOfDateBuildInfoWithErrors)
        {
            // Update time stamps for rest of the outputs
            self.update_time_stamps(
                orchestrator,
                emitted_files,
                diag::Updating_unchanged_output_timestamps_of_project_0,
            );
        }
        self.result_mut().build_kind = BuildKind::Program;
        if result.status == ExitStatus::DiagnosticsPresentOutputsSkipped
            || result.status == ExitStatus::DiagnosticsPresentOutputsGenerated
        {
            self.status = Some(UpToDateStatus::new(UpToDateStatusType::BuildErrors));
        } else {
            let oldest_output_file_name = match emitted_files.first() {
                Some(first) => first.clone(),
                None => resolved
                    .get_output_file_names()
                    .into_iter()
                    .next()
                    .unwrap_or_default(),
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
        if resolved.file_names().is_empty() && resolved.has_project_references() {
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
                                    compute_hash(&text, orchestrator.testing().is_some());
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

    // Go: build/buildtask.go:698 (*BuildTask).updateWatch
    // PORT: in orchestrator_watch.rs.

    // Go: build/buildtask.go:710 (*BuildTask).resetStatus
    pub fn reset_status(&mut self) {
        self.status = None;
        self.pending = true;
        self.errors = Vec::new();
    }

    // Go: build/buildtask.go:714 (*BuildTask).resetConfig
    // PORT: in orchestrator_watch.rs.

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
    // PORT: Go takes `mTime := orchestrator.opts.Sys.Now()` here, in the
    // `writeFile` call of the build info, before the test `OnEmittedFiles`
    // stamps the emitted files. `new_task_write_file` takes the time at
    // that write, and the caller passes it as `m_time`.
    pub fn on_build_info_emit(
        &mut self,
        orchestrator: &dyn BuildTaskOrchestrator,
        build_info_file_name: &str,
        build_info: Option<Rc<BuildInfo>>,
        has_changed_dts_file: bool,
        m_time: SystemTime,
    ) {
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
    // PORT: see `new_task_write_file`.
}

/// The build info that the emit wrote: its file name, Go
/// `WriteFileData.BuildInfo`, and the Go `Sys.Now()` of `onBuildInfoEmit`,
/// taken at the write.
type WrittenBuildInfo = Arc<Mutex<Option<(String, Arc<BuildInfo>, SystemTime)>>>;

// Go: build/buildtask.go:785 (*BuildTask).writeFile
// PORT: emit writes the source outputs on the checker threads, so the
// callback is `Send` and cannot hold the task, the `Rc` system or the `Rc`
// file system. Go writes through `orchestrator.host.FS()` (cachedvfs over
// bundled over osvfs); both wrappers pass a write of a real path to osvfs
// (cachedvfs.go:148 WriteFile), so this writes with the osvfs of the
// calling thread. The build info branch keeps what `onBuildInfoEmit` needs
// in `written`, and `compile_and_emit_finish` calls it after the emit. The
// watch-only `storeMTime` branch stores into the build host `m_times` at
// once (Go `SyncMap`), before the test `OnEmittedFiles` reads it.
fn new_task_write_file(
    written: WrittenBuildInfo,
    store_output_time_stamp: bool,
    m_times: Arc<Mutex<FxHashMap<Path, Option<SystemTime>>>>,
    compare_paths_options: ComparePathsOptions,
) -> WriteFile {
    Arc::new(
        move |file_name: &str, text: &str, data: &mut WriteFileData| -> Result<(), String> {
            osvfs_fs()
                .write_file(file_name, text)
                .map_err(|err| fs_error_text(&err))?;
            if let Some(build_info) = &data.build_info {
                *written.lock().unwrap_or_else(PoisonError::into_inner) = Some((
                    file_name.to_string(),
                    build_info.clone(),
                    task_write_file_now(),
                ));
            } else if store_output_time_stamp {
                // Store time stamps
                // Go: orchestrator.host.storeMTime(fileName, orchestrator.opts.Sys.Now())
                let m_time = task_write_file_now();
                let path = to_path(
                    file_name,
                    &compare_paths_options.current_directory,
                    compare_paths_options.use_case_sensitive_file_names,
                );
                m_times
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .insert(path, Some(m_time));
            }
            Ok(())
        },
    )
}

thread_local! {
    // Go `orchestrator.opts.Sys` of the task `writeFile`: the orchestrator
    // system, on the orchestrator thread, while a task emits (see
    // `task_write_file_now`).
    static WRITE_FILE_SYS: RefCell<Option<Rc<dyn System>>> = const { RefCell::new(None) };
}

// Go `orchestrator.opts.Sys.Now()` in the task `writeFile`.
// PORT: emit writes the source files' outputs on the checker threads,
// which cannot hold the `Rc` system; there it is the OS system's `Now`
// (`SystemTime::now`). The build info write runs on the orchestrator thread
// (incremental `emitBuildInfo`), so its time comes from the orchestrator
// system, in the same order as Go with the test `OnEmittedFiles` times.
fn task_write_file_now() -> SystemTime {
    WRITE_FILE_SYS
        .with(|sys| sys.borrow().as_ref().map(|sys| sys.now()))
        .unwrap_or_else(SystemTime::now)
}

/// Go `o.host` as the `incremental.BuildInfoReader` of
/// `ReadBuildInfoProgram`: its `ReadBuildInfo` (build/host.go:77) is the
/// task's `loadOrStoreBuildInfo`, whose value this holds.
struct TaskBuildInfo(Option<Rc<BuildInfo>>);

impl BuildInfoReader for TaskBuildInfo {
    fn read_build_info(&self, _config: &ParsedCommandLine) -> Option<BuildInfo> {
        self.0.as_deref().cloned()
    }
}

/// Go `o.opts.Sys.Now().Sub(start)`.
fn elapsed(sys: &dyn System, start: SystemTime) -> std::time::Duration {
    sys.now().duration_since(start).unwrap_or_default()
}
