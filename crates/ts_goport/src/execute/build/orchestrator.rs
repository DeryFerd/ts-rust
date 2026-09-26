//! Go: execute/build/orchestrator.go, and `tscBuildCompilation` of
//! execute/tsc.go:90 (the `tsc -b` entry).
//!
//! PORT: watch mode is out of scope (plan D3). `Watch`, `updateWatch`,
//! `resetCaches`, `checkTasksForEventChanges`, `computeDesiredWatches` and
//! `DoCycle` are not ported; `Start` calls `unported!` when `--watch` is set.
//!
//! PORT: concurrency. Go runs `buildOrCleanProject` for the tasks in
//! `order` on up to `numRoutines` goroutines; each goroutine takes the next
//! task in order, waits for its upstream tasks, builds, and then waits for
//! the previous task to report before it reports. Tasks here are
//! `Rc<RefCell<BuildTask>>` on one thread (see build_task.rs), and only the
//! compile runs elsewhere, in a worker process (plan D1). `build_all_tasks`
//! keeps the Go schedule: at most `numRoutines` tasks are taken and not yet
//! reported, a task starts when its upstream tasks are done, workers run in
//! parallel, and tasks report in `order`.
//!
//! PORT: Go shares `o.host`'s cached file system with every task. Each
//! worker gets the orchestrator's cache when it starts, and its additions
//! are merged back when its program is made and when its result arrives
//! (see shared_fs.rs, which also says what stays timing dependent).
//!
//! PORT: the aggregate `--extendedDiagnostics` statistics are not
//! collected (see build_task.rs); `report` calls `unported!` when they are
//! asked for.
//! `opts.Testing` is always nil.

use crate::execute::build::build_task::*;
use crate::execute::build::command_line::{ParsedBuildCommandLine, parse_build_command_line};
use crate::execute::build::host::BuildHost;
use crate::execute::build::worker::{
    SystemParseConfigHost, WorkerLauncher, compare_paths_options_of_sys, marshal_worker_fs_cache,
};
use crate::execute::incremental::build_info::BuildInfo;
use crate::execute::incremental::incremental::new_build_info_reader;
use crate::execute::tsc::compile::{CommandLineResult, ExitStatus, System, Writer, write_str};
use crate::execute::tsc::diagnostics::{
    DiagnosticReporter, DiagnosticsReporter, create_builder_status_reporter,
    create_diagnostic_reporter, create_report_error_summary, create_watch_status_reporter,
};
use crate::frontend::prelude::*;
use std::sync::mpsc;
use std::time::SystemTime;

// Go: build/orchestrator.go:25 Options
// PORT: `Testing` is dropped (always nil). `worker` starts the build
// worker processes (plan D1).
pub struct Options {
    pub sys: Rc<dyn System>,
    pub command: Rc<ParsedBuildCommandLine>,
    pub worker: WorkerLauncher,
}

// Go: build/orchestrator.go:31 orchestratorResult
// PORT: `statistics` is dropped (see top). Go `filesToDelete` is nil until
// a task adds a file, so an empty `Vec` is the Go nil.
#[derive(Default)]
struct OrchestratorResult {
    result: CommandLineResult,
    errors: Vec<Diagnostic>,
    files_to_delete: Vec<String>,
}

impl OrchestratorResult {
    // Go: build/orchestrator.go:38 (*orchestratorResult).report
    fn report(&self, o: &Orchestrator) {
        if o.opts.command.compiler_options.watch.is_true() {
            let message = if self.errors.len() == 1 {
                diag::Found_1_error_Watching_for_file_changes
            } else {
                diag::Found_0_errors_Watching_for_file_changes
            };
            (o.watch_status_reporter
                .as_ref()
                .expect("watch status reporter"))(&new_compiler_diagnostic(
                message,
                args![self.errors.len()],
            ));
        } else {
            (o.error_summary_reporter
                .as_ref()
                .expect("error summary reporter"))(&self.errors);
        }
        if !self.files_to_delete.is_empty() {
            (o.create_builder_status_reporter())(&new_compiler_diagnostic(
                diag::A_non_dry_build_would_delete_the_following_files_Colon_0,
                args![
                    self.files_to_delete
                        .iter()
                        .map(|f| format!("\r\n * {f}"))
                        .collect::<String>()
                ],
            ));
        }
        if !o.opts.command.compiler_options.diagnostics.is_true()
            && !o
                .opts
                .command
                .compiler_options
                .extended_diagnostics
                .is_true()
        {
            return;
        }
        unported!("Statistics.Report");
    }
}

// Go: build/orchestrator.go:61 Orchestrator
// PORT: `wm` (watch manager) is dropped (see top). Go `*SyncMap` of tasks
// is a plain map; tasks are `Rc<RefCell<BuildTask>>`.
pub struct Orchestrator {
    opts: Options,
    compare_paths_options: ComparePathsOptions,
    host: Rc<BuildHost>,

    // order generation result
    tasks: FxHashMap<Path, Rc<RefCell<BuildTask>>>,
    order: Vec<String>,
    errors: Vec<Diagnostic>,

    error_summary_reporter: Option<DiagnosticsReporter>,
    watch_status_reporter: Option<DiagnosticReporter>,
}

impl Orchestrator {
    // Go: build/orchestrator.go:83 (*Orchestrator).relativeFileName
    pub fn relative_file_name(&self, file_name: &str) -> String {
        convert_to_relative_path(file_name, &self.compare_paths_options)
    }

    // Go: build/orchestrator.go:87 (*Orchestrator).toPath
    pub fn to_path(&self, file_name: &str) -> Path {
        to_path(
            file_name,
            &self.compare_paths_options.current_directory,
            self.compare_paths_options.use_case_sensitive_file_names,
        )
    }

    // Go: build/orchestrator.go:91 (*Orchestrator).resolveBuildInfoFileName
    pub fn resolve_build_info_file_name(&self, file_name: &str, build_info_dir: &str) -> String {
        if !file_name.starts_with('.') {
            return combine_paths(
                &CompilerHost::default_library_path(&*self.host),
                &[file_name],
            );
        }
        get_normalized_absolute_path(file_name, build_info_dir)
    }

    // Go: build/orchestrator.go:98 (*Orchestrator).Order
    pub fn order(&self) -> &[String] {
        &self.order
    }

    // Go: build/orchestrator.go:102 (*Orchestrator).Upstream
    pub fn upstream(&self, config_name: &str) -> Vec<String> {
        let path = self.to_path(config_name);
        let task = self.get_task(&path);
        let task = task.borrow();
        task.up_stream
            .iter()
            .map(|t| t.task.borrow().config.clone())
            .collect()
    }

    // Go: build/orchestrator.go:110 (*Orchestrator).Downstream
    pub fn downstream(&self, config_name: &str) -> Vec<String> {
        let path = self.to_path(config_name);
        let task = self.get_task(&path);
        let task = task.borrow();
        task.down_stream
            .iter()
            .map(|t| t.borrow().config.clone())
            .collect()
    }

    // Go: build/orchestrator.go:118 (*Orchestrator).getTask
    pub fn get_task(&self, path: &Path) -> Rc<RefCell<BuildTask>> {
        match self.tasks.get(path) {
            Some(task) => task.clone(),
            None => panic!("No build task found for {}", path.as_str()),
        }
    }

    // Go: build/orchestrator.go:126 (*Orchestrator).createBuildTasks
    // PORT: Go parses the configs in parallel on a work group; here they
    // parse depth first on one thread. The task map and each task's
    // `resolved` are the same, because a path is taken by the first
    // `LoadOrStore` in both.
    fn create_build_tasks(
        &mut self,
        old_tasks: Option<&FxHashMap<Path, Rc<RefCell<BuildTask>>>>,
        configs: &[String],
    ) {
        for config in configs {
            let path = self.to_path(config);
            let mut task: Option<Rc<RefCell<BuildTask>>> = None;
            let mut build_info: Option<BuildInfoEntry> = None;
            if let Some(old_tasks) = old_tasks {
                if let Some(existing) = old_tasks.get(&path) {
                    if !existing.borrow().dirty {
                        // Reuse existing task if config is same
                        task = Some(existing.clone());
                    } else {
                        build_info = existing.borrow().build_info_entry.clone();
                    }
                }
            }
            let task = task.unwrap_or_else(|| {
                let mut task = BuildTask::new(config.clone(), old_tasks.is_none());
                task.build_info_entry = build_info;
                Rc::new(RefCell::new(task))
            });
            if self.tasks.contains_key(&path) {
                continue;
            }
            self.tasks.insert(path.clone(), task.clone());
            let resolved = self.host.get_resolved_project_reference(config, &path);
            {
                let mut task = task.borrow_mut();
                task.resolved = resolved.clone();
                task.up_stream = Vec::new();
            }
            if let Some(resolved) = resolved {
                let references = resolved.resolved_project_reference_paths().to_vec();
                self.create_build_tasks(old_tasks, &references);
            }
        }
    }

    // Go: build/orchestrator.go:158 (*Orchestrator).setupBuildTask
    // PORT: the Go `reportDone`, `prevReporter` and `done` channels are
    // dropped (see top).
    fn setup_build_task(
        &mut self,
        config_name: &str,
        down_stream: Option<&Rc<RefCell<BuildTask>>>,
        in_circular_context: bool,
        completed: &mut FxHashSet<Path>,
        analyzing: &mut FxHashSet<Path>,
        circularity_stack: &mut Vec<String>,
    ) -> Option<Rc<RefCell<BuildTask>>> {
        let path = self.to_path(config_name);
        let task = self.get_task(&path);
        if !completed.contains(&path) {
            if analyzing.contains(&path) {
                if !in_circular_context {
                    self.errors.push(new_compiler_diagnostic(
                        diag::Project_references_may_not_form_a_circular_graph_Cycle_detected_Colon_0,
                        args![circularity_stack.join("\n")],
                    ));
                }
                return None;
            }
            analyzing.insert(path.clone());
            circularity_stack.push(config_name.to_string());
            let resolved = task.borrow().resolved.clone();
            if let Some(resolved) = resolved {
                let references = resolved.resolved_project_reference_paths().to_vec();
                for (index, sub_reference) in references.iter().enumerate() {
                    let upstream = self.setup_build_task(
                        sub_reference,
                        Some(&task),
                        in_circular_context || resolved.project_references()[index].circular,
                        completed,
                        analyzing,
                        circularity_stack,
                    );
                    if let Some(upstream) = upstream {
                        task.borrow_mut().up_stream.push(UpstreamTask {
                            task: upstream,
                            ref_index: index,
                        });
                    }
                }
            }
            circularity_stack.pop();
            completed.insert(path);
            self.order.push(config_name.to_string());
        }
        if self.opts.command.compiler_options.watch.is_true() {
            if let Some(down_stream) = down_stream {
                task.borrow_mut().down_stream.push(down_stream.clone());
            }
        }
        Some(task)
    }

    // Go: build/orchestrator.go:203 (*Orchestrator).GenerateGraphReusingOldTasks
    pub fn generate_graph_reusing_old_tasks(&mut self) {
        let tasks = std::mem::take(&mut self.tasks);
        self.order = Vec::new();
        self.errors = Vec::new();
        self.generate_graph(Some(&tasks));
    }

    // Go: build/orchestrator.go:211 (*Orchestrator).GenerateGraph
    pub fn generate_graph(&mut self, old_tasks: Option<&FxHashMap<Path, Rc<RefCell<BuildTask>>>>) {
        let projects = self.opts.command.resolved_project_paths().to_vec();
        // Parse all config files in parallel
        self.create_build_tasks(old_tasks, &projects);

        // Generate the graph
        let mut completed = FxHashSet::default();
        let mut analyzing = FxHashSet::default();
        let mut circularity_stack = Vec::new();
        for project in &projects {
            self.setup_build_task(
                project,
                None,
                false,
                &mut completed,
                &mut analyzing,
                &mut circularity_stack,
            );
        }
    }

    // Go: build/orchestrator.go:227 (*Orchestrator).Start
    pub fn start(&mut self) -> CommandLineResult {
        if self.opts.command.compiler_options.watch.is_true() {
            unported!("Orchestrator.Watch");
        }
        self.generate_graph(None);
        self.build_or_clean()
    }

    // Go: build/orchestrator.go:517 (*Orchestrator).buildOrClean
    fn build_or_clean(&mut self) -> CommandLineResult {
        if !self.opts.command.build_options.clean.is_true()
            && self.opts.command.build_options.verbose.is_true()
        {
            (self.create_builder_status_reporter())(&new_compiler_diagnostic(
                diag::Projects_in_this_build_Colon_0,
                args![
                    self.order()
                        .iter()
                        .map(|p| format!("\r\n    * {}", self.relative_file_name(p)))
                        .collect::<String>()
                ],
            ));
        }
        let mut build_result = OrchestratorResult::default();
        if self.errors.is_empty() {
            self.build_all_tasks(&mut build_result);
        } else {
            // Circularity errors prevent any project from being built
            build_result.result.status = ExitStatus::ProjectReferenceCycleOutputsSkipped;
            let report_diagnostic = self.create_diagnostic_reporter();
            for err in &self.errors {
                report_diagnostic(err);
            }
            build_result.errors = self.errors.clone();
        }
        build_result.report(self);
        build_result.result
    }

    // Go: build/orchestrator.go:540 (*Orchestrator).numRoutines part of rangeTask
    fn num_routines(&self) -> i32 {
        let mut num_routines = 4;
        if self.opts.command.compiler_options.single_threaded.is_true() {
            num_routines = 1;
        } else if let Some(builders) = self.opts.command.build_options.builders {
            num_routines = builders;
        }
        num_routines
    }

    // Go: build/orchestrator.go:540 (*Orchestrator).rangeTask with
    // build/orchestrator.go:574 (*Orchestrator).buildOrCleanProject and the
    // build/buildtask.go:90 report wait.
    // PORT: see the top comment for the schedule. Go `numRoutines <= 0`
    // starts no goroutine, so no task runs; that is kept.
    fn build_all_tasks(&self, build_result: &mut OrchestratorResult) {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum State {
            NotTaken,
            Waiting,
            Running,
            Done,
        }
        // A running worker sends its program's file system cache entries
        // before its result (see shared_fs.rs).
        enum WorkerMessage {
            ProgramFsCache(CachedFsState),
            Done(WorkerCompileResult),
        }
        let num_routines = self.num_routines();
        if num_routines <= 0 {
            return;
        }
        let num_routines = num_routines as usize;
        let clean = self.opts.command.build_options.clean.is_true();
        let paths: Vec<Path> = self.order.iter().map(|c| self.to_path(c)).collect();
        let index_of: FxHashMap<Path, usize> = paths
            .iter()
            .enumerate()
            .map(|(i, p)| (p.clone(), i))
            .collect();
        let mut states = vec![State::NotTaken; paths.len()];
        let (tx, rx) = mpsc::channel::<(usize, WorkerMessage)>();
        let mut next_task = 0;
        let mut next_report = 0;
        let mut taken = 0;
        while next_report < paths.len() {
            let mut progressed = false;
            // Each free goroutine takes the next task in order.
            while taken < num_routines && next_task < paths.len() {
                states[next_task] = State::Waiting;
                next_task += 1;
                taken += 1;
                progressed = true;
            }
            // A taken task starts once its upstream tasks are done
            // (Go `waitOnUpstream`; `cleanProject` does not wait).
            for index in next_report..next_task {
                if states[index] != State::Waiting {
                    continue;
                }
                let task = self.get_task(&paths[index]);
                if !clean {
                    let upstream_done = task.borrow().up_stream.iter().all(|upstream| {
                        let path = self.to_path(&upstream.task.borrow().config);
                        index_of
                            .get(&path)
                            .is_none_or(|&i| states[i] == State::Done)
                    });
                    if !upstream_done {
                        continue;
                    }
                }
                progressed = true;
                let mut task = task.borrow_mut();
                task.result = Some(TaskResult::new(
                    self.create_task_builder_status_reporter(),
                    self.create_task_diagnostic_reporter(),
                ));
                if clean {
                    task.clean_project(self, &paths[index]);
                    states[index] = State::Done;
                } else if task.build_project_start(self, &paths[index]) {
                    let worker = self.opts.worker.clone();
                    let config = task.config.clone();
                    let fs_cache = marshal_worker_fs_cache(&self.host.cached_fs.state());
                    let tx = tx.clone();
                    std::thread::spawn(move || {
                        let result = worker.run(&config, &fs_cache, &mut |state| {
                            let _ = tx.send((index, WorkerMessage::ProgramFsCache(state)));
                        });
                        let _ = tx.send((index, WorkerMessage::Done(result)));
                    });
                    states[index] = State::Running;
                } else {
                    states[index] = State::Done;
                }
            }
            // Tasks report in order.
            while next_report < next_task && states[next_report] == State::Done {
                let task = self.get_task(&paths[next_report]);
                self.report_task(&mut task.borrow_mut(), build_result);
                next_report += 1;
                taken -= 1;
                progressed = true;
            }
            if !progressed {
                let (index, message) = rx.recv().expect("a build worker is running");
                let result = match message {
                    WorkerMessage::Done(result) => result,
                    WorkerMessage::ProgramFsCache(program_fs_cache) => {
                        self.host.cached_fs.load_state(&program_fs_cache);
                        continue;
                    }
                };
                self.host.cached_fs.load_state(&result.fs_cache);
                let task = self.get_task(&paths[index]);
                task.borrow_mut()
                    .build_project_finish(self, &paths[index], result);
                states[index] = State::Done;
            }
        }
    }

    // Go: build/buildtask.go:90 (*BuildTask).report, the orchestrator part
    // (see `BuildTask::report`).
    fn report_task(&self, task: &mut BuildTask, build_result: &mut OrchestratorResult) {
        let (result, errors) = task.report();
        if !errors.is_empty() {
            build_result.errors.extend(errors);
        }
        write_str(&self.opts.sys.writer(), &result.builder);
        if result.exit_status.code() > build_result.result.status.code() {
            build_result.result.status = result.exit_status;
        }
        // PORT: the `buildKind` statistics counts are dropped (see top).
        build_result.files_to_delete.extend(result.files_to_delete);
    }

    // Go: build/orchestrator.go:584 (*Orchestrator).getWriter with a nil task
    fn writer(&self) -> Writer {
        self.opts.sys.writer()
    }

    // Go: build/orchestrator.go:591 (*Orchestrator).createBuilderStatusReporter(nil)
    fn create_builder_status_reporter(&self) -> DiagnosticReporter {
        create_builder_status_reporter(
            self.opts.sys.clone(),
            self.writer(),
            &self.opts.command.compiler_options,
        )
    }

    // Go: build/orchestrator.go:595 (*Orchestrator).createDiagnosticReporter(nil)
    fn create_diagnostic_reporter(&self) -> DiagnosticReporter {
        create_diagnostic_reporter(
            &*self.opts.sys,
            self.writer(),
            &self.opts.command.compiler_options,
        )
    }

    // Go: build/orchestrator.go:591 (*Orchestrator).createBuilderStatusReporter(task)
    fn create_task_builder_status_reporter(&self) -> TaskDiagnosticReporter {
        task_reporter(|w| {
            create_builder_status_reporter(
                self.opts.sys.clone(),
                w,
                &self.opts.command.compiler_options,
            )
        })
    }

    // Go: build/orchestrator.go:595 (*Orchestrator).createDiagnosticReporter(task)
    fn create_task_diagnostic_reporter(&self) -> TaskDiagnosticReporter {
        task_reporter(|w| {
            create_diagnostic_reporter(&*self.opts.sys, w, &self.opts.command.compiler_options)
        })
    }
}

// PORT: Go `getWriter(task)` gives the reporter `&task.result.builder`. A
// `TaskDiagnosticReporter` gets the builder on each call instead (see
// build_task.rs), so the tsc reporter writes into its own buffer, and the
// buffer moves into the builder after each call.
fn task_reporter(make: impl FnOnce(Writer) -> DiagnosticReporter) -> TaskDiagnosticReporter {
    let buffer: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
    let reporter = make(buffer.clone());
    Box::new(move |builder: &mut String, diagnostic: &Diagnostic| {
        reporter(diagnostic);
        let bytes = std::mem::take(&mut *buffer.borrow_mut());
        builder.push_str(&String::from_utf8_lossy(&bytes));
    })
}

impl BuildTaskOrchestrator for Orchestrator {
    fn command(&self) -> &ParsedBuildCommandLine {
        &self.opts.command
    }

    fn compare_paths_options(&self) -> &ComparePathsOptions {
        &self.compare_paths_options
    }

    fn relative_file_name(&self, file_name: &str) -> String {
        Orchestrator::relative_file_name(self, file_name)
    }

    fn to_path(&self, file_name: &str) -> Path {
        Orchestrator::to_path(self, file_name)
    }

    fn now(&self) -> SystemTime {
        self.opts.sys.now()
    }

    fn fs(&self) -> Rc<dyn Fs> {
        CompilerHost::fs(&*self.host)
    }

    fn get_m_time(&self, file: &str) -> Option<SystemTime> {
        self.host.get_m_time(file)
    }

    fn set_m_time(&self, file: &str, m_time: SystemTime) -> Result<(), FsError> {
        self.host.set_m_time(file, Some(m_time))
    }

    fn store_m_time(&self, file: &str, m_time: SystemTime) {
        self.host.store_m_time(file, Some(m_time));
    }

    fn read_build_info_file(&self, config: &ParsedCommandLine) -> Option<Rc<BuildInfo>> {
        new_build_info_reader(self.host.clone() as Rc<dyn CompilerHost>)
            .read_build_info(config)
            .map(Rc::new)
    }

    fn compile_and_emit_in_worker(&self, config: &str, _config_path: &Path) -> WorkerCompileResult {
        let fs_cache = marshal_worker_fs_cache(&self.host.cached_fs.state());
        let result = self.opts.worker.run(config, &fs_cache, &mut |state| {
            self.host.cached_fs.load_state(&state);
        });
        self.host.cached_fs.load_state(&result.fs_cache);
        result
    }
}

// Go: build/orchestrator.go:603 NewOrchestrator
pub fn new_orchestrator(opts: Options) -> Orchestrator {
    let compare_paths_options = compare_paths_options_of_sys(&*opts.sys);
    let host = Rc::new(BuildHost::new(
        opts.sys.clone(),
        opts.command.clone(),
        compare_paths_options.clone(),
    ));
    let mut orchestrator = Orchestrator {
        opts,
        compare_paths_options,
        host,
        tasks: FxHashMap::default(),
        order: Vec::new(),
        errors: Vec::new(),
        error_summary_reporter: None,
        watch_status_reporter: None,
    };
    if orchestrator.opts.command.compiler_options.watch.is_true() {
        orchestrator.watch_status_reporter = Some(create_watch_status_reporter(
            orchestrator.opts.sys.clone(),
            orchestrator.opts.command.compiler_options.clone(),
        ));
    } else {
        orchestrator.error_summary_reporter = Some(create_report_error_summary(
            &*orchestrator.opts.sys,
            Some(&orchestrator.opts.command.compiler_options),
        ));
    }
    orchestrator
}

// Go: execute/tsc.go:90 tscBuildCompilation
// PORT: the locale is dropped (see command_line.rs), the pprof session is
// not ported, and `--help` output is out of scope (plan D3).
// `command_line_args` is the full command line (Go `commandLineArgs`); the
// build workers get the same arguments.
pub fn tsc_build_compilation(
    sys: Rc<dyn System>,
    command_line_args: &[String],
) -> CommandLineResult {
    let build_command = parse_build_command_line(command_line_args, &SystemParseConfigHost(&*sys));
    let report_diagnostic =
        create_diagnostic_reporter(&*sys, sys.writer(), &build_command.compiler_options);

    if !build_command.errors.is_empty() {
        for err in &build_command.errors {
            report_diagnostic(err);
        }
        return CommandLineResult {
            status: ExitStatus::DiagnosticsPresentOutputsSkipped,
            watcher: None,
        };
    }

    if !build_command.compiler_options.pprof_dir.is_empty() {
        unported!("pprof.BeginProfiling");
    }

    if build_command.compiler_options.help.is_true() {
        unported!("PrintBuildHelp");
    }

    let mut orchestrator = new_orchestrator(Options {
        sys,
        command: Rc::new(build_command),
        worker: WorkerLauncher::current(command_line_args.to_vec()),
    });
    orchestrator.start()
}
