//! Go: execute/build/orchestrator.go, and `tscBuildCompilation` of
//! execute/tsc.go:90 (the `tsc -b` entry).
//!
//! The watch part (`Watch`, `updateWatch`, `resetCaches`,
//! `checkTasksForEventChanges`, `computeDesiredWatches`, `DoCycle`) is in
//! orchestrator_watch.rs.
//!
//! PORT: concurrency. Go runs `buildOrCleanProject` for the tasks in
//! `order` on up to `numRoutines` goroutines; each goroutine takes the next
//! task in order, waits for its upstream tasks, builds, and then waits for
//! the previous task to report before it reports. Tasks here are
//! `Rc<RefCell<BuildTask>>` on this thread, which makes, emits and releases
//! the program of every task (see build_task.rs). `build_all_tasks` keeps
//! the Go schedule: at most `numRoutines` tasks are taken and not yet
//! reported, and tasks report in `order`. A taken task starts when its
//! upstream tasks are done, and a task that compiles makes its program at
//! once (`build_project_start`) and starts its check on the program's
//! checker threads, so the checkers of the started tasks work at the same
//! time, as the Go goroutines do. Each checker emits when its check ends,
//! and the emit keeps its writes in memory. The started tasks write their
//! outputs one at a time, the first in `order` first
//! (`build_project_finish`). So a task that runs beside others in Go reads
//! the file system before they write their outputs. Every task uses
//! `o.host` and its caches (parsed `.d.ts` and
//! `.json` files, configs, the cached file system, the mtimes), as in Go.
//! Each program is released when its task reports; its checker threads
//! free it in the background.
//!
//! PORT: the task keeps its project statistics (see build_task.rs), and
//! `report_task` adds them to the aggregate `--diagnostics` and
//! `--extendedDiagnostics` statistics.
//!
//! PORT: testing. `opts.testing` is `None` outside tests. A test compiles
//! each started task to the end at once, in build order, so the one test
//! file system and clock see one ordered sequence (see `build_all_tasks`).

use crate::contentmapper;
use crate::execute::build::build_task::*;
use crate::execute::build::command_line::ParsedBuildCommandLine;
use crate::execute::build::config_prefetch::ConfigPrefetch;
use crate::execute::build::host::BuildHost;
use crate::execute::incremental::build_info::{BuildInfo, is_build_info_file_name_default_library};
use crate::execute::incremental::incremental::{new_build_info_reader, parse_build_info};
use crate::execute::tsc::compile::{
    CommandLineResult, ExitStatus, System, Watcher, Writer, new_content_mapper_host, write_str,
};
use crate::execute::tsc::diagnostics::{
    DiagnosticReporter, DiagnosticsReporter, create_builder_status_reporter,
    create_diagnostic_reporter, create_report_error_summary, create_watch_status_reporter,
};
use crate::execute::tsc::statistics::Statistics;
use crate::execute::watchmanager::{WatchManager, new_watch_manager};
use crate::frontend::prelude::*;
use crate::gostd::Context;
// PORT: testing
use crate::execute::tsc::compile::CommandLineTesting;
use std::sync::{Arc, Condvar, Mutex, PoisonError};
use std::time::SystemTime;

// Go: build/orchestrator.go:27 Options
pub struct Options {
    pub sys: Rc<dyn System>,
    pub command: Rc<ParsedBuildCommandLine>,
    // PORT: testing. `None` outside tests.
    pub testing: Option<Rc<dyn CommandLineTesting>>,
}

// Go: build/orchestrator.go:33 orchestratorResult
// PORT: Go `filesToDelete` is nil until a task adds a file, so an empty
// `Vec` is the Go nil.
#[derive(Default)]
struct OrchestratorResult {
    result: CommandLineResult,
    errors: Vec<Diagnostic>,
    statistics: Statistics,
    files_to_delete: Vec<String>,
}

impl OrchestratorResult {
    // Go: build/orchestrator.go:40 (*orchestratorResult).report
    fn report(&mut self, o: &Orchestrator) {
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
        self.statistics.set_total_time(o.opts.sys.since_start());
        self.statistics
            .report_to(&o.opts.sys.writer(), o.opts.testing.clone());
    }
}

// Go: build/orchestrator.go:63 Orchestrator
// PORT: Go `*SyncMap` of tasks is a plain map; tasks are
// `Rc<RefCell<BuildTask>>`. Go `wm *watchmanager.WatchManager` is
// `Rc<RefCell<WatchManager>>`, so the watch loop can run while `DoCycle`
// borrows the orchestrator (see orchestrator_watch.rs).
pub struct Orchestrator {
    pub(crate) opts: Options,
    pub(crate) compare_paths_options: ComparePathsOptions,
    pub(crate) host: Rc<BuildHost>,

    // contentMapperHost transforms content-mapped files; it is created once per build session (when
    // enabled) and shared across all projects so mapper processes are consolidated. It closes itself when
    // the session context is cancelled (see contentmapper.New).
    // PORT: Go nil is `None`.
    pub(crate) content_mapper_host: Option<Rc<dyn contentmapper::Host>>,

    // order generation result
    tasks: FxHashMap<Path, Rc<RefCell<BuildTask>>>,
    pub(crate) order: Vec<String>,
    errors: Vec<Diagnostic>,

    error_summary_reporter: Option<DiagnosticsReporter>,
    pub(crate) watch_status_reporter: Option<DiagnosticReporter>,

    // fswatch event-based watching
    pub(crate) wm: Rc<RefCell<WatchManager>>,

    // PORT: not in Go (perf). The build info files that threads read ahead
    // of the up-to-date checks of this build cycle (`BuildInfoPrefetch`).
    build_info_prefetch: RefCell<Option<BuildInfoPrefetch>>,
    // PORT: not in Go (perf). The check parts that a thread made from the
    // build info that `read_build_info_file` gave last, and its file name.
    status_prefetch: RefCell<Option<(String, StatusPrefetch)>>,
}

impl Orchestrator {
    // Go: build/orchestrator.go:87 (*Orchestrator).relativeFileName
    pub fn relative_file_name(&self, file_name: &str) -> String {
        convert_to_relative_path(file_name, &self.compare_paths_options)
    }

    // Go: build/orchestrator.go:91 (*Orchestrator).toPath
    pub fn to_path(&self, file_name: &str) -> Path {
        to_path(
            file_name,
            &self.compare_paths_options.current_directory,
            self.compare_paths_options.use_case_sensitive_file_names,
        )
    }

    // Go: build/orchestrator.go:95 (*Orchestrator).resolveBuildInfoFileName
    pub fn resolve_build_info_file_name(&self, file_name: &str, build_info_dir: &str) -> String {
        if is_build_info_file_name_default_library(file_name) {
            return combine_paths(
                &CompilerHost::default_library_path(&*self.host),
                &[file_name],
            );
        }
        get_normalized_absolute_path(file_name, build_info_dir)
    }

    // Go: build/orchestrator.go:102 (*Orchestrator).Order
    pub fn order(&self) -> &[String] {
        &self.order
    }

    // Go: build/orchestrator.go:106 (*Orchestrator).Upstream
    pub fn upstream(&self, config_name: &str) -> Vec<String> {
        let path = self.to_path(config_name);
        let task = self.get_task(&path);
        let task = task.borrow();
        task.up_stream
            .iter()
            .map(|t| t.task.borrow().config.clone())
            .collect()
    }

    // Go: build/orchestrator.go:114 (*Orchestrator).Downstream
    pub fn downstream(&self, config_name: &str) -> Vec<String> {
        let path = self.to_path(config_name);
        let task = self.get_task(&path);
        let task = task.borrow();
        task.down_stream
            .iter()
            .map(|t| t.borrow().config.clone())
            .collect()
    }

    // Go: build/orchestrator.go:122 (*Orchestrator).getTask
    pub fn get_task(&self, path: &Path) -> Rc<RefCell<BuildTask>> {
        match self.tasks.get(path) {
            Some(task) => task.clone(),
            None => panic!("No build task found for {}", path.as_str()),
        }
    }

    // Go: build/orchestrator.go:130 (*Orchestrator).createBuildTasks
    // PORT: Go parses the configs in parallel on a work group; here they
    // parse depth first on one thread. The task map and each task's
    // `resolved` are the same, because a path is taken by the first
    // `LoadOrStore` in both. Threads match the file names of the configs
    // ahead of this thread (`start_config_prefetch`).
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
                        if let Some(project) = &existing.borrow().content_mapper_project {
                            let _ = project.close();
                        }
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
                if old_tasks.is_none() {
                    self.start_config_prefetch(&references);
                }
                self.create_build_tasks(old_tasks, &references);
            }
        }
    }

    /// PORT: not in Go (perf). Queues the parses of `references` on the
    /// config threads (config_prefetch.rs), and starts the threads when
    /// there are two references or more. Go parses the configs on a work
    /// group that is parallel unless `--singleThreaded`. Only for the first
    /// graph of a build that is not a watch (a watch parses changed configs
    /// again), and only on the OS file system (not in tests).
    fn start_config_prefetch(&self, references: &[String]) {
        if let Some(prefetch) = &*self.host.config_prefetch.borrow() {
            prefetch.queue(references);
            return;
        }
        let options = &self.opts.command.compiler_options;
        if references.len() < 2
            || options.watch.is_true()
            || options.single_threaded.is_true()
            || self.opts.testing.is_some()
            || !is_wrapped_os_fs(&self.opts.sys.fs())
        {
            return;
        }
        let prefetch = ConfigPrefetch::start(
            (**options).clone(),
            self.host.command_line_raw(),
            &self.compare_paths_options,
        );
        if let Some(prefetch) = &prefetch {
            prefetch.queue(references);
        }
        *self.host.config_prefetch.borrow_mut() = prefetch;
    }

    // Go: build/orchestrator.go:166 (*Orchestrator).setupBuildTask
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

    // Go: build/orchestrator.go:212 (*Orchestrator).GenerateGraphReusingOldTasks
    pub fn generate_graph_reusing_old_tasks(&mut self) {
        let tasks = std::mem::take(&mut self.tasks);
        self.order = Vec::new();
        self.errors = Vec::new();
        self.generate_graph(Some(&tasks));
    }

    // Go: build/orchestrator.go:220 (*Orchestrator).GenerateGraph
    pub fn generate_graph(&mut self, old_tasks: Option<&FxHashMap<Path, Rc<RefCell<BuildTask>>>>) {
        let projects = self.opts.command.resolved_project_paths().to_vec();
        // Parse all config files in parallel
        self.create_build_tasks(old_tasks, &projects);
        // The config threads stop after the config they parse.
        self.host.config_prefetch.borrow_mut().take();

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
        if let Some(old_tasks) = old_tasks {
            for (path, old_task) in old_tasks {
                if self
                    .tasks
                    .get(path)
                    .is_some_and(|task| Rc::ptr_eq(task, old_task))
                {
                    continue;
                }
                if let Some(project) = &old_task.borrow().content_mapper_project {
                    let _ = project.close();
                }
            }
        }
    }

    // Go: build/orchestrator.go:247 (*Orchestrator).Start
    // PORT: Go returns the orchestrator itself as `result.Watcher`, so this
    // takes the boxed orchestrator. `Watch` blocks in the watch loop until
    // `ctx` ends (orchestrator_watch.rs).
    // PORT: Go `defer o.contentMapperHost.Close()` runs when `start`
    // returns; `start` has one return, so the close is written before it.
    pub fn start(mut self: Box<Self>, ctx: &Context) -> CommandLineResult {
        self.content_mapper_host =
            new_content_mapper_host(ctx, &self.opts.sys, &self.opts.command.compiler_options);
        let close_content_mapper_host = self.content_mapper_host.clone().filter(|_| {
            !self.opts.command.compiler_options.watch.is_true() || self.opts.testing.is_none()
        });
        if self.opts.command.compiler_options.watch.is_true() {
            (self
                .watch_status_reporter
                .as_ref()
                .expect("watch status reporter"))(&new_compiler_diagnostic(
                diag::Starting_compilation_in_watch_mode,
                args![],
            ));
        }
        self.generate_graph(None);
        let mut result = self.build_or_clean();
        if self.opts.command.compiler_options.watch.is_true() {
            self.watch(ctx);
            result.watcher = Some(self as Box<dyn Watcher>);
        }
        if let Some(host) = close_content_mapper_host {
            let _ = host.close();
        }
        result
    }

    // Go: build/orchestrator.go:660 (*Orchestrator).buildOrClean
    pub(crate) fn build_or_clean(&mut self) -> CommandLineResult {
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
            build_result.statistics.projects = self.order().len() as i32;
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

    // Go: build/orchestrator.go:688 (*Orchestrator).numRoutines part of rangeTask
    pub(crate) fn num_routines(&self) -> i32 {
        let mut num_routines = 4;
        if self.opts.command.compiler_options.single_threaded.is_true() {
            num_routines = 1;
        } else if let Some(builders) = self.opts.command.build_options.builders {
            num_routines = builders;
        }
        num_routines
    }

    // Go: build/orchestrator.go:688 (*Orchestrator).rangeTask with
    // build/orchestrator.go:724 (*Orchestrator).buildOrCleanProject and the
    // build/buildtask.go:120 report wait.
    // PORT: see the top comment for the schedule. Go `numRoutines <= 0`
    // starts no goroutine, so no task runs; that is kept.
    fn build_all_tasks(&self, build_result: &mut OrchestratorResult) {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum State {
            NotTaken,
            Waiting,
            Compiling,
            Done,
        }
        let num_routines = self.num_routines();
        if num_routines <= 0 {
            return;
        }
        let num_routines = num_routines as usize;
        let clean = self.opts.command.build_options.clean.is_true();
        // PORT: testing (see the top comment)
        let testing = self.opts.testing.is_some();
        let paths: Vec<Path> = self.order.iter().map(|c| self.to_path(c)).collect();
        if !clean {
            *self.build_info_prefetch.borrow_mut() = self.start_build_info_prefetch(&paths);
        }
        let index_of: FxHashMap<Path, usize> = paths
            .iter()
            .enumerate()
            .map(|(i, p)| (p.clone(), i))
            .collect();
        let mut states = vec![State::NotTaken; paths.len()];
        let mut next_task = 0;
        let mut next_report = 0;
        while next_report < paths.len() {
            // Each free goroutine takes the next task in order.
            while next_task - next_report < num_routines && next_task < paths.len() {
                states[next_task] = State::Waiting;
                next_task += 1;
            }
            // A taken task starts once its upstream tasks are done
            // (Go `waitOnUpstream`; `cleanProject` does not wait). A task
            // that compiles makes its program now.
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
                let mut task = task.borrow_mut();
                task.result = Some(TaskResult::new(
                    self.create_task_builder_status_reporter(),
                    self.create_task_diagnostic_reporter(),
                ));
                states[index] = if clean {
                    task.clean_project(self, &paths[index]);
                    State::Done
                } else if !task.build_project_start(self, &paths[index]) {
                    State::Done
                } else if testing {
                    task.build_project_finish(self, &paths[index]);
                    State::Done
                } else {
                    State::Compiling
                };
            }
            // Tasks report in order.
            let mut reported = false;
            while next_report < next_task && states[next_report] == State::Done {
                let task = self.get_task(&paths[next_report]);
                self.report_task(&mut task.borrow_mut(), build_result);
                next_report += 1;
                reported = true;
            }
            if reported {
                continue;
            }
            // The first task that has not reported has its upstream tasks
            // reported, so it has started. It is not done, so it compiles.
            // It emits now, before the other started tasks.
            assert!(
                states[next_report] == State::Compiling,
                "the first unreported build task has not started"
            );
            let task = self.get_task(&paths[next_report]);
            task.borrow_mut()
                .build_project_finish(self, &paths[next_report]);
            states[next_report] = State::Done;
        }
        // A task that did not read its build info leaves its read unused.
        self.build_info_prefetch.borrow_mut().take();
        self.status_prefetch.borrow_mut().take();
        self.host.m_time_prefetch.borrow_mut().take();
    }

    /// PORT: not in Go (perf). Starts reading the build info files that the
    /// up-to-date checks of the tasks at `paths` will read (see
    /// `BuildInfoPrefetch`), on up to `num_routines` threads. None when
    /// there is nothing to gain or the read could differ from the task's
    /// own read: one routine (`--singleThreaded` or `--builders 1`: Go
    /// checks one task at a time), `--force` (no check reads the build
    /// info), a file system other than the OS one (tests), or fewer than
    /// two files. A solution (Go `upToDateStatusTypeSolution`) and a task
    /// that keeps the build info of an earlier cycle (watch) read nothing.
    /// A build info file that two tasks name (by path) is left out, so no
    /// task of the build writes a prefetched file before its task reads it.
    /// The threads also make the check parts of each build info
    /// (`StatusPrefetch`) and read the mtimes of its task's TypeScript
    /// sources (`BuildHost::m_time_prefetch`).
    fn start_build_info_prefetch(&self, paths: &[Path]) -> Option<BuildInfoPrefetch> {
        let num_routines = usize::try_from(self.num_routines()).unwrap_or(0);
        if num_routines < 2
            || self.opts.command.build_options.force.is_true()
            || !is_wrapped_os_fs(&self.opts.sys.fs())
        {
            return None;
        }
        let mut named: FxHashMap<Path, usize> = FxHashMap::default();
        let mut reads: Vec<(Path, BuildInfoRead)> = Vec::new();
        for path in paths {
            let task = self.get_task(path);
            let task = task.borrow();
            let Some(resolved) = &task.resolved else {
                continue;
            };
            let name = resolved.get_build_info_file_name();
            if name.is_empty() {
                continue;
            }
            let build_info_path = self.to_path(&name);
            *named.entry(build_info_path.clone()).or_default() += 1;
            let solution = resolved.file_names().is_empty() && resolved.has_project_references();
            let keeps = task
                .build_info_entry
                .as_ref()
                .is_some_and(|entry| entry.path == build_info_path);
            if !solution && !keeps {
                reads.push((
                    build_info_path,
                    BuildInfoRead {
                        name,
                        input_files: resolved.file_names().to_vec(),
                    },
                ));
            }
        }
        let reads: Vec<BuildInfoRead> = reads
            .into_iter()
            .filter_map(|(path, read)| (named[&path] == 1).then_some(read))
            .collect();
        if reads.len() < 2 {
            return None;
        }
        let m_times: MTimePrefetch = Arc::default();
        let prefetch = BuildInfoPrefetch::start(
            reads,
            num_routines,
            self.compare_paths_options.clone(),
            m_times.clone(),
        )?;
        *self.host.m_time_prefetch.borrow_mut() = Some(m_times);
        Some(prefetch)
    }

    // Go: build/buildtask.go:120 (*BuildTask).report, the orchestrator part
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
        if let Some(statistics) = &result.statistics {
            build_result.statistics.aggregate(statistics);
        }
        // If we built the program, or updated timestamps, or had errors, we need to
        // delete files that are no longer needed
        match result.build_kind {
            BuildKind::Program => {
                // PORT: testing. The program is current for the call, as
                // the test reads its files.
                if let (Some(testing), Some(program)) = (&self.opts.testing, &result.program) {
                    let _scope = crate::core::enter_program(Some(program.get_program()));
                    testing.on_program(program);
                }
                build_result.statistics.projects_built += 1
            }
            BuildKind::Pseudo => build_result.statistics.timestamp_updates += 1,
            BuildKind::None => {}
        }
        build_result.files_to_delete.extend(result.files_to_delete);
        // Go drops `t.result` here (`t.result = nil`).
        if let Some(program) = result.program {
            release_task_program(program);
        }
    }

    // Go: build/orchestrator.go:736 (*Orchestrator).getWriter with a nil task
    fn writer(&self) -> Writer {
        self.opts.sys.writer()
    }

    // Go: build/orchestrator.go:743 (*Orchestrator).createBuilderStatusReporter(nil)
    fn create_builder_status_reporter(&self) -> DiagnosticReporter {
        create_builder_status_reporter(
            self.opts.sys.clone(),
            self.writer(),
            &self.opts.command.locale(),
            &self.opts.command.compiler_options,
            self.opts.testing.clone(),
        )
    }

    // Go: build/orchestrator.go:747 (*Orchestrator).createDiagnosticReporter(nil)
    fn create_diagnostic_reporter(&self) -> DiagnosticReporter {
        create_diagnostic_reporter(
            &*self.opts.sys,
            self.writer(),
            &self.opts.command.locale(),
            &self.opts.command.compiler_options,
        )
    }

    // Go: build/orchestrator.go:743 (*Orchestrator).createBuilderStatusReporter(task)
    fn create_task_builder_status_reporter(&self) -> TaskDiagnosticReporter {
        task_reporter(|w| {
            create_builder_status_reporter(
                self.opts.sys.clone(),
                w,
                &self.opts.command.locale(),
                &self.opts.command.compiler_options,
                self.opts.testing.clone(),
            )
        })
    }

    // Go: build/orchestrator.go:747 (*Orchestrator).createDiagnosticReporter(task)
    fn create_task_diagnostic_reporter(&self) -> TaskDiagnosticReporter {
        task_reporter(|w| {
            create_diagnostic_reporter(
                &*self.opts.sys,
                w,
                &self.opts.command.locale(),
                &self.opts.command.compiler_options,
            )
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
        let name = config.get_build_info_file_name();
        let prefetched = self
            .build_info_prefetch
            .borrow_mut()
            .as_mut()
            .and_then(|prefetch| prefetch.take(&name));
        if let Some((build_info, status_prefetch)) = prefetched {
            *self.status_prefetch.borrow_mut() = status_prefetch.map(|status| (name, status));
            return build_info.map(Rc::new);
        }
        new_build_info_reader(self.host.clone() as Rc<dyn CompilerHost>)
            .read_build_info(config)
            .map(Rc::new)
    }

    fn take_status_prefetch(&self, build_info_file_name: &str) -> Option<StatusPrefetch> {
        let (name, status_prefetch) = self.status_prefetch.borrow_mut().take()?;
        (name == build_info_file_name).then_some(status_prefetch)
    }

    fn sys(&self) -> Rc<dyn System> {
        self.opts.sys.clone()
    }

    fn host(&self) -> Rc<BuildHost> {
        self.host.clone()
    }

    // PORT: testing
    fn testing(&self) -> Option<Rc<dyn CommandLineTesting>> {
        self.opts.testing.clone()
    }

    fn content_mapper_host(&self) -> Option<Rc<dyn contentmapper::Host>> {
        self.content_mapper_host.clone()
    }
}

/// PORT: not in Go (perf). Go checks whether up to `numRoutines` projects
/// are up to date at the same time, each on its goroutine, and each reads
/// and unmarshals its build info file there (`loadOrStoreBuildInfo`). The
/// orchestrator here checks one task at a time, so threads read and parse
/// the build info files first, in build order, and a task takes the parse
/// of its file (`take`), waiting for it when a thread has not finished
/// it. A thread reads with the OS file system of its thread, as the host
/// does (`ReadBuildInfo`: read the file, then `parse_build_info`).
///
/// After the parse, the thread does the other parts of the check that need
/// no task state: the root info reader and the paths of the file names
/// (`StatusPrefetch`), and the mtimes of the task's TypeScript sources
/// that are not declaration files, the root files and the files of the
/// build info (`MTimePrefetch`). No task of a build writes such a file, so
/// the mtime is the one that the check would read later.
struct BuildInfoPrefetch {
    slots: FxHashMap<String, Arc<BuildInfoSlot>>,
}

/// One build info file that the threads read, and the root files of its
/// task (`resolved.FileNames()`).
struct BuildInfoRead {
    name: String,
    input_files: Vec<String>,
}

/// The mtimes that the build info threads read ahead of the checks, by
/// path. `BuildHost::load_or_store_m_time` takes an mtime from here where it
/// would read it from the file system.
pub(crate) type MTimePrefetch = Arc<Mutex<FxHashMap<Path, Option<SystemTime>>>>;

/// What a thread made for one build info file: Go `ReadBuildInfo`'s result
/// (`None` when the file cannot be read or parsed) and the check parts of
/// a parsed build info.
type BuildInfoResult = (Option<BuildInfo>, Option<StatusPrefetch>);

/// The result for one file: `None` until a thread has read it, then
/// `Some(None)` when the thread panicked, else `Some(Some(result))`.
#[derive(Default)]
struct BuildInfoSlot {
    result: Mutex<Option<Option<BuildInfoResult>>>,
    done: Condvar,
}

/// True for a TypeScript file that is not a declaration file. A build
/// never writes one (its outputs are JavaScript, declaration, map, JSON
/// and build info files).
fn is_typescript_source(file_name: &str) -> bool {
    file_extension_is_one_of(
        file_name,
        &[EXTENSION_TS, EXTENSION_TSX, EXTENSION_MTS, EXTENSION_CTS],
    ) && !is_declaration_file_name(file_name)
}

/// The most threads that read build info files.
const MAX_BUILD_INFO_THREADS: usize = 8;

impl BuildInfoPrefetch {
    /// Starts the threads that read and parse the files of `reads`, in
    /// order, at most `num_routines` (Go `numRoutines`), and put the
    /// mtimes they read into `m_times`. None when no thread starts.
    fn start(
        reads: Vec<BuildInfoRead>,
        num_routines: usize,
        compare_paths_options: ComparePathsOptions,
        m_times: MTimePrefetch,
    ) -> Option<Self> {
        let slots: Vec<(String, Arc<BuildInfoSlot>)> = reads
            .iter()
            .map(|read| (read.name.clone(), Arc::default()))
            .collect();
        let queue = Arc::new(Mutex::new(
            reads
                .into_iter()
                .zip(slots.iter().map(|(_, slot)| slot.clone()))
                .collect::<Vec<_>>()
                .into_iter(),
        ));
        let compare_paths_options = Arc::new(compare_paths_options);
        let threads = MAX_BUILD_INFO_THREADS
            .min(num_routines)
            .min(crate::program::available_cores())
            .min(slots.len());
        let mut started = 0;
        for _ in 0..threads {
            let queue = queue.clone();
            let compare_paths_options = compare_paths_options.clone();
            let m_times = m_times.clone();
            // A thread that cannot start leaves its files to the others.
            let spawned = std::thread::Builder::new()
                .name("goport-buildinfo".to_string())
                .spawn(move || {
                    let fs = crate::frontend::bundled::wrap_fs(crate::frontend::vfs::osvfs_fs());
                    loop {
                        let next = queue.lock().unwrap_or_else(PoisonError::into_inner).next();
                        let Some((read, slot)) = next else {
                            break;
                        };
                        // A read that panics is left to the task, which
                        // panics on it too.
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            let (data, ok) = fs.read_file(&read.name);
                            let build_info = if ok { parse_build_info(&data) } else { None };
                            let status = build_info.as_ref().map(|build_info| {
                                let status = StatusPrefetch::new(
                                    build_info,
                                    &read.name,
                                    &read.input_files,
                                    &compare_paths_options,
                                );
                                prefetch_m_times(&*fs, &read, &status, &m_times);
                                status
                            });
                            (build_info, status)
                        }));
                        *slot.result.lock().unwrap_or_else(PoisonError::into_inner) =
                            Some(result.ok());
                        slot.done.notify_all();
                    }
                });
            started += usize::from(spawned.is_ok());
        }
        (started > 0).then(|| BuildInfoPrefetch {
            slots: slots.into_iter().collect(),
        })
    }

    /// The build info of `name` that a thread read, and its check parts,
    /// once: `None` when it is not prefetched, was taken, or its read
    /// panicked; then the caller reads it. Waits for the thread that reads
    /// it.
    fn take(&mut self, name: &str) -> Option<BuildInfoResult> {
        let slot = self.slots.remove(name)?;
        let mut result = slot.result.lock().unwrap_or_else(PoisonError::into_inner);
        loop {
            if let Some(read) = result.take() {
                return read;
            }
            result = slot
                .done
                .wait(result)
                .unwrap_or_else(PoisonError::into_inner);
        }
    }
}

/// Reads the mtimes of the TypeScript sources (`is_typescript_source`) of
/// `read` (its root files and the files of its build info, `status`) into
/// `m_times`, as `BuildHost::get_m_time` reads them (`incremental.GetMTime`).
fn prefetch_m_times(
    fs: &dyn Fs,
    read: &BuildInfoRead,
    status: &StatusPrefetch,
    m_times: &MTimePrefetch,
) {
    let roots = read.input_files.iter().zip(&status.input_paths);
    let files = status.file_names.iter().map(|(file, path)| (file, path));
    let read: Vec<(Path, Option<SystemTime>)> = roots
        .chain(files)
        .filter(|(file, _)| is_typescript_source(file))
        .map(|(file, path)| (path.clone(), fs.stat(file).and_then(|stat| stat.mod_time())))
        .collect();
    let mut m_times = m_times.lock().unwrap_or_else(PoisonError::into_inner);
    for (path, m_time) in read {
        m_times.entry(path).or_insert(m_time);
    }
}

// Go: build/orchestrator.go:751 NewOrchestrator
pub fn new_orchestrator(opts: Options) -> Orchestrator {
    // PORT: Go passes the method value `opts.Sys.FS().DirectoryExists`.
    let fs = opts.sys.fs();
    let wm = new_watch_manager(
        opts.sys.writer(),
        Box::new(move |path: &str| fs.directory_exists(path)),
    );
    // Go: the `comparePathsOptions` field of the `Orchestrator` literal.
    let compare_paths_options = ComparePathsOptions {
        current_directory: opts.sys.get_current_directory(),
        use_case_sensitive_file_names: opts.sys.fs().use_case_sensitive_file_names(),
    };
    let host = Rc::new(BuildHost::new(
        opts.sys.clone(),
        opts.command.clone(),
        compare_paths_options.clone(),
    ));
    let mut orchestrator = Orchestrator {
        opts,
        compare_paths_options,
        host,
        content_mapper_host: None,
        tasks: FxHashMap::default(),
        order: Vec::new(),
        errors: Vec::new(),
        error_summary_reporter: None,
        watch_status_reporter: None,
        wm: Rc::new(RefCell::new(wm)),
        build_info_prefetch: RefCell::new(None),
        status_prefetch: RefCell::new(None),
    };
    if orchestrator.opts.command.compiler_options.watch.is_true() {
        orchestrator.watch_status_reporter = Some(create_watch_status_reporter(
            orchestrator.opts.sys.clone(),
            &orchestrator.opts.command.locale(),
            orchestrator.opts.command.compiler_options.clone(),
            orchestrator.opts.testing.clone(),
        ));
        // Go: if t, ok := opts.Testing.(CommandLineTestingWithWatchBackend); ok { wm.SetBackend(t.WatchBackend()) }
        // PORT: the test backend comes from `watcher::set_test_watch_backend`.
        if let Some(backend) = crate::execute::watcher::test_watch_backend() {
            orchestrator.wm.borrow_mut().set_backend(backend);
        }
    } else {
        orchestrator.error_summary_reporter = Some(create_report_error_summary(
            &*orchestrator.opts.sys,
            &orchestrator.opts.command.locale(),
            Some(&orchestrator.opts.command.compiler_options),
        ));
    }
    orchestrator
}
