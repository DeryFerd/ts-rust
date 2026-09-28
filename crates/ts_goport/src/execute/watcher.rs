//! Go: execute/watcher.go (package `execute`): `tsc --watch` without
//! `--build`.
//!
//! PORT: testing. Go `testing tsc.CommandLineTesting` is `None` outside
//! tests (see tsc/compile.rs). The test watch backend comes from
//! `set_test_watch_backend`, not from `testing`.
//!
//! PORT: Go runs `DoCycle` from `WatchManager.RunLoop` on the goroutine
//! that called `start`. The port does the same on the calling thread. The
//! watch manager is `Rc<RefCell<WatchManager>>`: the loop keeps a shared
//! borrow while `do_cycle` borrows the watcher mutably, and `do_cycle` only
//! takes shared borrows of the manager.
//!
//! PORT: Go makes a new program on every build. Each build here makes a
//! program version (`execute_tsc::new_program_version`) and runs with it
//! current (`core::enter_program`). Files that the source file cache keeps
//! are shared with the last version. The last version is released when the
//! next build has read it (Go drops the old program there).

use crate::execute::build::host::TscExtendedConfigCache;
use crate::execute::execute_tsc::{get_trace_from_sys, new_program_version, os_write_file};
use crate::execute::incremental;
use crate::execute::tsc::compile::{
    CommandLineTesting, CompileAndEmitResult, CompileTimes, System, SystemParseConfigHost,
    write_str,
};
use crate::execute::tsc::diagnostics::{
    DiagnosticReporter, DiagnosticsReporter, create_watch_status_reporter,
};
use crate::execute::tsc::emit::{EmitInput, emit_files_and_report_errors};
use crate::execute::watchmanager::{
    WatchBackend, WatchManager, can_watch_directory, is_dir_covered_by_watch, new_watch_manager,
};
use crate::frontend::prelude::*;
use crate::frontend::vfs::trackingvfs;
use crate::fswatch;
use crate::gostd::{Context, GoError};
use std::time::SystemTime;

// Go: execute/watcher.go:24 cachedSourceFile
// PORT: Go `time.Time` is `Option<SystemTime>` (`None` = zero), as in
// `vfs::FileInfo`.
pub struct CachedSourceFile {
    pub file: Rc<ParsedSourceFile>,
    pub mod_time: Option<SystemTime>,
}

// Go: execute/watcher.go:29 watchCompilerHost
// PORT: the embedded Go `compiler.CompilerHost` is the `compiler_host`
// field; the trait impl below forwards to it. Go `*collections.SyncMap`
// shared with the watcher is `Rc<RefCell<FxHashMap>>` (one thread).
pub struct WatchCompilerHost {
    pub compiler_host: Rc<dyn CompilerHost>,
    pub cache: Rc<RefCell<FxHashMap<Path, Rc<CachedSourceFile>>>>,
}

impl CompilerHost for WatchCompilerHost {
    fn fs(&self) -> Rc<dyn Fs> {
        self.compiler_host.fs()
    }

    fn default_library_path(&self) -> String {
        self.compiler_host.default_library_path()
    }

    fn get_current_directory(&self) -> String {
        self.compiler_host.get_current_directory()
    }

    fn trace(&self, msg: &'static Message, args: Vec<String>) {
        self.compiler_host.trace(msg, args);
    }

    // Go: execute/watcher.go:34 (*watchCompilerHost).GetSourceFile
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<Rc<ParsedSourceFile>> {
        let info = self.compiler_host.fs().stat(&opts.file_name);

        let cached = self.cache.borrow().get(&opts.path).cloned();
        if let Some(cached) = cached {
            if let Some(info) = &info {
                if info.mod_time() == cached.mod_time {
                    return Some(cached.file.clone());
                }
            }
        }

        let file = self.compiler_host.get_source_file(opts);
        if let Some(file) = &file {
            if let Some(info) = &info {
                self.cache.borrow_mut().insert(
                    opts.path.clone(),
                    Rc::new(CachedSourceFile {
                        file: file.clone(),
                        mod_time: info.mod_time(),
                    }),
                );
            }
        } else {
            self.cache.borrow_mut().remove(&opts.path);
        }
        file
    }

    fn get_resolved_project_reference(
        &self,
        file_name: &str,
        path: &Path,
    ) -> Option<Rc<ParsedCommandLine>> {
        self.compiler_host
            .get_resolved_project_reference(file_name, path)
    }

    // PORT: not in Go (see `CompilerHost::prefetch_parses`). A rebuild
    // gets the files that did not change from `cache`, so parse workers
    // would parse them again for nothing, and those parses stay in the
    // workers' AST arenas (about 38 MiB for each query-core rebuild). The
    // first build, and a build after an overflow or a config change (both
    // empty the cache), still parse ahead.
    fn prefetch_parses(&self) -> bool {
        self.cache.borrow().is_empty() && self.compiler_host.prefetch_parses()
    }
}

// Go: execute/watcher.go:57 Watcher
// PORT: Go `*tsoptions.ParsedCommandLine` is `Rc<ParsedCommandLine>`. Go
// `*collections.OrderedMap[string, any]` is
// `Option<IndexMap<String, CompilerOptionsValue>>` (as in build/host.rs).
// Go `*incremental.Program` and `*tsc.ExtendedConfigCache` are `Option`s
// (nil before `start`). Go `*collections.Set` of seen files is a plain
// set (empty before the first build, which Go's nil set reads as). Go
// `time.Time` is `Option<SystemTime>`.
pub struct Watcher {
    sys: Rc<dyn System>,
    config_file_name: String,
    config: Rc<ParsedCommandLine>,
    compiler_options_from_command_line: Rc<CompilerOptions>,
    command_line_raw: Option<IndexMap<String, CompilerOptionsValue>>,
    report_diagnostic: DiagnosticReporter,
    report_error_summary: DiagnosticsReporter,
    report_watch_status: DiagnosticReporter,
    testing: Option<Rc<dyn CommandLineTesting>>,

    program: Option<incremental::program::Program>,
    extended_config_cache: Option<Rc<TscExtendedConfigCache>>,
    config_modified: bool,
    config_has_errors: bool,
    config_file_paths: Vec<String>,

    source_file_cache: Rc<RefCell<FxHashMap<Path, Rc<CachedSourceFile>>>>,

    wm: Rc<RefCell<WatchManager>>,
    seen_files: FxHashSet<Path>, // all build dependencies (for event filtering)
    config_mtimes: FxHashMap<String, Option<SystemTime>>,
}

// Go: execute/watcher.go:81 `var _ tsc.Watcher = (*Watcher)(nil)`
impl crate::execute::tsc::Watcher for Watcher {
    fn do_cycle(&mut self) {
        Watcher::do_cycle(self);
    }
}

thread_local! {
    /// The watch backend of `set_test_watch_backend`.
    static TEST_WATCH_BACKEND: RefCell<Option<Rc<dyn WatchBackend>>> = const { RefCell::new(None) };
}

/// Go `tsc.CommandLineTesting` with `WatchBackend()`
/// (watchmanager.CommandLineTestingWithWatchBackend): a watcher that this
/// thread makes later uses `backend` in place of the OS file watcher.
// PORT: a test harness sets the backend here, not through `testing`. With
// `testing` set too, the watcher is in Go's test mode: `start` returns
// after the first build and the test calls `DoCycle`. Without it (the
// `goport_watch` bin), the watcher still runs its own loop.
pub fn set_test_watch_backend(backend: Rc<dyn WatchBackend>) {
    TEST_WATCH_BACKEND.with(|slot| *slot.borrow_mut() = Some(backend));
}

/// The backend of `set_test_watch_backend` (also for `tsc -b --watch`).
pub(crate) fn test_watch_backend() -> Option<Rc<dyn WatchBackend>> {
    TEST_WATCH_BACKEND.with(|slot| slot.borrow().clone())
}

// Go: execute/watcher.go:83 createWatcher
pub fn create_watcher(
    sys: Rc<dyn System>,
    config_parse_result: Rc<ParsedCommandLine>,
    compiler_options_from_command_line: Rc<CompilerOptions>,
    command_line_raw: Option<IndexMap<String, CompilerOptionsValue>>,
    report_diagnostic: DiagnosticReporter,
    report_error_summary: DiagnosticsReporter,
    testing: Option<Rc<dyn CommandLineTesting>>,
) -> Watcher {
    // PORT: Go passes the method value `sys.FS().DirectoryExists`.
    let fs = sys.fs();
    let mut wm = new_watch_manager(
        sys.writer(),
        Box::new(move |path: &str| fs.directory_exists(path)),
    );
    // Go: if t, ok := testing.(CommandLineTestingWithWatchBackend); ok { wm.SetBackend(t.WatchBackend()) }
    if let Some(backend) = test_watch_backend() {
        wm.set_backend(backend);
    }
    let mut w = Watcher {
        sys: sys.clone(),
        config_file_name: String::new(),
        config: config_parse_result.clone(),
        compiler_options_from_command_line,
        command_line_raw,
        report_diagnostic,
        report_error_summary,
        report_watch_status: create_watch_status_reporter(
            sys,
            &config_parse_result.locale(),
            config_parse_result.compiler_options().clone(),
            testing.clone(),
        ),
        testing,
        program: None,
        extended_config_cache: None,
        config_modified: false,
        config_has_errors: false,
        config_file_paths: Vec::new(),
        source_file_cache: Rc::new(RefCell::new(FxHashMap::default())),
        wm: Rc::new(RefCell::new(wm)),
        seen_files: FxHashSet::default(),
        config_mtimes: FxHashMap::default(),
    };
    if let Some(config_file) = &config_parse_result.config_file {
        w.config_file_name = source_file_file_name(config_file.source_file).to_string();
    }
    w
}

impl Watcher {
    // Go: execute/watcher.go:114 (*Watcher).start
    pub fn start(&mut self, ctx: &Context) {
        self.wm.borrow().lock();
        let extended_config_cache = Rc::new(TscExtendedConfigCache::default());
        self.extended_config_cache = Some(extended_config_cache.clone());
        let host = new_compiler_host(
            &self.sys.get_current_directory(),
            self.sys.fs(),
            &self.sys.default_library_path(),
            Some(extended_config_cache as Rc<dyn ExtendedConfigCache>),
            Some(get_trace_from_sys(
                &*self.sys,
                self.config.locale(),
                self.testing.clone(),
            )),
        );
        self.program = incremental::program::read_build_info_program(
            &self.config,
            &*incremental::incremental::new_build_info_reader(host.clone()),
            &*host,
        );

        if !self.config_file_name.is_empty() {
            let mut config_file_paths = vec![self.config_file_name.clone()];
            config_file_paths.extend(self.config.extended_source_files().iter().cloned());
            self.config_file_paths = config_file_paths;
        }

        if !self
            .sys
            .get_environment_variable("TS_WATCH_DEBUG")
            .is_empty()
        {
            self.wm.borrow_mut().debug_log = Some(self.sys.writer());
        }

        if self.testing.is_none() {
            self.wm.borrow_mut().ensure_default_backend();
        }

        (self.report_watch_status)(&new_compiler_diagnostic(
            diag::Starting_compilation_in_watch_mode,
            args![],
        ));
        if self.do_build().is_err() {
            self.wm.borrow().force_overflow();
        }
        self.wm.borrow().unlock();

        if self.testing.is_none() {
            // PORT: Go passes the method value `w.DoCycle`.
            let wm = Rc::clone(&self.wm);
            wm.borrow().run_loop(ctx, &mut || self.do_cycle());
        }
    }

    // Go: execute/watcher.go:143 (*Watcher).computeDesiredWatches
    // PORT: Go ranges over `WildcardDirectories()` (a map, random order).
    pub fn compute_desired_watches(&self, seen_file_paths: &[String]) -> FxHashMap<String, bool> {
        let cwd = self.sys.get_current_directory();

        let mut desired_dirs: FxHashMap<String, bool> = FxHashMap::default(); // dir → recursive

        // Wildcard directories from tsconfig (recursive or non-recursive)
        if self.config.config_file.is_some() {
            for (dir, recursive) in self.config.wildcard_directories() {
                let real_dir = self.sys.fs().realpath(dir);
                desired_dirs.insert(real_dir, *recursive);
            }
        }

        // For no-config CLI mode, ensure CWD is watched
        if self.config.config_file.is_none() && desired_dirs.is_empty() {
            let dir = self.sys.fs().realpath(&cwd);
            desired_dirs.insert(dir, false);
        }

        // Config file parent directories as non-recursive watches
        for cfg_path in &self.config_file_paths {
            let real_path = self.sys.fs().realpath(cfg_path);
            let dir = get_directory_path(&real_path);
            if !desired_dirs.contains_key(&dir) {
                desired_dirs.insert(dir, false);
            }
        }

        // For no-config CLI mode, also watch the CLI-specified files' directories
        if self.config.config_file.is_none() {
            for file_name in self.config.file_names() {
                let abs_path = get_normalized_absolute_path(file_name, &cwd);
                let real_path = self.sys.fs().realpath(&abs_path);
                let dir = get_directory_path(&real_path);
                if !desired_dirs.contains_key(&dir) {
                    desired_dirs.insert(dir, false);
                }
            }
        }

        // Add parent directories for seen files not covered by existing dir watches.
        // Resolve ancestor fallbacks first so coverage checks use final dirs.
        let mut resolved_dirs = self.wm.borrow().resolve_desired_dirs(&desired_dirs);

        let opts = self.compare_paths_options();
        for file_path in seen_file_paths {
            let dir = get_directory_path(file_path);
            if !is_dir_covered_by_watch(&resolved_dirs, &dir, &opts) && can_watch_directory(&dir) {
                resolved_dirs.insert(dir, false);
            }
        }

        // Re-resolve in case newly added dirs don't exist
        self.wm.borrow().resolve_desired_dirs(&resolved_dirs)
    }

    // Go: execute/watcher.go:201 (*Watcher).reconcileWatches
    pub fn reconcile_watches(&self, seen_file_paths: &[String]) -> Result<(), GoError> {
        let desired_dirs = self.compute_desired_watches(seen_file_paths);
        self.wm.borrow().reconcile_watches(&desired_dirs)
    }

    // Go: execute/watcher.go:206 (*Watcher).comparePathsOptions
    pub fn compare_paths_options(&self) -> ComparePathsOptions {
        ComparePathsOptions {
            use_case_sensitive_file_names: self.sys.fs().use_case_sensitive_file_names(),
            current_directory: self.sys.get_current_directory(),
        }
    }

    // Go: execute/watcher.go:213 (*Watcher).DoCycle
    // PORT: Go unlocks with `defer`; the port unlocks before each return.
    pub fn do_cycle(&mut self) {
        self.wm.borrow().lock();

        let (changed_paths, overflow) = self.wm.borrow().drain_events();
        let has_events = !changed_paths.is_empty() || overflow;

        if self.recheck_ts_config() {
            self.wm.borrow().unlock();
            return;
        }

        if has_events && !overflow && !self.config_modified {
            // Filter fswatch events against known dependencies
            if self.is_relevant_change(&changed_paths) {
                self.evict_changed_source_files(&changed_paths);
            } else {
                if let Some(debug_log) = &self.wm.borrow().debug_log {
                    write_str(
                        debug_log,
                        &format!(
                            "[watch] DoCycle: {} event(s) not relevant to compilation, skipping rebuild\n",
                            changed_paths.len()
                        ),
                    );
                }
                self.on_program();
                self.wm.borrow().unlock();
                return;
            }
        } else if overflow {
            // Overflow: evict the entire source file cache to force re-build
            self.source_file_cache = Rc::new(RefCell::new(FxHashMap::default()));
        } else if !has_events && !self.config_modified {
            // No events and no config change
            if let Some(debug_log) = &self.wm.borrow().debug_log {
                write_str(debug_log, "[watch] DoCycle: no events, skipping\n");
            }
            self.on_program();
            self.wm.borrow().unlock();
            return;
        }

        (self.report_watch_status)(&new_compiler_diagnostic(
            diag::File_change_detected_Starting_incremental_compilation,
            args![],
        ));
        if self.do_build().is_err() {
            // Mid-cycle watch failure; force a full rebuild on the next event
            self.wm.borrow().force_overflow();
        }
        self.wm.borrow().unlock();
    }

    // Go: execute/watcher.go:258 (*Watcher).isRelevantChange
    // PORT: Go map iteration order is random; `changed_paths` is an
    // `FxHashMap`. The result does not depend on the order.
    pub fn is_relevant_change(
        &self,
        changed_paths: &FxHashMap<String, fswatch::EventKind>,
    ) -> bool {
        let case_sensitive = self.sys.fs().use_case_sensitive_file_names();
        let cwd = self.sys.get_current_directory();
        let opts = self.compare_paths_options();
        for event_path in changed_paths.keys() {
            let p = to_path(event_path, &cwd, case_sensitive);
            if self.seen_files.contains(&p) {
                return true;
            }
            if self.config.config_file.is_some()
                && self.config.possibly_matches_file_name(event_path)
            {
                return true;
            }
            if self.config.config_file.is_some() && self.config.possibly_matches_directory_name(&p)
            {
                return true;
            }
            if self.sys.fs().directory_exists(event_path)
                && self.wm.borrow().is_path_under_watch(event_path, &opts)
            {
                return true;
            }
        }
        false
    }

    // Go: execute/watcher.go:282 (*Watcher).doBuild
    pub fn do_build(&mut self) -> Result<(), GoError> {
        if self.config_modified {
            self.source_file_cache = Rc::new(RefCell::new(FxHashMap::default()));
        }

        let cached = cachedvfs_from(self.sys.fs());
        let tfs = Rc::new(trackingvfs::FS {
            inner: cached.clone(),
            seen_files: RefCell::new(IndexSet::default()),
        });
        let inner_host = new_compiler_host(
            &self.sys.get_current_directory(),
            tfs.clone() as Rc<dyn Fs>,
            &self.sys.default_library_path(),
            self.extended_config_cache
                .clone()
                .map(|cache| cache as Rc<dyn ExtendedConfigCache>),
            Some(get_trace_from_sys(
                &*self.sys,
                self.config.locale(),
                self.testing.clone(),
            )),
        );
        let host: Rc<dyn CompilerHost> = Rc::new(WatchCompilerHost {
            compiler_host: inner_host,
            cache: self.source_file_cache.clone(),
        });

        if self.config.config_file.is_some() {
            let wildcard_dirs = self.config.wildcard_directories().clone();
            for dir in wildcard_dirs.keys() {
                tfs.seen_files.borrow_mut().insert(dir.clone());
            }
            if !wildcard_dirs.is_empty() {
                self.config = Rc::new(
                    self.config
                        .reload_file_names_of_parsed_command_line(&*self.sys.fs()),
                );
            }
        }
        for path in &self.config_file_paths {
            tfs.seen_files.borrow_mut().insert(path.clone());
        }

        // Go: compiler.NewProgram(compiler.ProgramOptions{Config, Host})
        // PORT: a new program version, current for the rest of the build.
        let version = new_program_version(host.clone(), self.config.clone());
        let _program = crate::core::enter_program(Some(version));
        let mut program = incremental::program::new_program(
            self.program.as_ref(),
            incremental::incremental::create_host(host),
            self.testing.is_some(),
        );
        // PORT: Go passes a nil incremental host. The Rust `new_program`
        // takes a host, so the field is cleared after.
        program.host = None;
        // PORT: Go drops the old program here. `program::release_program`
        // stops its checker pool, which frees its checkers. Its `GoProgram`,
        // frontend program and file versions stay leaked.
        if let Some(old) = self.program.replace(program).and_then(|old| old.program) {
            crate::program::release_program(old);
        }

        let result = self.compile_and_emit();
        cached.disable_and_clear_cache();

        let case_sensitive = self.sys.fs().use_case_sensitive_file_names();
        let cwd = self.sys.get_current_directory();
        let seen_slice: Vec<String> = tfs.seen_files.borrow().iter().cloned().collect();
        self.seen_files = FxHashSet::with_capacity_and_hasher(seen_slice.len(), Default::default());
        for p in &seen_slice {
            self.seen_files.insert(to_path(p, &cwd, case_sensitive));
        }

        self.config_mtimes =
            FxHashMap::with_capacity_and_hasher(self.config_file_paths.len(), Default::default());
        for cfg_path in &self.config_file_paths {
            if let Some(s) = self.sys.fs().stat(cfg_path) {
                self.config_mtimes.insert(cfg_path.clone(), s.mod_time());
            }
        }

        if let Err(err) = self.reconcile_watches(&seen_slice) {
            write_str(&self.sys.writer(), &format!("{}\n", err.error()));
            return Err(err);
        }
        self.config_modified = false;

        // PORT: Go `w.program.GetProgram().FilesByPath()`. `FilesByPath` is on
        // the frontend program of the current program version.
        let program = crate::program::go_frontend_program()
            .expect("the watch build made a Go frontend program");
        let program_files = program.files_by_path();
        self.source_file_cache
            .borrow_mut()
            .retain(|path, _| program_files.contains_key(path));

        let error_count = result.diagnostics.len();
        if error_count == 1 {
            (self.report_watch_status)(&new_compiler_diagnostic(
                diag::Found_1_error_Watching_for_file_changes,
                args![],
            ));
        } else {
            (self.report_watch_status)(&new_compiler_diagnostic(
                diag::Found_0_errors_Watching_for_file_changes,
                args![error_count],
            ));
        }

        self.on_program();
        Ok(())
    }

    /// Go `if w.testing != nil { w.testing.OnProgram(w.program) }`.
    // PORT: the test reads the program's files, so its version is current
    // for the call.
    fn on_program(&self) {
        let (Some(testing), Some(program)) = (&self.testing, &self.program) else {
            return;
        };
        let _program = crate::core::enter_program(program.program);
        testing.on_program(program);
    }

    // Go: execute/watcher.go:356 (*Watcher).evictChangedSourceFiles
    pub fn evict_changed_source_files(
        &self,
        changed_paths: &FxHashMap<String, fswatch::EventKind>,
    ) {
        let case_sensitive = self.sys.fs().use_case_sensitive_file_names();
        let cwd = self.sys.get_current_directory();
        for event_path in changed_paths.keys() {
            let p = to_path(event_path, &cwd, case_sensitive);
            if self.source_file_cache.borrow().contains_key(&p) {
                if let Some(debug_log) = &self.wm.borrow().debug_log {
                    write_str(
                        debug_log,
                        &format!("[watch] evicting cached source file: {}\n", p.as_str()),
                    );
                }
                self.source_file_cache.borrow_mut().remove(&p);
            }
        }
    }

    // Go: execute/watcher.go:370 (*Watcher).compileAndEmit
    // PORT: `EmitInput.Program` is the current program (see tsc/emit.rs);
    // `do_build` makes the build's version current. Go leaves `WriteFile`
    // nil; see `os_write_file`.
    pub fn compile_and_emit(&self) -> CompileAndEmitResult {
        let program = self.program.as_ref().expect("the watch program is set");
        emit_files_and_report_errors(&EmitInput {
            sys: &*self.sys,
            program_like: program,
            config: Some(&self.config),
            report_diagnostic: self.report_diagnostic.clone(),
            report_error_summary: self.report_error_summary.clone(),
            writer: self.sys.writer(),
            write_file: Some(os_write_file()),
            compile_times: Rc::new(RefCell::new(CompileTimes::default())),
            testing: self.testing.clone(),
            testing_m_times_cache: None,
        })
    }

    // Go: execute/watcher.go:384 (*Watcher).recheckTsConfig
    pub fn recheck_ts_config(&mut self) -> bool {
        if self.config_file_name.is_empty() {
            return false;
        }

        if !self.config_has_errors && !self.config_file_paths.is_empty() {
            let mut changed = false;
            for path in &self.config_file_paths {
                let old_mtime = self.config_mtimes.get(path);
                let s = self.sys.fs().stat(path);
                match old_mtime {
                    None => {
                        if s.is_some() {
                            changed = true;
                            break;
                        }
                    }
                    Some(old_mtime) => {
                        if s.is_none_or(|s| s.mod_time() != *old_mtime) {
                            changed = true;
                            break;
                        }
                    }
                }
            }
            if !changed {
                return false;
            }
        }

        let Some(config_parse_result) = self.parse_config_file() else {
            return true;
        };
        if self.config_has_errors {
            self.config_modified = true;
        }
        self.config_has_errors = false;
        let mut config_file_paths = vec![self.config_file_name.clone()];
        config_file_paths.extend(config_parse_result.extended_source_files().iter().cloned());
        self.config_file_paths = config_file_paths;
        // PORT: Go `reflect.DeepEqual` is `PartialEq` (see `ParsedOptions`).
        if self.config.parsed_config != config_parse_result.parsed_config {
            self.config_modified = true;
        }
        self.config = config_parse_result;
        false
    }

    // Go: execute/watcher.go:425 (*Watcher).parseConfigFile
    pub fn parse_config_file(&mut self) -> Option<Rc<ParsedCommandLine>> {
        let extended_config_cache = Rc::new(TscExtendedConfigCache::default());
        let (config_parse_result, errors) = get_parsed_command_line_of_config_file(
            &self.config_file_name,
            Some(&*self.compiler_options_from_command_line),
            self.command_line_raw.as_ref(),
            &SystemParseConfigHost(&*self.sys),
            Some(&*extended_config_cache),
        );
        if !errors.is_empty() {
            for e in &errors {
                (self.report_diagnostic)(e);
            }
            self.config_has_errors = true;
            let error_count = errors.len();
            if error_count == 1 {
                (self.report_watch_status)(&new_compiler_diagnostic(
                    diag::Found_1_error_Watching_for_file_changes,
                    args![],
                ));
            } else {
                (self.report_watch_status)(&new_compiler_diagnostic(
                    diag::Found_0_errors_Watching_for_file_changes,
                    args![error_count],
                ));
            }
            return None;
        }
        self.extended_config_cache = Some(extended_config_cache);
        config_parse_result.map(Rc::new)
    }
}
