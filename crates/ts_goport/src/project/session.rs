//! Go `internal/project/session.go`.
//!
//! PORT: one thread (see `project/dirty/interfaces.rs`). Every Go mutex of
//! `Session` is dropped; fields that Go changes after construction are
//! `Cell` / `RefCell`. Go `*Session` is `Rc<Session>`: methods that queue
//! work capturing the session (background tasks, timers) or that hand the
//! session to snapshot code take `self: &Rc<Self>`.
//!
//! Background tasks (`backgroundQueue.Enqueue`) run through
//! `background::Queue`, which posts them to `gostd::local::go` in Go
//! enqueue order. Debounce sleeps, the idle cache clean timer and the
//! telemetry ticker are `gostd::local::after_func` timers, so their
//! functions run on the dispatch thread; a debounced task keeps a
//! `background::TaskHold` until its timer has run. `WaitForBackgroundTasks`
//! drains `gostd::local` through `Queue::wait`. The one exception is the
//! clone of the auto-import warm, which is `gostd::local` idle work: the
//! LSP server runs it only after a quiet period with no message, and the
//! reader thread can cancel it (`WarmAutoImportPreempt`).
//!
//! Go runtime metrics (`runtime/metrics`) exist only in the Go runtime.
//! Performance telemetry reads them as `KindBad` (`metrics_read`), so its
//! Go runtime fields are 0; the system memory fields come from
//! `/proc/meminfo` (`osmemory_get`). The log-only runtime metrics and
//! `runtime.GC()` are PORT skips.

use crate::project::prelude::*;

use std::cell::Cell;
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, Instant};

// PORT: the Go text of a nil pointer dereference, for the Go calls on a
// maybe-nil pointer or interface that do not check for nil.
const NIL_DEREF: &str = "invalid memory address or nil pointer dereference";

// Go: project/session.go:33 UpdateReason
// PORT: Go `type UpdateReason int` with iota consts. Go
// `UpdateReasonDidOpenFile` is `UpdateReason::DID_OPEN_FILE` (same values).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UpdateReason(pub i32);

impl UpdateReason {
    pub const UNKNOWN: UpdateReason = UpdateReason(0);
    pub const DID_OPEN_FILE: UpdateReason = UpdateReason(1);
    pub const DID_CLOSE_FILE: UpdateReason = UpdateReason(2);
    pub const DID_CHANGE_COMPILER_OPTIONS_FOR_INFERRED_PROJECTS: UpdateReason = UpdateReason(3);
    pub const REQUESTED_LANGUAGE_SERVICE_PENDING_CHANGES: UpdateReason = UpdateReason(4);
    pub const REQUESTED_LANGUAGE_SERVICE_PROJECT_NOT_LOADED: UpdateReason = UpdateReason(5);
    pub const REQUESTED_LANGUAGE_SERVICE_FOR_FILE_NOT_OPEN: UpdateReason = UpdateReason(6);
    pub const REQUESTED_LANGUAGE_SERVICE_PROJECT_DIRTY: UpdateReason = UpdateReason(7);
    pub const REQUESTED_LOAD_PROJECT_TREE: UpdateReason = UpdateReason(8);
    pub const REQUESTED_LANGUAGE_SERVICE_WITH_AUTO_IMPORTS: UpdateReason = UpdateReason(9);
    pub const IDLE_CLEAN_DISK_CACHE: UpdateReason = UpdateReason(10);
}

// Go: project/session.go:51 watchRequestTimeout
// watchRequestTimeout is the maximum time to wait for the client to respond to
// a WatchFiles or UnwatchFiles request while holding the watches mutex.
pub const WATCH_REQUEST_TIMEOUT: Duration = Duration::from_secs(1);

// Go: project/session.go:55 SessionOptions
// SessionOptions are the immutable initialization options for a session.
// Snapshots may reference them as a pointer since they never change.
// PORT: Go `*SessionOptions` is `Rc<SessionOptions>`.
pub struct SessionOptions {
    pub current_directory: String,
    pub default_library_path: String,
    pub typings_location: String,
    pub position_encoding: lsproto::PositionEncodingKind,
    pub watch_enabled: bool,
    pub logging_enabled: bool,
    pub telemetry_enabled: bool,
    pub push_diagnostics_enabled: bool,
    pub debounce_delay: Duration,
    pub locale: locale::Locale,
    pub checker_pool_options: CheckerPoolOptions,
}

// Go: project/session.go:69 SessionInit
// PORT: Go nil interfaces and pointers are `None`.
pub struct SessionInit {
    pub background_ctx: Context,
    pub options: Rc<SessionOptions>,
    pub fs: Rc<dyn vfs::Fs>,
    pub client: Option<Rc<dyn Client>>,
    pub logger: Option<Rc<dyn logging::Logger>>,
    pub npm_executor: Option<Rc<dyn ata::NpmExecutor>>,
    pub parse_cache: Option<Rc<ParseCache>>,
}

// Go: project/session.go:85 Session
// Session manages the state of an LSP session. It receives textDocument
// events and requests for LanguageService objects from the LPS server
// and processes them into immutable snapshots as the data source for
// LanguageServices. When Session transitions from one snapshot to the
// next, it diffs them and updates file watchers and Automatic Type
// Acquisition (ATA) state accordingly.
// PORT: the Go mutexes (`snapshotMu`, `snapshotUpdateMu`,
// `scheduledSnapshotUpdateMu`, `userConfigRWMu`, `pendingFileChangesMu`,
// `pendingATAChangesMu`, `diagnosticsRefreshMu`, `warmAutoImportMu`,
// `idleCacheCleanMu`) are dropped. Go `atomic.*` fields are `Cell`.
pub struct Session {
    pub background_ctx: Context,
    pub options: Rc<SessionOptions>,
    pub start_time: Instant,
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    pub client: Option<Rc<dyn Client>>,
    pub logger: Option<Rc<dyn logging::Logger>>,
    pub npm_executor: Option<Rc<dyn ata::NpmExecutor>>,
    pub fs: Rc<OverlayFS>,

    // parseCache is the ref-counted cache of source files used when
    // creating programs during snapshot cloning.
    pub parse_cache: Rc<ParseCache>,
    // PORT: the parse cache references that auto-import registry clones
    // keep after the clone, one per path (see
    // `AutoImportRegistryCloneHost::dispose`). No Go counterpart.
    pub auto_import_parse_keys: Rc<AutoImportParseKeys>,
    // extendedConfigCache is the ref-counted cache of tsconfig ASTs
    // that are used in the "extends" of another tsconfig.
    pub extended_config_cache: Rc<ExtendedConfigCache>,
    // programCounter counts how many snapshots reference a program.
    // When a program is no longer referenced, its source files are
    // released from the parseCache.
    pub program_counter: Rc<ProgramCounter>,

    // read-only after initialization
    pub initial_user_preferences: RefCell<lsutil::UserPreferences>,
    // current preferences
    pub workspace_user_preferences: RefCell<lsutil::UserPreferences>,
    pub compiler_options_for_inferred_projects: RefCell<Option<Rc<CompilerOptions>>>,
    // PORT: set right after the session `Rc` exists (Go assigns it after
    // the composite literal). The installer holds the session as its host,
    // so the pair is a reference cycle that lives as long as the process.
    pub typings_installer: RefCell<Option<Rc<ata::TypingsInstaller>>>,
    pub background_queue: Rc<background::Queue>,

    // snapshotID is the counter for snapshot IDs. It does not necessarily
    // equal the `snapshot.ID`. It is stored on Session instead of globally
    // so IDs are predictable in tests.
    pub snapshot_id: Cell<u64>,

    // snapshot is the current immutable state of all projects.
    pub snapshot: RefCell<Rc<Snapshot>>,

    // scheduledSnapshotUpdateCancel is the cancelation function for a scheduled
    // snapshot update. Snapshot updates are scheduled and debounced after file closes.
    pub scheduled_snapshot_update_cancel: RefCell<Option<gostd::context::CancelFunc>>,
    pub scheduled_snapshot_update_generation: Cell<u64>,

    pub pending_user_config_changes: Cell<bool>,

    // pendingFileChanges are accumulated from textDocument/* events delivered
    // by the LSP server through DidOpenFile(), DidChangeFile(), etc. They are
    // applied to the next snapshot update.
    pub pending_file_changes: RefCell<Vec<FileChange>>,

    // pendingATAChanges are produced by Automatic Type Acquisition (ATA)
    // installations and applied to the next snapshot update.
    pub pending_ata_changes: RefCell<FxHashMap<tspath::Path, Rc<ATAStateChange>>>,

    // diagnosticsRefreshCancel is the cancelation function for a scheduled
    // diagnostics refresh. Diagnostics refreshes are scheduled and debounced
    // after file watch changes and ATA updates.
    pub diagnostics_refresh_cancel: RefCell<Option<gostd::context::CancelFunc>>,
    pub diagnostics_refresh_generation: Cell<u64>,

    // warmAutoImportCancel is the cancelation function for a running
    // auto-import cache warming task. It is cancelled on file opens,
    // closes, changes, watched-file changes, new auto-import warming
    // requests, and when the session closes.
    // PORT: Go stores its own closure (it logs through the session logger),
    // which is not `Send`, so this is an `Rc<dyn Fn()>`, not a
    // `gostd::context::CancelFunc`.
    pub warm_auto_import_cancel: RefCell<Option<Rc<dyn Fn()>>>,
    // PORT: the `Send` copy of `warm_auto_import_cancel` for the LSP reader
    // thread. See `WarmAutoImportPreempt`.
    pub warm_auto_import_preempt: WarmAutoImportPreempt,
    // PORT: the auto-import warm whose clone waits for idle time (see
    // `warm_auto_import_cache`), and whether an idle job for it is queued.
    pub warm_auto_import_pending: RefCell<Option<PendingWarm>>,
    pub warm_auto_import_queued: Cell<bool>,

    // idleCacheCleanTimer is a resettable timer for scheduling idle disk
    // cache cleans. The timer resets on any file event (open, close,
    // change, save, watch) and fires after 30 seconds of inactivity.
    pub idle_cache_clean_timer: RefCell<Option<gostd::local::LocalTimer>>,

    // performanceTelemetryCancel cancels the periodic performance telemetry ticker.
    pub performance_telemetry_cancel: RefCell<Option<gostd::context::CancelFunc>>,

    // seenProjects tracks projects that have already had telemetry sent.
    pub seen_projects: RefCell<FxHashSet<tspath::Path>>,

    // watches tracks the current watch globs and how many individual WatchedFiles
    // are using each glob.
    pub watches: Rc<WatchRegistry>,

    // globalDiagPublishPending is set to true when a global diagnostics publish
    // task should be enqueued. It is reset when the task runs, coalescing multiple
    // requests into a single background task.
    pub global_diag_publish_pending: Cell<bool>,
}

// Go: project/session.go:180 NewSession
pub fn new_session(init: &SessionInit) -> Rc<Session> {
    let current_directory = init.options.current_directory.clone();
    let use_case_sensitive_file_names = init.fs.use_case_sensitive_file_names();
    let to_path: Rc<dyn Fn(&str) -> tspath::Path> = Rc::new(move |file_name: &str| {
        tspath::to_path(file_name, &current_directory, use_case_sensitive_file_names)
    });
    let overlay_fs = new_overlay_fs(
        init.fs.clone(),
        IndexMap::default(),
        init.options.position_encoding.clone(),
        to_path.clone(),
    );
    let mut parse_cache = init.parse_cache.clone();
    if parse_cache.is_none() {
        parse_cache = Some(new_parse_cache(RefCountCacheOptions::default()));
    }
    let extended_config_cache = new_extended_config_cache();

    let mut session_logger = init.logger.clone();
    if session_logger.is_none() {
        session_logger = logging::new_nop_logger();
    }
    let session = Rc::new(Session {
        background_ctx: init.background_ctx.clone(),
        options: init.options.clone(),
        to_path: to_path.clone(),
        client: init.client.clone(),
        logger: session_logger,
        npm_executor: init.npm_executor.clone(),
        fs: overlay_fs,
        parse_cache: parse_cache.expect(NIL_DEREF),
        auto_import_parse_keys: Rc::new(RefCell::new(FxHashMap::default())),
        extended_config_cache,
        program_counter: Rc::new(ProgramCounter::default()),
        background_queue: background::new_queue(),
        start_time: Instant::now(),
        snapshot: RefCell::new(new_snapshot(
            0_u64,
            Rc::new(SnapshotFS {
                to_path: to_path.clone(),
                fs: init.fs.clone(),
                overlays: IndexMap::default(),
                overlay_directories: FxHashMap::default(),
                disk_files: Rc::new(FxHashMap::default()),
                disk_directories: Rc::new(FxHashMap::default()),
                read_files: RefCell::new(FxHashMap::default()),
                node_modules_realpath_aliases: Rc::new(FxHashMap::default()),
            }),
            init.options.clone(),
            Rc::new(ConfigFileRegistry::default()),
            None,
            lsutil::new_default_user_preferences(),
            None,
            Some(new_watched_files::<FxHashMap<tspath::Path, String>>(
                "auto-import",
                lsproto::WatchKind(
                    lsproto::WatchKind::CREATE.0
                        | lsproto::WatchKind::CHANGE.0
                        | lsproto::WatchKind::DELETE.0,
                ),
                lsproto::get_client_capabilities(&init.background_ctx)
                    .workspace
                    .did_change_watched_files
                    .relative_pattern_support,
                Rc::new(|node_modules_dirs: &FxHashMap<tspath::Path, String>| {
                    let mut patterns: Vec<String> = Vec::with_capacity(node_modules_dirs.len());
                    // PORT: Go map order is random; the patterns are sorted below.
                    for dir in node_modules_dirs.values() {
                        patterns.push(get_recursive_glob_pattern(dir));
                    }
                    patterns.sort();
                    PatternsAndIgnored {
                        patterns_inside_workspace: patterns,
                        ..Default::default()
                    }
                }),
            )),
            to_path,
        )),
        initial_user_preferences: RefCell::new(lsutil::new_default_user_preferences()),
        workspace_user_preferences: RefCell::new(lsutil::new_default_user_preferences()),
        compiler_options_for_inferred_projects: RefCell::new(None),
        typings_installer: RefCell::new(None),
        snapshot_id: Cell::new(0),
        scheduled_snapshot_update_cancel: RefCell::new(None),
        scheduled_snapshot_update_generation: Cell::new(0),
        pending_user_config_changes: Cell::new(false),
        pending_file_changes: RefCell::new(Vec::new()),
        pending_ata_changes: RefCell::new(FxHashMap::default()),
        diagnostics_refresh_cancel: RefCell::new(None),
        diagnostics_refresh_generation: Cell::new(0),
        warm_auto_import_cancel: RefCell::new(None),
        warm_auto_import_preempt: WarmAutoImportPreempt::default(),
        warm_auto_import_pending: RefCell::new(None),
        warm_auto_import_queued: Cell::new(false),
        idle_cache_clean_timer: RefCell::new(None),
        performance_telemetry_cancel: RefCell::new(None),
        seen_projects: RefCell::new(FxHashSet::default()),
        watches: new_watch_registry(),
        global_diag_publish_pending: Cell::new(false),
    });

    if !init.options.typings_location.is_empty() && init.npm_executor.is_some() {
        let typings_installer = ata::new_typings_installer(
            &ata::TypingsInstallerOptions {
                typings_location: init.options.typings_location.clone(),
                throttle_limit: 5,
            },
            session.clone(),
        );
        *session.typings_installer.borrow_mut() = Some(typings_installer);
    }

    session
}

// PORT: Go `FS()` and `GetCurrentDirectory()` implement
// `module.ResolutionHost`, whose Rust form returns borrowed values. The
// inherent methods keep the Go results for other callers (api session).
impl crate::frontend::module::ResolutionHost for Session {
    // Go: project/session.go:255 FS
    fn fs(&self) -> &dyn vfs::Fs {
        &*self.fs.fs
    }

    // Go: project/session.go:260 GetCurrentDirectory
    fn get_current_directory(&self) -> &str {
        &self.options.current_directory
    }
}

// Go: project/session.go:1584 NpmInstall
// PORT: Go `NpmInstall` implements `ata.NpmExecutor`. With this impl and
// `module::ResolutionHost`, `Session` is an `ata::TypingsInstallerHost`.
impl ata::NpmExecutor for Session {
    fn npm_install(&self, cwd: &str, npm_install_args: &[String]) -> (Vec<u8>, Option<GoError>) {
        self.npm_executor
            .as_ref()
            .expect(NIL_DEREF)
            .npm_install(cwd, npm_install_args)
    }
}

impl Session {
    // Go: project/session.go:255 FS
    // FS implements module.ResolutionHost
    pub fn fs(&self) -> Rc<dyn vfs::Fs> {
        self.fs.fs.clone()
    }

    // Go: project/session.go:260 GetCurrentDirectory
    // GetCurrentDirectory implements module.ResolutionHost
    pub fn get_current_directory(&self) -> String {
        self.options.current_directory.clone()
    }

    // Go: project/session.go:265 Config
    // Gets copy of current configuration
    pub fn config(&self) -> lsutil::UserPreferences {
        self.workspace_user_preferences.borrow().clone()
    }

    // Go: project/session.go:272 Trace
    // Trace implements module.ResolutionHost
    pub fn trace(&self, _msg: &str) {
        panic!("ATA module resolution should not use tracing");
    }

    // Go: project/session.go:276 Configure
    pub fn configure(self: &Rc<Self>, config: lsutil::UserPreferences) {
        self.pending_user_config_changes.set(true);
        let old_config = self.workspace_user_preferences.replace(config.clone());

        // Tell the client to re-request certain commands depending on user preference changes.
        self.refresh_inlay_hints_if_needed(&old_config, &config);
        self.refresh_code_lens_if_needed(&old_config, &config);
        self.refresh_diagnostics_if_needed(&old_config, &config);
        self.refresh_ata_if_needed(&old_config, &config);
    }

    // Go: project/session.go:290 InitializeWithUserConfig
    pub fn initialize_with_user_config(self: &Rc<Self>, config: lsutil::UserPreferences) {
        *self.initial_user_preferences.borrow_mut() = config.clone();
        self.configure(config);
    }

    // Go: project/session.go:295 DidOpenFile
    pub fn did_open_file(
        self: &Rc<Self>,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
        version: i32,
        content: &str,
        language_kind: &lsproto::LanguageKind,
    ) {
        self.cancel_warm_auto_import_cache();
        self.schedule_idle_cache_clean();
        self.cancel_scheduled_snapshot_update();
        self.pending_file_changes.borrow_mut().push(FileChange {
            kind: FileChangeKind::OPEN,
            uri: uri.clone(),
            version,
            content: content.to_string(),
            language_kind: language_kind.clone(),
            ..Default::default()
        });
        let (changes, overlays) = self.flush_changes_locked(ctx);
        self.update_snapshot_exported(
            ctx,
            overlays,
            SnapshotChange {
                reason: UpdateReason::DID_OPEN_FILE,
                file_changes: changes,
                resource_request: ResourceRequest {
                    documents: vec![uri.clone()],
                    ..Default::default()
                },
                ..Default::default()
            },
        );
    }

    // Go: project/session.go:320 DidCloseFile
    pub fn did_close_file(self: &Rc<Self>, _ctx: &Context, uri: &lsproto::DocumentUri) {
        self.cancel_warm_auto_import_cache();
        self.schedule_idle_cache_clean();
        self.pending_file_changes.borrow_mut().push(FileChange {
            kind: FileChangeKind::CLOSE,
            uri: uri.clone(),
            ..Default::default()
        });
        self.schedule_snapshot_update(UpdateReason::DID_CLOSE_FILE);
    }

    // Go: project/session.go:332 DidChangeFile
    pub fn did_change_file(
        self: &Rc<Self>,
        _ctx: &Context,
        uri: &lsproto::DocumentUri,
        version: i32,
        changes: &[lsproto::TextDocumentContentChangePartialOrWholeDocument],
    ) {
        self.cancel_diagnostics_refresh();
        self.cancel_warm_auto_import_cache();
        self.schedule_idle_cache_clean();
        self.pending_file_changes.borrow_mut().push(FileChange {
            kind: FileChangeKind::CHANGE,
            uri: uri.clone(),
            version,
            changes: changes.to_vec(),
            ..Default::default()
        });
    }

    // Go: project/session.go:346 DidSaveFile
    pub fn did_save_file(self: &Rc<Self>, _ctx: &Context, uri: &lsproto::DocumentUri) {
        self.schedule_idle_cache_clean();
        self.pending_file_changes.borrow_mut().push(FileChange {
            kind: FileChangeKind::SAVE,
            uri: uri.clone(),
            ..Default::default()
        });
    }

    // Go: project/session.go:356 DidChangeWatchedFiles
    // PORT: Go `[]*lsproto.FileEvent` is `&[lsproto::FileEvent]`.
    pub fn did_change_watched_files(
        self: &Rc<Self>,
        _ctx: &Context,
        changes: &[lsproto::FileEvent],
    ) {
        let mut file_changes: Vec<FileChange> = Vec::with_capacity(changes.len());
        for change in changes {
            let kind = match change.type_ {
                lsproto::FileChangeType::CREATED => FileChangeKind::WATCH_CREATE,
                lsproto::FileChangeType::CHANGED => FileChangeKind::WATCH_CHANGE,
                lsproto::FileChangeType::DELETED => FileChangeKind::WATCH_DELETE,
                _ => continue, // Ignore unknown change types.
            };
            file_changes.push(FileChange {
                kind,
                uri: change.uri.clone(),
                ..Default::default()
            });
        }

        self.pending_file_changes.borrow_mut().extend(file_changes);

        // Schedule a debounced diagnostics refresh
        self.schedule_diagnostics_refresh();
        self.cancel_warm_auto_import_cache();
        self.schedule_idle_cache_clean();
    }

    // Go: project/session.go:386 DidChangeCompilerOptionsForInferredProjects
    pub fn did_change_compiler_options_for_inferred_projects(
        self: &Rc<Self>,
        ctx: &Context,
        options: Option<Rc<CompilerOptions>>,
    ) {
        *self.compiler_options_for_inferred_projects.borrow_mut() = options.clone();
        self.update_snapshot_exported(
            ctx,
            self.fs.overlays(),
            SnapshotChange {
                reason: UpdateReason::DID_CHANGE_COMPILER_OPTIONS_FOR_INFERRED_PROJECTS,
                compiler_options_for_inferred_projects: options,
                ..Default::default()
            },
        );
    }

    // Go: project/session.go:394 ScheduleDiagnosticsRefresh
    // PORT: Go sleeps inside the background task with
    // `select { case <-time.After(delay): case <-ctx.Done(): }`. Here the
    // task arms a `gostd::local::after_func` timer for the delay, and the
    // rest of the task runs when it fires; a cancelled context makes it
    // return then (Go returns at once; nothing else differs). The task
    // keeps a `background::TaskHold` until then, so `Queue::wait` (Go
    // `WaitForBackgroundTasks`) waits for the refresh, as Go's does.
    pub fn schedule_diagnostics_refresh(self: &Rc<Self>) {
        // Cancel any existing scheduled diagnostics refresh
        let existing_cancel = self.diagnostics_refresh_cancel.borrow().clone();
        if let Some(existing_cancel) = existing_cancel {
            existing_cancel();
            self.logger.log("Delaying scheduled diagnostics refresh...");
        } else {
            self.logger.log("Scheduling new diagnostics refresh...");
        }

        // Create a new cancellable context for the debounce task
        let (debounce_ctx, cancel) = gostd::context::with_cancel(&self.background_ctx);
        self.diagnostics_refresh_generation
            .set(self.diagnostics_refresh_generation.get() + 1);
        let generation = self.diagnostics_refresh_generation.get();
        *self.diagnostics_refresh_cancel.borrow_mut() = Some(cancel.clone());

        // Enqueue the debounced diagnostics refresh
        let s = self.clone();
        self.background_queue.enqueue(&debounce_ctx, move |ctx| {
            let ctx = ctx.clone();
            let delay = s.options.debounce_delay;
            let hold = s.background_queue.hold();
            let mut task = Some(move || {
                let run = || {
                    // Sleep for the debounce delay
                    if ctx.err().is_some() {
                        // Context was cancelled, newer events arrived
                        return;
                    }
                    // Delay completed, proceed with refresh

                    // Clear the cancel function since we're about to execute the refresh
                    if s.diagnostics_refresh_generation.get() != generation {
                        return;
                    }
                    *s.diagnostics_refresh_cancel.borrow_mut() = None;

                    if s.options.logging_enabled {
                        s.logger.log("Running scheduled diagnostics refresh");
                    }
                    if let Err(err) = s
                        .client
                        .as_ref()
                        .expect(NIL_DEREF)
                        .refresh_diagnostics(&s.background_ctx)
                    {
                        if s.options.logging_enabled {
                            s.logger
                                .logf(&format!("Error refreshing diagnostics: {}", err.error()));
                        }
                    }
                };
                run();
                // Go: defer cancel()
                cancel();
                drop(hold);
            });
            gostd::local::after_func(
                delay,
                Box::new(move || {
                    if let Some(task) = task.take() {
                        task();
                    }
                }),
            );
        });
    }

    // Go: project/session.go:442 cancelDiagnosticsRefresh
    pub fn cancel_diagnostics_refresh(&self) {
        let cancel = self.diagnostics_refresh_cancel.borrow().clone();
        if let Some(cancel) = cancel {
            cancel();
            self.logger.log("Canceled scheduled diagnostics refresh");
            *self.diagnostics_refresh_cancel.borrow_mut() = None;
            self.diagnostics_refresh_generation
                .set(self.diagnostics_refresh_generation.get() + 1);
        }
    }

    // Go: project/session.go:453 ScheduleSnapshotUpdate
    // PORT: the debounce sleep is a `gostd::local::after_func` timer, and
    // the task keeps a `background::TaskHold` until the update has run, as
    // in `schedule_diagnostics_refresh`.
    pub fn schedule_snapshot_update(self: &Rc<Self>, reason: UpdateReason) {
        // Cancel any existing scheduled snapshot update
        let existing_cancel = self.scheduled_snapshot_update_cancel.borrow().clone();
        if let Some(existing_cancel) = existing_cancel {
            existing_cancel();
            if self.options.logging_enabled {
                self.logger.log("Delaying scheduled snapshot update...");
            }
        } else if self.options.logging_enabled {
            self.logger.log("Scheduling new snapshot update...");
        }

        // Create a new cancellable context for the debounce task
        let (debounce_ctx, cancel) = gostd::context::with_cancel(&self.background_ctx);
        self.scheduled_snapshot_update_generation
            .set(self.scheduled_snapshot_update_generation.get() + 1);
        let generation = self.scheduled_snapshot_update_generation.get();
        *self.scheduled_snapshot_update_cancel.borrow_mut() = Some(cancel.clone());

        // Enqueue the debounced snapshot update
        let s = self.clone();
        self.background_queue.enqueue(&debounce_ctx, move |ctx| {
            let ctx = ctx.clone();
            let delay = s.options.debounce_delay;
            let hold = s.background_queue.hold();
            let mut task = Some(move || {
                let run = || {
                    // Sleep for the debounce delay
                    if ctx.err().is_some() {
                        // Context was cancelled, newer events arrived or another snapshot update ran
                        return;
                    }
                    // Delay completed, proceed with update

                    // Clear the cancel function since we're about to execute the update
                    if s.scheduled_snapshot_update_generation.get() != generation {
                        return;
                    }
                    *s.scheduled_snapshot_update_cancel.borrow_mut() = None;

                    if s.options.logging_enabled {
                        s.logger.log("Running scheduled snapshot update");
                    }

                    let (file_changes, overlays, ata_changes, new_config) = s.flush_changes(&ctx);
                    if file_changes.is_empty() && ata_changes.is_empty() && new_config.is_none() {
                        return;
                    }

                    s.update_snapshot_exported(
                        &ctx,
                        overlays,
                        SnapshotChange {
                            reason,
                            file_changes,
                            ata_changes,
                            new_config,
                            ..Default::default()
                        },
                    );
                };
                run();
                // Go: defer cancel()
                cancel();
                drop(hold);
            });
            gostd::local::after_func(
                delay,
                Box::new(move || {
                    if let Some(task) = task.take() {
                        task();
                    }
                }),
            );
        });
    }

    // Go: project/session.go:515 cancelScheduledSnapshotUpdate
    pub fn cancel_scheduled_snapshot_update(&self) {
        let cancel = self.scheduled_snapshot_update_cancel.borrow().clone();
        if let Some(cancel) = cancel {
            cancel();
            if self.options.logging_enabled {
                self.logger.log("Canceled scheduled snapshot update");
            }
            *self.scheduled_snapshot_update_cancel.borrow_mut() = None;
            self.scheduled_snapshot_update_generation
                .set(self.scheduled_snapshot_update_generation.get() + 1);
        }
    }

    // Go: project/session.go:528 cancelWarmAutoImportCache
    pub fn cancel_warm_auto_import_cache(&self) {
        let cancel = self.warm_auto_import_cancel.borrow().clone();
        if let Some(cancel) = cancel {
            cancel();
            *self.warm_auto_import_cancel.borrow_mut() = None;
            self.warm_auto_import_preempt.clear();
        }
        // PORT: a cancelled warm whose clone has not started lets its
        // snapshot go now (see `run_pending_warm`).
        match self.warm_auto_import_pending.take() {
            Some(warm) if warm.ctx.err().is_some() => self.end_pending_warm(warm),
            pending => *self.warm_auto_import_pending.borrow_mut() = pending,
        }
    }
}

/// PORT: the state that Go's `warmAutoImportCache` keeps for its clone,
/// while the clone waits for idle time. It holds a reference on
/// `new_snapshot` (Go `tryRef`).
pub struct PendingWarm {
    ctx: Context,
    cancel: gostd::context::CancelFunc,
    changed_file: lsproto::DocumentUri,
    new_snapshot: Rc<Snapshot>,
    /// The id that Go's clone takes when the warm starts.
    snapshot_id: u64,
}

/// PORT: cancels the auto-import warm from the LSP reader thread.
///
/// Go runs the warm on a goroutine, and the dispatch goroutine cancels it
/// when it handles didOpen, didChange, didClose or didChangeWatchedFiles.
/// Here the warm runs on the dispatch thread, so the dispatch thread cannot
/// get to those messages until the warm ends. The reader thread calls
/// `cancel` when one of them arrives, and the warm stops at its next
/// context check. The handler's own `cancel_warm_auto_import_cache` then
/// finds the warm done, as Go's does when the warm has ended.
///
/// It holds the same context and cancel function as
/// `Session::warm_auto_import_cancel`, and is set and cleared with it.
#[derive(Clone, Default)]
pub struct WarmAutoImportPreempt(Arc<Mutex<Option<WarmAutoImportPreemptEntry>>>);

struct WarmAutoImportPreemptEntry {
    ctx: Context,
    cancel: gostd::context::CancelFunc,
    file_name: String,
}

impl WarmAutoImportPreempt {
    fn entry(&self) -> MutexGuard<'_, Option<WarmAutoImportPreemptEntry>> {
        // PORT: Go mutexes do not poison.
        self.0.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn set(&self, ctx: Context, cancel: gostd::context::CancelFunc, file_name: String) {
        *self.entry() = Some(WarmAutoImportPreemptEntry {
            ctx,
            cancel,
            file_name,
        });
    }

    fn clear(&self) {
        *self.entry() = None;
    }

    /// Go `cancelWarmAutoImportCache`, with the log line of the stored
    /// cancel function. Safe to call from any thread.
    pub fn cancel(&self, logger: &dyn logging::Logger) {
        let Some(entry) = self.entry().take() else {
            return;
        };
        if entry.ctx.err().is_some() {
            return;
        }
        logger.logf(&format!(
            "Cancelling auto-import warming for file {}",
            entry.file_name
        ));
        (entry.cancel)();
    }
}

// Go: project/session.go:537 idleCacheCleanDelay
pub const IDLE_CACHE_CLEAN_DELAY: Duration = Duration::from_secs(30);

impl Session {
    // Go: project/session.go:539 scheduleIdleCacheClean
    pub fn schedule_idle_cache_clean(self: &Rc<Self>) {
        if let Some(timer) = self.idle_cache_clean_timer.borrow().as_ref() {
            timer.stop();
        }

        let s = self.clone();
        let timer = gostd::local::after_func(
            IDLE_CACHE_CLEAN_DELAY,
            Box::new(move || {
                *s.idle_cache_clean_timer.borrow_mut() = None;

                s.cancel_scheduled_snapshot_update();

                let ctx = s.background_ctx.clone();
                let (file_changes, overlays, ata_changes, new_config) = s.flush_changes(&ctx);
                s.update_snapshot_exported(
                    &ctx,
                    overlays,
                    SnapshotChange {
                        reason: UpdateReason::IDLE_CLEAN_DISK_CACHE,
                        file_changes,
                        ata_changes,
                        new_config,
                        clean_disk_cache: true,
                        ..Default::default()
                    },
                );

                // Go: go func() { runtime.GC() }()
                // PORT: skipped. Rust has no garbage collector; memory the
                // new snapshot released is freed when its last owner drops.
            }),
        );
        *self.idle_cache_clean_timer.borrow_mut() = Some(timer);
    }

    // Go: project/session.go:570 cancelIdleCacheClean
    pub fn cancel_idle_cache_clean(&self) {
        let timer = self.idle_cache_clean_timer.borrow_mut().take();
        if let Some(timer) = timer {
            timer.stop();
        }
    }
}

// Go: project/session.go:579 performanceTelemetryInterval
pub const PERFORMANCE_TELEMETRY_INTERVAL: Duration = Duration::from_secs(5 * 60);

// PORT: Go `runtime/metrics.Sample` and `metrics.Value` (Go standard
// library). Only the shape is ported: the values describe the Go runtime.
#[derive(Clone, Debug, Default)]
struct MetricsSample {
    name: &'static str,
    value: MetricsValue,
}

// PORT: Go `metrics.Value` by `Kind()`.
#[derive(Clone, Copy, Debug, Default)]
enum MetricsValue {
    #[default]
    Bad,
    Uint64(u64),
    Float64(f64),
    Float64Histogram,
}

// Go: runtime/metrics/sample.go:45 Read (go1.26.8), which runs
// runtime/metrics.go:1028 readMetricsLocked.
// PORT: Go computes each metric from Go runtime statistics (heap, GC,
// scheduler, goroutines). The port has no Go runtime, so it has none of
// these metrics. Go gives `KindBad` for a name it does not have, so every
// sample is `KindBad` and every Go runtime field of the telemetry event is
// 0 (`memoryUsedBytes`, `goMemLimit`, `goGCPercent`, the heap and GC
// fields, `goMaxProcs`, `goroutineCount`, `gcCpuSeconds`, `userCpuSeconds`).
fn metrics_read(samples: &mut [MetricsSample]) {
    // Sample.
    for sample in samples.iter_mut() {
        sample.value = MetricsValue::Bad;
    }
}

// PORT: Go `go-osstat/memory.Stats` (the two fields session.go reads).
struct OsMemoryStats {
    total: u64,
    used: u64,
}

// Go: github.com/mackerelio/go-osstat@v0.2.7 memory/memory_linux.go:15 Get
// Get memory statistics
fn osmemory_get() -> Result<OsMemoryStats, GoError> {
    // Reference: man 5 proc, Documentation/filesystems/proc.txt in Linux source code
    let mut file = match std::fs::File::open("/proc/meminfo") {
        Ok(file) => file,
        Err(err) => return Err(crate::pprof::path_error("open", "/proc/meminfo", &err)),
    };
    // Go: defer file.Close(). The file closes when it drops.
    collect_memory_stats(&mut file)
}

// Go: github.com/mackerelio/go-osstat@v0.2.7 memory/memory_linux.go:33 collectMemoryStats
// PORT: Go fills every `Stats` field. The port keeps the fields that
// `Total` and `Used` need (`OsMemoryStats`); the other `memStats` names set
// only fields that nobody reads. Go reads lines with `bufio.Scanner`, which
// stops at the first read error; the port reads the whole file first. A
// meminfo line is never longer than the 64 KiB scanner limit.
fn collect_memory_stats(out: &mut dyn std::io::Read) -> Result<OsMemoryStats, GoError> {
    let mut data = Vec::new();
    if let Err(err) = out.read_to_end(&mut data) {
        return Err(gostd::errors::new(format!(
            "scan error for /proc/meminfo: {err}"
        )));
    }
    let (mut total, mut free, mut available, mut buffers, mut cached) =
        (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut mem_available_enabled = false;
    // Go: bufio.ScanLines. A line ends at "\n" and loses a final "\r"; the
    // empty piece after the last "\n" has no ':' and is skipped.
    for line in data.split(|&c| c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let Some(i) = line.iter().position(|&c| c == b':') else {
            continue;
        };
        let fld = &line[..i];
        let ptr = match fld {
            b"MemTotal" => &mut total,
            b"MemFree" => &mut free,
            b"MemAvailable" => &mut available,
            b"Buffers" => &mut buffers,
            b"Cached" => &mut cached,
            _ => continue,
        };
        // Go: strings.TrimSpace(strings.TrimRight(line[i+1:], "kB"))
        let mut val = &line[i + 1..];
        while let [rest @ .., b'k' | b'B'] = val {
            val = rest;
        }
        // PORT: Go TrimSpace also trims non-ASCII spaces, which meminfo does
        // not have.
        let is_space = |c: &u8| matches!(c, b'\t' | b'\n' | 0x0b | 0x0c | b'\r' | b' ');
        while let [c, rest @ ..] = val
            && is_space(c)
        {
            val = rest;
        }
        while let [rest @ .., c] = val
            && is_space(c)
        {
            val = rest;
        }
        // Go: strconv.ParseUint(val, 10, 64). Rust also takes a leading '+'.
        if val.first() != Some(&b'+')
            && let Some(v) = std::str::from_utf8(val)
                .ok()
                .and_then(|v| v.parse::<u64>().ok())
        {
            *ptr = v.wrapping_mul(1024);
        }
        if fld == b"MemAvailable" {
            mem_available_enabled = true;
        }
    }

    let used = if mem_available_enabled {
        total.wrapping_sub(available)
    } else {
        total
            .wrapping_sub(free)
            .wrapping_sub(buffers)
            .wrapping_sub(cached)
    };

    Ok(OsMemoryStats { total, used })
}

impl Session {
    // Go: project/session.go:583 StartPerformanceTelemetry
    // StartPerformanceTelemetry begins periodic collection and sending of performance
    // telemetry. It should be called once after the session is initialized.
    // PORT: Go loops over a `time.Ticker` in the background task. Here the
    // task arms a `gostd::local::after_func` timer that re-arms itself for
    // the next tick until the context is done (checked on each tick).
    pub fn start_performance_telemetry(self: &Rc<Self>) {
        if !self.options.telemetry_enabled {
            return;
        }
        let (ctx, cancel) = gostd::context::with_cancel(&self.background_ctx);
        *self.performance_telemetry_cancel.borrow_mut() = Some(cancel);
        let s = self.clone();
        self.background_queue.enqueue(&ctx, move |ctx| {
            let ctx = ctx.clone();
            let ticker: Rc<RefCell<Option<gostd::local::LocalTimer>>> = Rc::new(RefCell::new(None));
            let tick_ticker = ticker.clone();
            let timer = gostd::local::after_func(
                PERFORMANCE_TELEMETRY_INTERVAL,
                Box::new(move || {
                    // Go: case <-ctx.Done(): return (defer ticker.Stop())
                    if ctx.err().is_some() {
                        let stopped = tick_ticker.borrow_mut().take();
                        if let Some(stopped) = stopped {
                            stopped.stop();
                        }
                        return;
                    }
                    // Go: case <-ticker.C (the ticker sends the next tick after the interval)
                    if let Some(t) = tick_ticker.borrow().as_ref() {
                        t.reset(PERFORMANCE_TELEMETRY_INTERVAL);
                    }
                    if s.client.is_none() || !s.client.as_ref().expect(NIL_DEREF).is_active() {
                        return; // Go: continue
                    }
                    s.send_performance_telemetry(&ctx);
                }),
            );
            *ticker.borrow_mut() = Some(timer);
        });
    }

    // Go: project/session.go:606 stopPerformanceTelemetry
    pub fn stop_performance_telemetry(&self) {
        let cancel = self.performance_telemetry_cancel.borrow().clone();
        if let Some(cancel) = cancel {
            cancel();
            *self.performance_telemetry_cancel.borrow_mut() = None;
        }
    }

    // Go: project/session.go:613 sendPerformanceTelemetry
    pub fn send_performance_telemetry(&self, ctx: &Context) {
        if self.client.is_none() || !self.options.telemetry_enabled {
            return;
        }
        let snapshot = self.snapshot.borrow().clone();

        // Read Go runtime metrics in a single call
        const S_MEMORY_USED_BYTES: usize = 0;
        const S_GO_MEM_LIMIT: usize = 1;
        const S_GO_GC_PERCENT: usize = 2;
        const S_HEAP_GOAL_BYTES: usize = 3;
        const S_HEAP_LIVE_BYTES: usize = 4;
        const S_HEAP_OBJECT_COUNT: usize = 5;
        const S_HEAP_STACK_BYTES: usize = 6;
        const S_HEAP_RELEASED_BYTES: usize = 7;
        const S_HEAP_FREE_BYTES: usize = 8;
        const S_GC_SCAN_HEAP_BYTES: usize = 9;
        const S_GO_MAX_PROCS: usize = 10;
        const S_GOROUTINE_COUNT: usize = 11;
        const S_GC_CYCLES_TOTAL: usize = 12;
        const S_GC_CPU_SECONDS: usize = 13;
        const S_USER_CPU_SECONDS: usize = 14;
        const S_METRIC_COUNT: usize = 15;
        let mut samples: Vec<MetricsSample> = vec![MetricsSample::default(); S_METRIC_COUNT];
        samples[S_MEMORY_USED_BYTES].name = "/memory/classes/total:bytes";
        samples[S_GO_MEM_LIMIT].name = "/gc/gomemlimit:bytes";
        samples[S_GO_GC_PERCENT].name = "/gc/gogc:percent";
        samples[S_HEAP_GOAL_BYTES].name = "/gc/heap/goal:bytes";
        samples[S_HEAP_LIVE_BYTES].name = "/gc/heap/live:bytes";
        samples[S_HEAP_OBJECT_COUNT].name = "/gc/heap/objects:objects";
        samples[S_HEAP_STACK_BYTES].name = "/memory/classes/heap/stacks:bytes";
        samples[S_HEAP_RELEASED_BYTES].name = "/memory/classes/heap/released:bytes";
        samples[S_HEAP_FREE_BYTES].name = "/memory/classes/heap/free:bytes";
        samples[S_GC_SCAN_HEAP_BYTES].name = "/gc/scan/heap:bytes";
        samples[S_GO_MAX_PROCS].name = "/sched/gomaxprocs:threads";
        samples[S_GOROUTINE_COUNT].name = "/sched/goroutines:goroutines";
        samples[S_GC_CYCLES_TOTAL].name = "/gc/cycles/total:gc-cycles";
        samples[S_GC_CPU_SECONDS].name = "/cpu/classes/gc/total:cpu-seconds";
        samples[S_USER_CPU_SECONDS].name = "/cpu/classes/user:cpu-seconds";
        metrics_read(&mut samples);

        let mut measurements = lsproto::PerformanceStatsTelemetryMeasurements {
            open_file_count: snapshot.fs.overlays.len() as f64,
            uptime_seconds: self.start_time.elapsed().as_secs_f64(),
            project_count: snapshot.project_collection.projects().len() as f64,
            config_count: snapshot.config_file_registry.configs.len() as f64,
            cached_disk_file_count: snapshot.fs.disk_files.len() as f64,
            ..Default::default()
        };

        let read_uint64 = |s: &MetricsSample| -> f64 {
            if let MetricsValue::Uint64(v) = s.value {
                return v as f64;
            }
            0.0
        };
        let read_float64 = |s: &MetricsSample| -> f64 {
            if let MetricsValue::Float64(v) = s.value {
                return v;
            }
            0.0
        };

        measurements.memory_used_bytes = read_uint64(&samples[S_MEMORY_USED_BYTES]);
        if let MetricsValue::Uint64(v) = samples[S_GO_MEM_LIMIT].value {
            if v < i64::MAX as u64 {
                measurements.go_mem_limit = v as f64;
            }
            // else: default (MaxInt64) exceeds MAX_SAFE_INTEGER; leave as 0 to indicate unconfigured
        }
        measurements.go_gc_percent = read_uint64(&samples[S_GO_GC_PERCENT]);
        measurements.heap_goal_bytes = read_uint64(&samples[S_HEAP_GOAL_BYTES]);
        measurements.heap_live_bytes = read_uint64(&samples[S_HEAP_LIVE_BYTES]);
        measurements.heap_object_count = read_uint64(&samples[S_HEAP_OBJECT_COUNT]);
        measurements.heap_stack_bytes = read_uint64(&samples[S_HEAP_STACK_BYTES]);
        measurements.heap_released_bytes = read_uint64(&samples[S_HEAP_RELEASED_BYTES]);
        measurements.heap_free_bytes = read_uint64(&samples[S_HEAP_FREE_BYTES]);
        measurements.gc_scan_heap_bytes = read_uint64(&samples[S_GC_SCAN_HEAP_BYTES]);
        measurements.go_max_procs = read_uint64(&samples[S_GO_MAX_PROCS]);
        measurements.goroutine_count = read_uint64(&samples[S_GOROUTINE_COUNT]);
        measurements.gc_cycles_total = read_uint64(&samples[S_GC_CYCLES_TOTAL]);
        measurements.gc_cpu_seconds = read_float64(&samples[S_GC_CPU_SECONDS]);
        measurements.user_cpu_seconds = read_float64(&samples[S_USER_CPU_SECONDS]);

        // Read system memory stats
        if let Ok(sys_mem) = osmemory_get() {
            measurements.system_mem_total = sys_mem.total as f64;
            measurements.system_mem_used = sys_mem.used as f64;
        }

        // Read auto-import registry stats
        if let Some(registry) = snapshot.auto_import_registry() {
            let auto_import_stats = registry.get_cache_stats();
            measurements.auto_import_project_bucket_count =
                auto_import_stats.project_buckets.len() as f64;
            measurements.auto_import_node_modules_bucket_count =
                auto_import_stats.node_modules_buckets.len() as f64;
            measurements.auto_import_unique_package_count =
                auto_import_stats.unique_package_count as f64;
            for b in &auto_import_stats.project_buckets {
                measurements.auto_import_project_export_count += b.export_count as f64;
                measurements.auto_import_project_file_count += b.file_count as f64;
            }
            for b in &auto_import_stats.node_modules_buckets {
                measurements.auto_import_node_modules_export_count += b.export_count as f64;
                measurements.auto_import_node_modules_file_count += b.file_count as f64;
                if b.dependency_names.is_none() {
                    measurements.auto_import_node_modules_unfiltered_bucket_count += 1.0;
                }
            }
        }

        if let Err(err) = self.client.as_ref().expect(NIL_DEREF).send_telemetry(
            ctx,
            lsproto::TelemetryEvent {
                performance_stats_telemetry_event: Some(lsproto::PerformanceStatsTelemetryEvent {
                    measurements: Some(measurements),
                    ..Default::default()
                }),
                ..Default::default()
            },
        ) {
            if self.options.logging_enabled {
                self.logger.logf(&format!(
                    "Error sending performance telemetry: {}",
                    err.error()
                ));
            }
        }
    }

    // Go: project/session.go:735 sendProjectInfoTelemetryForNewProjects
    pub fn send_project_info_telemetry_for_new_projects(
        &self,
        old_snapshot: &Rc<Snapshot>,
        new_snapshot: &Rc<Snapshot>,
    ) {
        if !self.options.telemetry_enabled {
            return;
        }
        let ctx = self.background_ctx.clone();
        crate::frontend::core_ls_ext::diff_ordered_maps(
            &old_snapshot.project_collection.projects_by_path(),
            &new_snapshot.project_collection.projects_by_path(),
            |_: &tspath::Path, added_project| {
                self.send_project_info_telemetry(&ctx, added_project);
            },
            |_: &tspath::Path, _| {},
            |_: &tspath::Path, _, _| {},
        );
    }

    // Go: project/session.go:751 sendProjectInfoTelemetry
    pub fn send_project_info_telemetry(&self, ctx: &Context, project: &Rc<RefCell<Project>>) {
        if self.client.is_none() || !self.options.telemetry_enabled {
            return;
        }
        let project = project.borrow();
        if self
            .seen_projects
            .borrow()
            .contains(&project.config_file_path)
        {
            return;
        }

        if project.program.is_none() || project.command_line.is_none() {
            return;
        }

        let info = self.collect_project_info_telemetry(&project);
        if let Err(err) = self
            .client
            .as_ref()
            .expect(NIL_DEREF)
            .send_telemetry(ctx, info)
        {
            if self.options.logging_enabled {
                self.logger.logf(&format!(
                    "Error sending project info telemetry: {}",
                    err.error()
                ));
            }
            return;
        }

        self.seen_projects
            .borrow_mut()
            .insert(project.config_file_path.clone());
    }

    // Go: project/session.go:774 collectProjectInfoTelemetry
    // PORT: Go `map[string]string` and `map[string]any` are `IndexMap`s in
    // insertion order (PORT: Go map order is random, also in its JSON).
    pub fn collect_project_info_telemetry(&self, project: &Project) -> lsproto::TelemetryEvent {
        let command_line = project.command_line.as_ref().expect(NIL_DEREF);
        // PORT: Go replaces a nil `CompilerOptions()` with an empty
        // `core.CompilerOptions`; the Rust command line always has options.
        let opts = command_line.compiler_options().clone();

        let mut config_file_name = "other".to_string();
        if project.kind == Kind::CONFIGURED {
            let base_name = tspath::get_base_file_name(&project.config_file_name);
            if base_name == "tsconfig.json" || base_name == "jsconfig.json" {
                config_file_name = base_name;
            }
        }

        let mut project_type = "inferred";
        if project.kind == Kind::CONFIGURED {
            project_type = "configured";
        }

        let mut props: IndexMap<String, String> = IndexMap::default();
        props.insert("configFileName".to_string(), config_file_name);
        props.insert("projectType".to_string(), project_type.to_string());
        props.insert("version".to_string(), crate::core::version().to_string());

        // Compiler options — same approach as Strada's convertCompilerOptionsForTelemetry:
        // booleans and enum string names, no paths.
        let mut compiler_options: IndexMap<String, LspAny> = IndexMap::default();
        set_tristate(&mut compiler_options, "strict", opts.strict);
        set_tristate(&mut compiler_options, "noImplicitAny", opts.no_implicit_any);
        set_tristate(
            &mut compiler_options,
            "noImplicitThis",
            opts.no_implicit_this,
        );
        set_tristate(
            &mut compiler_options,
            "strictNullChecks",
            opts.strict_null_checks,
        );
        set_tristate(
            &mut compiler_options,
            "strictFunctionTypes",
            opts.strict_function_types,
        );
        set_tristate(
            &mut compiler_options,
            "strictBindCallApply",
            opts.strict_bind_call_apply,
        );
        set_tristate(
            &mut compiler_options,
            "strictPropertyInitialization",
            opts.strict_property_initialization,
        );
        set_tristate(
            &mut compiler_options,
            "strictBuiltinIteratorReturn",
            opts.strict_builtin_iterator_return,
        );
        set_tristate(
            &mut compiler_options,
            "useUnknownInCatchVariables",
            opts.use_unknown_in_catch_variables,
        );
        set_tristate(
            &mut compiler_options,
            "exactOptionalPropertyTypes",
            opts.exact_optional_property_types,
        );
        set_tristate(&mut compiler_options, "allowJs", opts.allow_js);
        set_tristate(&mut compiler_options, "checkJs", opts.check_js);
        set_tristate(&mut compiler_options, "noEmit", opts.no_emit);
        set_tristate(&mut compiler_options, "declaration", opts.declaration);
        set_tristate(&mut compiler_options, "composite", opts.composite);
        set_tristate(
            &mut compiler_options,
            "isolatedModules",
            opts.isolated_modules,
        );
        set_tristate(&mut compiler_options, "skipLibCheck", opts.skip_lib_check);
        set_tristate(&mut compiler_options, "incremental", opts.incremental);
        if opts.target != ScriptTarget::NONE {
            compiler_options.insert("target".to_string(), LspAny::String(opts.target.string()));
        }
        if opts.module != ModuleKind::NONE {
            compiler_options.insert("module".to_string(), LspAny::String(opts.module.string()));
        }
        if opts.module_resolution != ModuleResolutionKind::UNKNOWN {
            compiler_options.insert(
                "moduleResolution".to_string(),
                LspAny::String(opts.module_resolution.string()),
            );
        }
        if opts.jsx != JsxEmit::NONE {
            compiler_options.insert("jsx".to_string(), LspAny::String(opts.jsx.string()));
        }
        if let Ok(b) = crate::frontend::json::json_marshal(&compiler_options, &[]) {
            props.insert("compilerOptions".to_string(), b);
        }

        // Config file shape
        // PORT: Go `Raw.(*collections.OrderedMap[string, any])` is the
        // `CompilerOptionsValue::Map` form of `raw`.
        if let tsoptions::CompilerOptionsValue::Map(raw) = &command_line.raw {
            props.insert(
                "extends".to_string(),
                bool_telemetry(raw.contains_key("extends")),
            );
            props.insert(
                "files".to_string(),
                bool_telemetry(raw.contains_key("files")),
            );
            props.insert(
                "include".to_string(),
                bool_telemetry(raw.contains_key("include")),
            );
            props.insert(
                "exclude".to_string(),
                bool_telemetry(raw.contains_key("exclude")),
            );
        }

        lsproto::TelemetryEvent {
            project_info_telemetry_event: Some(lsproto::ProjectInfoTelemetryEvent {
                properties: props,
                measurements: Some(count_file_stats(
                    project.program.expect(NIL_DEREF).get_source_files(),
                )),
                ..Default::default()
            }),
            ..Default::default()
        }
    }
}

// Go: project/session.go:852 setTristate
pub fn set_tristate(m: &mut IndexMap<String, LspAny>, key: &str, v: Tristate) {
    if v == Tristate::True {
        m.insert(key.to_string(), LspAny::Bool(true));
    } else if v == Tristate::False {
        m.insert(key.to_string(), LspAny::Bool(false));
    }
}

// Go: project/session.go:860 boolTelemetry
pub fn bool_telemetry(v: bool) -> String {
    if v {
        return "true".to_string();
    }
    "false".to_string()
}

// Go: project/session.go:867 countFileStats
// PORT: Go returns `*lsproto.ProjectInfoTelemetryMeasurements`; the event
// field holds the value.
pub fn count_file_stats(
    source_files: &[Rc<crate::frontend::parser::ParsedSourceFile>],
) -> lsproto::ProjectInfoTelemetryMeasurements {
    let mut stats = lsproto::ProjectInfoTelemetryMeasurements::default();
    for sf in source_files {
        let size = sf.root.end() as f64;
        match sf.script_kind {
            ScriptKind::JS => {
                stats.js_file_count += 1.0;
                stats.js_file_size += size;
            }
            ScriptKind::JSX => {
                stats.jsx_file_count += 1.0;
                stats.jsx_file_size += size;
            }
            ScriptKind::TS => {
                if tspath::is_declaration_file_name(sf.file_name()) {
                    stats.dts_file_count += 1.0;
                    stats.dts_file_size += size;
                } else {
                    stats.ts_file_count += 1.0;
                    stats.ts_file_size += size;
                }
            }
            ScriptKind::TSX => {
                stats.tsx_file_count += 1.0;
                stats.tsx_file_size += size;
            }
            _ => {}
        }
    }
    stats
}

impl Session {
    // Go: project/session.go:894 Snapshot
    pub fn snapshot(&self) -> Rc<Snapshot> {
        self.snapshot.borrow().clone()
    }

    // Go: project/session.go:904 getSnapshot
    // getSnapshot flushes pending changes and updates the session's snapshot
    // if needed for the given request. When callerRef is true, the returned
    // snapshot has an extra reference for the caller (taken atomically under
    // snapshotMu), guaranteeing it stays alive until the caller calls Deref.
    pub fn get_snapshot(
        self: &Rc<Self>,
        ctx: &Context,
        request: ResourceRequest,
        caller_ref: bool,
    ) -> Rc<Snapshot> {
        self.cancel_scheduled_snapshot_update();

        let (file_changes, overlays, ata_changes, new_config) = self.flush_changes(ctx);
        let update_snapshot =
            !file_changes.is_empty() || !ata_changes.is_empty() || new_config.is_some();
        if update_snapshot {
            // If there are pending file changes, we need to update the snapshot.
            // Sending the requested URI ensures that the project for this URI is loaded.
            return self.update_snapshot(
                ctx,
                overlays,
                SnapshotChange {
                    reason: UpdateReason::REQUESTED_LANGUAGE_SERVICE_PENDING_CHANGES,
                    file_changes,
                    ata_changes,
                    new_config,
                    resource_request: request,
                    ..Default::default()
                },
                caller_ref,
            );
        }
        // If there are no pending file changes, we can try to use the current snapshot.
        let snapshot = self.snapshot.borrow().clone();
        let mut update_reason = UpdateReason::UNKNOWN;
        if !request.projects.is_empty() {
            update_reason = UpdateReason::REQUESTED_LANGUAGE_SERVICE_PROJECT_DIRTY;
        } else if request.project_tree.is_some() {
            update_reason = UpdateReason::REQUESTED_LOAD_PROJECT_TREE;
        } else if !request.auto_imports.0.is_empty() {
            update_reason = UpdateReason::REQUESTED_LANGUAGE_SERVICE_WITH_AUTO_IMPORTS;
        } else {
            for document in &request.documents {
                match snapshot.get_default_project(document) {
                    None => {
                        update_reason = UpdateReason::REQUESTED_LANGUAGE_SERVICE_PROJECT_NOT_LOADED;
                    }
                    Some(project) => {
                        if project.borrow().dirty {
                            update_reason = UpdateReason::REQUESTED_LANGUAGE_SERVICE_PROJECT_DIRTY;
                        }
                    }
                }
            }
            if update_reason == UpdateReason::UNKNOWN {
                for document in &request.configured_project_documents {
                    if snapshot.fs.is_open_file(&document.file_name()) {
                        match snapshot.get_default_project(document) {
                            None => {
                                update_reason =
                                    UpdateReason::REQUESTED_LANGUAGE_SERVICE_PROJECT_NOT_LOADED;
                            }
                            Some(project) => {
                                if project.borrow().dirty {
                                    update_reason =
                                        UpdateReason::REQUESTED_LANGUAGE_SERVICE_PROJECT_DIRTY;
                                }
                            }
                        }
                    } else {
                        update_reason = UpdateReason::REQUESTED_LANGUAGE_SERVICE_FOR_FILE_NOT_OPEN;
                    }
                }
            }
        }
        if update_reason == UpdateReason::UNKNOWN {
            if caller_ref {
                snapshot.ref_();
            }
            return snapshot;
        }

        self.update_snapshot(
            ctx,
            overlays,
            SnapshotChange {
                reason: update_reason,
                resource_request: request,
                ..Default::default()
            },
            caller_ref,
        )
    }

    // Go: project/session.go:975 getSnapshotAndDefaultProject
    // PORT: Go `project.GetProgram()` may be nil and `ls.NewLanguageService`
    // keeps it; the Rust language service needs a program, so a nil one
    // panics here (Go panics on first use).
    pub fn get_snapshot_and_default_project(
        self: &Rc<Self>,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
        caller_ref: bool,
    ) -> Result<(Rc<Snapshot>, Rc<RefCell<Project>>, ls::LanguageService), GoError> {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                documents: vec![uri.clone()],
                ..Default::default()
            },
            caller_ref,
        );
        let Some(project) = snapshot.get_default_project(uri) else {
            return Err(gostd::errors::errorf(
                format!("no project found for URI {}", uri),
                vec![],
            ));
        };
        let language_service = {
            let p = project.borrow();
            ls::new_language_service(
                p.config_file_path.clone(),
                p.program.expect(NIL_DEREF),
                snapshot.clone(),
                &uri.file_name(),
            )
        };
        Ok((snapshot, project, language_service))
    }

    // Go: project/session.go:988 GetLanguageService
    pub fn get_language_service(
        self: &Rc<Self>,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<ls::LanguageService, GoError> {
        let (_, _, language_service) =
            self.get_snapshot_and_default_project(ctx, uri, false /*callerRef*/)?;
        Ok(language_service)
    }

    // Go: project/session.go:996 GetLanguageServiceAndProjectsForFile
    // PORT: Go `[]ls.Project` is `Vec<Rc<dyn ls::Project>>`.
    pub fn get_language_service_and_projects_for_file(
        self: &Rc<Self>,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<
        (
            Rc<RefCell<Project>>,
            ls::LanguageService,
            Vec<Rc<dyn ls::Project>>,
        ),
        GoError,
    > {
        let (snapshot, project, default_ls) =
            self.get_snapshot_and_default_project(ctx, uri, false /*callerRef*/)?;
        // !!! TODO: sheetal:  Get other projects that contain the file with symlink
        let all_projects = snapshot.get_projects_containing_file(uri);
        Ok((project, default_ls, all_projects))
    }

    // Go: project/session.go:1006 GetProjectsForFile
    pub fn get_projects_for_file(
        self: &Rc<Self>,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<Vec<Rc<dyn ls::Project>>, GoError> {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                configured_project_documents: vec![uri.clone()],
                ..Default::default()
            },
            false, /*callerRef*/
        );

        // !!! TODO: sheetal:  Get other projects that contain the file with symlink
        let all_projects = snapshot.get_projects_containing_file(uri);
        Ok(all_projects)
    }

    // Go: project/session.go:1018 GetLanguageServicesForDocuments
    pub fn get_language_services_for_documents(
        self: &Rc<Self>,
        ctx: &Context,
        uris: &[lsproto::DocumentUri],
    ) -> Vec<ls::LanguageService> {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                documents: uris.to_vec(),
                ..Default::default()
            },
            false, /*callerRef*/
        );

        let mut active_file = String::new();
        if !uris.is_empty() {
            active_file = uris[0].file_name();
        }

        let projects = snapshot.project_collection.projects();
        let mut services: Vec<ls::LanguageService> = Vec::with_capacity(projects.len());
        for project in &projects {
            let project = project.borrow();
            let Some(program) = project.program else {
                continue;
            };

            services.push(ls::new_language_service(
                project.config_file_path.clone(),
                program,
                snapshot.clone(),
                &active_file,
            ));
        }
        services
    }

    // Go: project/session.go:1043 GetLanguageServiceForProjectWithFile
    // PORT: the Go server passes `p.(*project.Project)` (a type assertion on
    // an `ls.Project`). Only `Id()` of the argument is read, so the port
    // takes the `ls::Project` interface itself.
    pub fn get_language_service_for_project_with_file(
        self: &Rc<Self>,
        ctx: &Context,
        project: &dyn ls::Project,
        uri: &lsproto::DocumentUri,
    ) -> Option<ls::LanguageService> {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                projects: vec![project.id()],
                ..Default::default()
            },
            false, /*callerRef*/
        );
        // Ensure we have updated project
        let project = snapshot
            .project_collection
            .get_project_by_path(&project.id())?;
        let project = project.borrow();
        // if program doesnt contain this file any more ignore it
        if !project.has_file(&uri.file_name()) {
            return None;
        }
        Some(ls::new_language_service(
            project.config_file_path.clone(),
            project.program.expect(NIL_DEREF),
            snapshot.clone(),
            &uri.file_name(),
        ))
    }

    // Go: project/session.go:1064 WithSnapshotLoadingProjectTree
    // WithSnapshotLoadingProjectTree acquires a ref'd snapshot with the
    // requested project trees loaded, then calls fn. The snapshot stays alive
    // for the duration of fn.
    // PORT: Go `*collections.Set[tspath.Path]` is `Option<&FxHashSet<..>>`
    // (nil loads all project trees).
    pub fn with_snapshot_loading_project_tree(
        self: &Rc<Self>,
        ctx: &Context,
        requested_project_trees: Option<&FxHashSet<tspath::Path>>,
        fn_: &mut dyn FnMut(&Rc<Snapshot>),
    ) {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                project_tree: Some(ProjectTreeRequest {
                    referenced_projects: requested_project_trees.cloned(),
                }),
                ..Default::default()
            },
            true, /*callerRef*/
        );
        fn_(&snapshot);
        // Go: defer snapshot.Deref(s)
        Snapshot::deref(&snapshot, self);
    }

    // Go: project/session.go:1083 GetCurrentLanguageServiceWithAutoImports
    // GetCurrentLanguageServiceWithAutoImports flushes pending file changes, clones the
    // current snapshot with auto-import preparation for the given URI, then returns a
    // LanguageService for the default project. Use this only outside of request handling
    // (e.g. cache warming). For request handlers, use GetLanguageServiceWithAutoImports
    // with the request-level snapshot instead.
    pub fn get_current_language_service_with_auto_imports(
        self: &Rc<Self>,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<ls::LanguageService, GoError> {
        let snapshot = self.get_snapshot(
            ctx,
            ResourceRequest {
                documents: vec![uri.clone()],
                auto_imports: uri.clone(),
                ..Default::default()
            },
            false, /*callerRef*/
        );
        let Some(project) = snapshot.get_default_project(uri) else {
            return Err(gostd::errors::errorf(
                format!("no project found for URI {}", uri),
                vec![],
            ));
        };
        let project = project.borrow();
        Ok(ls::new_language_service(
            project.config_file_path.clone(),
            project.program.expect(NIL_DEREF),
            snapshot.clone(),
            &uri.file_name(),
        ))
    }

    // Go: project/session.go:1105 WithLanguageServiceAndSnapshot
    // WithLanguageServiceAndSnapshot synchronously acquires a ref'd snapshot and
    // creates a language service for the given URI. fn receives both the language
    // service and the backing snapshot so it can clone the snapshot (e.g. to
    // enable auto-imports). The snapshot is kept alive until the async work
    // completes.
    //
    // Only use this method when the callback needs direct access to the snapshot.
    // For handlers that only need a LanguageService, use GetLanguageService
    // directly—language services continue to work even after their backing
    // snapshot has been disposed.
    // PORT: Go `(func() error, error)` is `Result<Option<..>, GoError>`
    // (`Ok(None)` is a nil function with a nil error). `fn` takes the
    // language service by value so the async work can own it.
    pub fn with_language_service_and_snapshot(
        self: &Rc<Self>,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
        fn_: impl FnOnce(
            ls::LanguageService,
            Rc<Snapshot>,
        ) -> Result<Option<Box<dyn FnOnce() -> Result<(), GoError>>>, GoError>,
    ) -> Result<Option<Box<dyn FnOnce() -> Result<(), GoError>>>, GoError> {
        let (snapshot, _, language_service) =
            self.get_snapshot_and_default_project(ctx, uri, true /*callerRef*/)?;
        let async_work = fn_(language_service, snapshot.clone());
        let async_work = match async_work {
            Ok(Some(async_work)) => async_work,
            Ok(None) => {
                Snapshot::deref(&snapshot, self);
                return Ok(None);
            }
            Err(err) => {
                Snapshot::deref(&snapshot, self);
                return Err(err);
            }
        };
        let s = self.clone();
        Ok(Some(Box::new(move || {
            let result = async_work();
            // Go: defer snapshot.Deref(s)
            Snapshot::deref(&snapshot, &s);
            result
        })))
    }

    // Go: project/session.go:1129 GetLanguageServiceWithAutoImports
    // GetLanguageServiceWithAutoImports clones the given snapshot with auto-import
    // preparation for the given URI, without flushing pending file changes.
    // The cloned snapshot will be adopted as the session's current snapshot in the background
    // if other changes haven't been adopted in the meantime.
    pub fn get_language_service_with_auto_imports(
        self: &Rc<Self>,
        ctx: &Context,
        base_snapshot: &Rc<Snapshot>,
        uri: &lsproto::DocumentUri,
    ) -> Result<ls::LanguageService, GoError> {
        let change = SnapshotChange {
            reason: UpdateReason::REQUESTED_LANGUAGE_SERVICE_WITH_AUTO_IMPORTS,
            resource_request: ResourceRequest {
                documents: vec![uri.clone()],
                auto_imports: uri.clone(),
                ..Default::default()
            },
            ..Default::default()
        };
        let new_snapshot =
            Snapshot::clone_(base_snapshot, ctx, change, &base_snapshot.fs.overlays, self);

        let Some(project) = new_snapshot.get_default_project(uri) else {
            // Clone's initial ref (1) is released since we won't use this snapshot.
            Snapshot::deref(&new_snapshot, self);
            return Err(gostd::errors::errorf(
                format!("no project found for URI {}", uri),
                vec![],
            ));
        };

        // The clone's initial ref (1) is transferred to adoptSnapshotChange,
        // which will either promote it as the session's current snapshot or
        // release it if the session has moved on.
        let s = self.clone();
        let task_base_snapshot = base_snapshot.clone();
        let task_new_snapshot = new_snapshot.clone();
        self.background_queue
            .enqueue(&self.background_ctx, move |_ctx| {
                s.adopt_snapshot_change(&task_base_snapshot, &task_new_snapshot);
            });

        let project = project.borrow();
        Ok(ls::new_language_service(
            project.config_file_path.clone(),
            project.program.expect(NIL_DEREF),
            new_snapshot.clone(),
            &uri.file_name(),
        ))
    }

    // Go: project/session.go:1160 adoptSnapshotChange
    // adoptSnapshotChange promotes a cloned snapshot as the session's current
    // snapshot so future requests benefit from the work already done. If the
    // session has moved on, the snapshot is discarded; the next request needing
    // auto-imports will redo the work on the latest snapshot.
    pub fn adopt_snapshot_change(
        self: &Rc<Self>,
        base_snapshot: &Rc<Snapshot>,
        new_snapshot: &Rc<Snapshot>,
    ) {
        let old_snapshot = self.snapshot.borrow().clone();
        if Rc::ptr_eq(&old_snapshot, base_snapshot) {
            // Session hasn't moved on; adopt the new snapshot. The clone's initial
            // ref is transferred to become the session's ref for its current snapshot.
            *self.snapshot.borrow_mut() = new_snapshot.clone();
            if self.options.logging_enabled {
                self.logger.logf(&format!(
                    "Adopted snapshot {} (parent {}) as current session snapshot (replacing {})",
                    new_snapshot.id, new_snapshot.parent_id, old_snapshot.id
                ));
                self.logger.log(&new_snapshot.builder_logs.string());
            }
            Snapshot::deref(&old_snapshot, self);
        } else {
            // Session has moved on to a newer snapshot; discard this one.
            // Release the clone's initial ref. If a handler is still using
            // the snapshot, its own ref keeps it alive.
            if self.options.logging_enabled {
                self.logger.logf(&format!(
                    "Discarded snapshot {} (parent {}); session has moved on to snapshot {}",
                    new_snapshot.id, new_snapshot.parent_id, old_snapshot.id
                ));
                let logs = new_snapshot.builder_logs.string();
                if !logs.is_empty() {
                    self.logger.logf(&format!(
                        "--- Discarded snapshot {} builder logs (NOT adopted) ---",
                        new_snapshot.id
                    ));
                    self.logger.log(&logs);
                    self.logger.logf(&format!(
                        "--- End discarded snapshot {} builder logs ---",
                        new_snapshot.id
                    ));
                }
            }
            Snapshot::deref(new_snapshot, self);
        }
    }

    // Go: project/session.go:1190 UpdateSnapshot
    // PORT: Go has `UpdateSnapshot` and `updateSnapshot`; the exported one
    // ends in `_exported` (PORTING "Names").
    pub fn update_snapshot_exported(
        self: &Rc<Self>,
        ctx: &Context,
        overlays: IndexMap<tspath::Path, Rc<Overlay>>,
        change: SnapshotChange,
    ) {
        self.update_snapshot(ctx, overlays, change, false);
    }

    // Go: project/session.go:1198 updateSnapshotRef
    // updateSnapshotRef is like UpdateSnapshot but returns the created snapshot
    // with an extra reference for the caller. The ref is taken atomically with
    // the snapshot assignment under snapshotMu, so the snapshot is guaranteed
    // to be alive when returned. The caller must call snapshot.Deref(s) when done.
    pub fn update_snapshot_ref(
        self: &Rc<Self>,
        ctx: &Context,
        overlays: IndexMap<tspath::Path, Rc<Overlay>>,
        change: SnapshotChange,
    ) -> Rc<Snapshot> {
        self.update_snapshot(ctx, overlays, change, true)
    }

    // Go: project/session.go:1202 updateSnapshot
    // PORT: Go passes `change` by value to `Clone` and keeps its own copy
    // for the background task, so the port clones it.
    pub fn update_snapshot(
        self: &Rc<Self>,
        ctx: &Context,
        overlays: IndexMap<tspath::Path, Rc<Overlay>>,
        change: SnapshotChange,
        caller_ref: bool,
    ) -> Rc<Snapshot> {
        let old_snapshot = self.snapshot.borrow().clone();
        let new_snapshot = Snapshot::clone_(&old_snapshot, ctx, change.clone(), &overlays, self);
        *self.snapshot.borrow_mut() = new_snapshot.clone();
        if caller_ref {
            new_snapshot.ref_();
        }
        if !Rc::ptr_eq(&new_snapshot, &old_snapshot) {
            // Release the session's reference to the old snapshot. The new snapshot's
            // clone ref (1) is transferred to become the session's ref for its current
            // snapshot. Other holders (e.g. active handlers) keep the old snapshot alive
            // via their own refs until they complete.
            Snapshot::deref(&old_snapshot, self);
        }

        // Enqueue ATA updates if needed
        if self.typings_installer.borrow().is_some() && !self.config().is_ata_disabled() {
            self.trigger_ata_for_updated_projects(&new_snapshot);
        }

        // Enqueue logging, watch updates, and diagnostic refresh tasks
        // !!! userPreferences/configuration updates
        let s = self.clone();
        let task_old_snapshot = old_snapshot.clone();
        let task_new_snapshot = new_snapshot.clone();
        self.background_queue
            .enqueue(&self.background_ctx, move |ctx| {
                let old_snapshot = &task_old_snapshot;
                let new_snapshot = &task_new_snapshot;
                if s.options.logging_enabled {
                    s.logger.logf(&format!(
                        "Adopted snapshot {} (parent {}) as current session snapshot (replacing {})",
                        new_snapshot.id, new_snapshot.parent_id, old_snapshot.id
                    ));
                    s.logger.log(&new_snapshot.builder_logs.string());
                    s.log_project_changes(old_snapshot, new_snapshot);
                    s.log_runtime_metrics();
                    s.logger.log("");
                }
                if s.options.watch_enabled {
                    if let Err(err) = s.update_watches(old_snapshot, new_snapshot) {
                        if s.options.logging_enabled {
                            s.logger.log(&err.error());
                        }
                    }
                }
                s.publish_program_diagnostics(old_snapshot, new_snapshot);
                s.send_project_info_telemetry_for_new_projects(old_snapshot, new_snapshot);
                s.warm_auto_import_cache(ctx, &change, old_snapshot, new_snapshot);
            });

        new_snapshot
    }

    // Go: project/session.go:1249 WaitForBackgroundTasks
    // WaitForBackgroundTasks waits for all background tasks to complete.
    // This is intended to be used only for testing purposes.
    // PORT: `Queue::wait` runs `gostd::local::run_pending` until the
    // queue's tasks have finished, including the debounced ones, which
    // count until their timer has run. The auto-import warm clone is idle work
    // (see `warm_auto_import_cache`); Go waits for it as part of its task,
    // so this runs the idle work too.
    pub fn wait_for_background_tasks(&self) {
        self.cancel_idle_cache_clean();
        self.background_queue.wait();
        while gostd::local::run_idle() {
            self.background_queue.wait();
        }
    }
}

// Go: project/session.go:1254 updateWatch
// PORT: Go `*WatchedFiles[T]` arguments are `Option<&WatchedFiles<T>>`.
// Go `logger != nil` compares the interface, which always holds the
// session logger (a nil `*logger` for the nop logger), so it is always
// true; the nop logger is `None` here and its calls do nothing.
pub fn update_watch<T>(
    ctx: &Context,
    session: &Session,
    logger: &Option<Rc<dyn logging::Logger>>,
    old_watcher: Option<&WatchedFiles<T>>,
    new_watcher: Option<&WatchedFiles<T>>,
) -> Vec<GoError> {
    let mut errors: Vec<GoError> = Vec::new();
    if let Some(new_watcher) = new_watcher {
        let w = new_watcher.watchers();
        let mut watchers = w.workspace_watchers.clone();
        watchers.extend(w.outside_workspace_watchers.iter().cloned());
        if !watchers.is_empty() {
            let mut new_watchers: IndexMap<WatcherID, lsproto::FileSystemWatcher> =
                IndexMap::default();
            for (i, watcher) in watchers.iter().enumerate() {
                let glob_id = WatcherID(format!("{}.{}", w.watcher_id, i));
                if session.watches.acquire(watcher, glob_id.clone()) {
                    new_watchers.insert(glob_id, watcher.clone());
                }
            }
            let mut watch_errors: Vec<GoError> = Vec::new();
            for (id, watcher) in &new_watchers {
                // Create a fresh timeout per client call so earlier calls
                // don't consume the deadline for later ones.
                let (call_ctx, call_cancel) =
                    gostd::context::with_timeout(ctx, WATCH_REQUEST_TIMEOUT);
                let err = session.client.as_ref().expect(NIL_DEREF).watch_files(
                    &call_ctx,
                    id.clone(),
                    std::slice::from_ref(watcher),
                );
                call_cancel();
                match err {
                    Err(err) => watch_errors.push(err),
                    Ok(()) => {
                        if old_watcher.is_none() {
                            logger.log(&format!("Added new watch: {}", id));
                        } else {
                            logger.log(&format!("Updated watch: {}", id));
                        }
                        logger.log(&format!("\t{}", file_system_watcher_glob_string(watcher)));
                        logger.log("");
                    }
                }
            }
            if !watch_errors.is_empty() {
                // Roll back ALL newly-acquired watchers on any failure to keep
                // refcounts clean. On retry, Acquire will see them as new again.
                // Re-registering an already-registered watcher with the client
                // is harmless (registerCapability with the same ID replaces it).
                for watcher in new_watchers.values() {
                    session.watches.release(watcher);
                }
                session.watches.mark_pending(w.watcher_id.clone());
                errors.extend(watch_errors);
            } else {
                session.watches.clear_pending(&w.watcher_id);
            }
            if !w.ignored_paths.is_empty() {
                logger.logf(&format!(
                    "{} paths ineligible for watching",
                    w.ignored_paths.len()
                ));
                if logger.is_verbose() {
                    // PORT: Go map order is random (log text only).
                    for path in &w.ignored_paths {
                        logger.log(&format!("\t{}", path));
                    }
                }
            }
        }
    }
    if let Some(old_watcher) = old_watcher {
        let w = old_watcher.watchers();
        let mut watchers = w.workspace_watchers.clone();
        watchers.extend(w.outside_workspace_watchers.iter().cloned());
        if !watchers.is_empty() {
            let mut removed_ids: Vec<WatcherID> = Vec::new();
            for watcher in &watchers {
                let (id, removed) = session.watches.release(watcher);
                if removed {
                    removed_ids.push(id);
                }
            }
            for id in removed_ids {
                let (call_ctx, call_cancel) =
                    gostd::context::with_timeout(ctx, WATCH_REQUEST_TIMEOUT);
                let err = session
                    .client
                    .as_ref()
                    .expect(NIL_DEREF)
                    .unwatch_files(&call_ctx, id.clone());
                call_cancel();
                match err {
                    Err(err) => errors.push(err),
                    Ok(()) => {
                        if new_watcher.is_none() {
                            logger.log(&format!("Removed watch: {}", id));
                        }
                    }
                }
            }
        }
    }
    errors
}

impl Session {
    // Go: project/session.go:1334 updateWatches
    // PORT: the Go closures all append to `errors`, so it is a `RefCell`.
    // Go ranges over the config map (random order); the port uses the
    // `FxHashMap` order, which only changes the order of watch requests.
    pub fn update_watches(
        &self,
        old_snapshot: &Rc<Snapshot>,
        new_snapshot: &Rc<Snapshot>,
    ) -> Result<(), GoError> {
        let errors: RefCell<Vec<GoError>> = RefCell::new(Vec::new());
        let start = Instant::now();
        let ctx = self.background_ctx.clone();
        crate::frontend::core_ls_ext::diff_maps_func(
            &old_snapshot.config_file_registry.configs,
            &new_snapshot.config_file_registry.configs,
            |a: &Rc<RefCell<ConfigFileEntry>>, b: &Rc<RefCell<ConfigFileEntry>>| {
                WatchedFiles::id(a.borrow().root_files_watch.as_deref())
                    == WatchedFiles::id(b.borrow().root_files_watch.as_deref())
            },
            Some(
                &mut |_: &tspath::Path, added_entry: &Rc<RefCell<ConfigFileEntry>>| {
                    let added = update_watch(
                        &ctx,
                        self,
                        &self.logger,
                        None,
                        added_entry.borrow().root_files_watch.as_deref(),
                    );
                    errors.borrow_mut().extend(added);
                },
            ),
            Some(
                &mut |_: &tspath::Path, removed_entry: &Rc<RefCell<ConfigFileEntry>>| {
                    let removed = update_watch(
                        &ctx,
                        self,
                        &self.logger,
                        removed_entry.borrow().root_files_watch.as_deref(),
                        None,
                    );
                    errors.borrow_mut().extend(removed);
                },
            ),
            Some(&mut |_: &tspath::Path,
                       old_entry: &Rc<RefCell<ConfigFileEntry>>,
                       new_entry: &Rc<RefCell<ConfigFileEntry>>| {
                let changed = update_watch(
                    &ctx,
                    self,
                    &self.logger,
                    old_entry.borrow().root_files_watch.as_deref(),
                    new_entry.borrow().root_files_watch.as_deref(),
                );
                errors.borrow_mut().extend(changed);
            }),
        );
        // Retry config watchers whose IDs didn't change but whose previous registration failed.
        for (path, new_entry) in &new_snapshot.config_file_registry.configs {
            if let Some(old_entry) = old_snapshot.config_file_registry.configs.get(path) {
                let new_id = WatchedFiles::id(new_entry.borrow().root_files_watch.as_deref());
                if WatchedFiles::id(old_entry.borrow().root_files_watch.as_deref()) == new_id
                    && self.watches.is_pending(&new_id)
                {
                    let retried = update_watch(
                        &ctx,
                        self,
                        &self.logger,
                        None,
                        new_entry.borrow().root_files_watch.as_deref(),
                    );
                    errors.borrow_mut().extend(retried);
                }
            }
        }

        crate::frontend::core_ls_ext::diff_ordered_maps(
            &old_snapshot.project_collection.projects_by_path(),
            &new_snapshot.project_collection.projects_by_path(),
            |_: &tspath::Path, added_project| {
                let added_project = added_project.borrow();
                let program_files = update_watch(
                    &ctx,
                    self,
                    &self.logger,
                    None,
                    added_project.program_files_watch.as_deref(),
                );
                errors.borrow_mut().extend(program_files);
                let typings = update_watch(
                    &ctx,
                    self,
                    &self.logger,
                    None,
                    added_project.typings_watch.as_deref(),
                );
                errors.borrow_mut().extend(typings);
            },
            |_: &tspath::Path, removed_project| {
                let removed_project = removed_project.borrow();
                let program_files = update_watch(
                    &ctx,
                    self,
                    &self.logger,
                    removed_project.program_files_watch.as_deref(),
                    None,
                );
                errors.borrow_mut().extend(program_files);
                let typings = update_watch(
                    &ctx,
                    self,
                    &self.logger,
                    removed_project.typings_watch.as_deref(),
                    None,
                );
                errors.borrow_mut().extend(typings);
            },
            |_: &tspath::Path, old_project, new_project| {
                let old_project = old_project.borrow();
                let new_project = new_project.borrow();
                if WatchedFiles::id(old_project.program_files_watch.as_deref())
                    != WatchedFiles::id(new_project.program_files_watch.as_deref())
                {
                    let changed = update_watch(
                        &ctx,
                        self,
                        &self.logger,
                        old_project.program_files_watch.as_deref(),
                        new_project.program_files_watch.as_deref(),
                    );
                    errors.borrow_mut().extend(changed);
                } else if self.watches.is_pending(&WatchedFiles::id(
                    new_project.program_files_watch.as_deref(),
                )) {
                    let retried = update_watch(
                        &ctx,
                        self,
                        &self.logger,
                        None,
                        new_project.program_files_watch.as_deref(),
                    );
                    errors.borrow_mut().extend(retried);
                }
                if WatchedFiles::id(old_project.typings_watch.as_deref())
                    != WatchedFiles::id(new_project.typings_watch.as_deref())
                {
                    let changed = update_watch(
                        &ctx,
                        self,
                        &self.logger,
                        old_project.typings_watch.as_deref(),
                        new_project.typings_watch.as_deref(),
                    );
                    errors.borrow_mut().extend(changed);
                } else if self
                    .watches
                    .is_pending(&WatchedFiles::id(new_project.typings_watch.as_deref()))
                {
                    let retried = update_watch(
                        &ctx,
                        self,
                        &self.logger,
                        None,
                        new_project.typings_watch.as_deref(),
                    );
                    errors.borrow_mut().extend(retried);
                }
            },
        );

        if WatchedFiles::id(old_snapshot.auto_imports_watch.as_deref())
            != WatchedFiles::id(new_snapshot.auto_imports_watch.as_deref())
        {
            let changed = update_watch(
                &ctx,
                self,
                &self.logger,
                old_snapshot.auto_imports_watch.as_deref(),
                new_snapshot.auto_imports_watch.as_deref(),
            );
            errors.borrow_mut().extend(changed);
        } else if self.watches.is_pending(&WatchedFiles::id(
            new_snapshot.auto_imports_watch.as_deref(),
        )) {
            let retried = update_watch(
                &ctx,
                self,
                &self.logger,
                None,
                new_snapshot.auto_imports_watch.as_deref(),
            );
            errors.borrow_mut().extend(retried);
        }

        let errors = errors.into_inner();
        if !errors.is_empty() {
            // Go: fmt.Errorf("errors updating watches: %v", errors) (no %w).
            let texts: Vec<String> = errors.iter().map(|err| err.error()).collect();
            return Err(gostd::errors::errorf(
                format!("errors updating watches: [{}]", texts.join(" ")),
                vec![],
            ));
        } else if self.options.logging_enabled {
            // PORT: `%v` of a Go `time.Duration`; log text only.
            self.logger
                .log(&format!("Updated watches in {:?}", start.elapsed()));
        }
        Ok(())
    }

    // Go: project/session.go:1410 Close
    pub fn close(&self) {
        // Cancel any pending scheduled snapshot update
        self.cancel_scheduled_snapshot_update();
        // Cancel any pending diagnostics refresh
        self.cancel_diagnostics_refresh();
        // Cancel any pending auto-import cache warming
        self.cancel_warm_auto_import_cache();
        // Cancel any pending idle cache clean
        self.cancel_idle_cache_clean();
        // Cancel periodic performance telemetry
        self.stop_performance_telemetry();
        self.background_queue.close();
    }

    // Go: project/session.go:1424 flushChanges
    // PORT: Go `*lsutil.UserPreferences` is `Option<lsutil::UserPreferences>`.
    pub fn flush_changes(
        &self,
        ctx: &Context,
    ) -> (
        FileChangeSummary,
        IndexMap<tspath::Path, Rc<Overlay>>,
        FxHashMap<tspath::Path, Rc<ATAStateChange>>,
        Option<lsutil::UserPreferences>,
    ) {
        let pending_ata_changes = std::mem::take(&mut *self.pending_ata_changes.borrow_mut());
        let (file_changes, overlays) = self.flush_changes_locked(ctx);
        let mut new_prefs: Option<lsutil::UserPreferences> = None;
        if self.pending_user_config_changes.get() {
            let p = self.workspace_user_preferences.borrow().clone();
            new_prefs = Some(p);
        }
        self.pending_user_config_changes.set(false);
        (file_changes, overlays, pending_ata_changes, new_prefs)
    }

    // Go: project/session.go:1444 flushChangesLocked
    // flushChangesLocked should only be called with s.pendingFileChangesMu held.
    pub fn flush_changes_locked(
        &self,
        _ctx: &Context,
    ) -> (FileChangeSummary, IndexMap<tspath::Path, Rc<Overlay>>) {
        if self.pending_file_changes.borrow().is_empty() {
            return (FileChangeSummary::default(), self.fs.overlays());
        }

        let start = Instant::now();
        let pending_file_changes = std::mem::take(&mut *self.pending_file_changes.borrow_mut());
        let (changes, overlays) = self.fs.process_changes(&pending_file_changes);
        if self.options.logging_enabled {
            // PORT: `%v` of a Go `time.Duration`; log text only.
            self.logger.log(&format!(
                "Processed {} file changes in {:?}",
                pending_file_changes.len(),
                start.elapsed()
            ));
        }
        // Go: s.pendingFileChanges = nil (taken above)
        (changes, overlays)
    }

    // Go: project/session.go:1459 logProjectChanges
    // logProjectChanges logs information about projects that have changed between snapshots
    pub fn log_project_changes(&self, old_snapshot: &Rc<Snapshot>, new_snapshot: &Rc<Snapshot>) {
        let logged_project_changes = Cell::new(false);
        let log_project = |project: &Rc<RefCell<Project>>| {
            let mut builder = String::new();
            project.borrow().print(
                self.logger.is_verbose(), /*writeFileNames*/
                self.logger.is_verbose(), /*writeFileExplanation*/
                &mut builder,
            );
            self.logger.log(&builder);
            logged_project_changes.set(true);
        };
        crate::frontend::core_ls_ext::diff_ordered_maps(
            &old_snapshot.project_collection.projects_by_path(),
            &new_snapshot.project_collection.projects_by_path(),
            |_path: &tspath::Path, added_project| {
                // New project added
                log_project(added_project);
            },
            |_path: &tspath::Path, removed_project| {
                // Project removed
                self.logger.logf(&format!(
                    "\nProject '{}' removed\n{}",
                    removed_project.borrow().name(),
                    HR
                ));
            },
            |_path: &tspath::Path, _old_project, new_project| {
                // Project updated
                if new_project.borrow().program_update_kind == ProgramUpdateKind::NEW_FILES {
                    log_project(new_project);
                }
            },
        );

        if logged_project_changes.get() || self.logger.is_verbose() {
            self.log_cache_stats(new_snapshot);
        }
    }
}

// Go: project/session.go:1491 runtimeMetricsSamples
// PORT: Go `sync.OnceValue` over `metrics.All()`, keeping the `/memory/`
// and `/gc/` metrics. `metrics.All()` describes the Go runtime; this
// runtime has no Go metrics, so the list is empty (log text only).
fn runtime_metrics_samples() -> Vec<MetricsSample> {
    let descs: Vec<&'static str> = Vec::new();
    let mut samples: Vec<MetricsSample> = Vec::new();
    for name in descs {
        if name.starts_with("/memory/") || name.starts_with("/gc/") {
            samples.push(MetricsSample {
                name,
                ..Default::default()
            });
        }
    }
    samples
}

impl Session {
    // Go: project/session.go:1503 logRuntimeMetrics
    // PORT: log text only. The sample list is empty (see
    // `runtime_metrics_samples`), so `metrics.Read` is not called; the log
    // keeps the header line.
    pub fn log_runtime_metrics(&self) {
        let samples = runtime_metrics_samples();
        // Go: gometrics.Read(samples) (skipped; no Go runtime metrics)

        let mut builder = String::new();
        builder.push_str("\n======== Runtime Metrics ========");
        for sample in &samples {
            match sample.value {
                MetricsValue::Uint64(v) => {
                    builder.push_str(&format!("\n{} = {}", sample.name, v));
                }
                MetricsValue::Float64(v) => {
                    builder.push_str(&format!("\n{} = {:.6}", sample.name, v));
                }
                MetricsValue::Float64Histogram => {
                    // Skip histograms for log readability
                }
                MetricsValue::Bad => {}
            }
        }
        self.logger.log(&builder);
    }

    // Go: project/session.go:1522 logCacheStats
    pub fn log_cache_stats(&self, snapshot: &Rc<Snapshot>) {
        let mut parse_cache_size = 0;
        let mut extended_config_count = 0;
        if self.logger.is_verbose() {
            for _ in self.parse_cache.entries.borrow().iter() {
                parse_cache_size += 1;
            }
            for _ in self.extended_config_cache.entries.borrow().iter() {
                extended_config_count += 1;
            }
        }
        self.logger.log("\n======== Cache Statistics ========");
        self.logger.logf(&format!(
            "Open file count:   {:6}",
            snapshot.fs.overlays.len()
        ));
        self.logger.logf(&format!(
            "Cached disk files: {:6}",
            snapshot.fs.disk_files.len()
        ));
        self.logger.logf(&format!(
            "Realpath aliases:  {:6}",
            snapshot.fs.node_modules_realpath_aliases.len()
        ));
        self.logger.logf(&format!(
            "Project count:     {:6}",
            snapshot.project_collection.projects().len()
        ));
        self.logger.logf(&format!(
            "Config count:      {:6}",
            snapshot.config_file_registry.configs.len()
        ));
        if self.logger.is_verbose() {
            self.logger.logf(&format!(
                "Parse cache size:           {:6}",
                parse_cache_size
            ));
            self.logger.logf(&format!(
                "Program count:              {:6}",
                self.program_counter.len()
            ));
            self.logger.logf(&format!(
                "Extended config cache size: {:6}",
                extended_config_count
            ));

            self.logger.log("Auto Imports:");
            let auto_import_stats = snapshot
                .auto_import_registry()
                .expect(NIL_DEREF)
                .get_cache_stats();
            self.logger.logf(&format!(
                "\tUnique packages (by realpath): {}",
                auto_import_stats.unique_package_count
            ));
            if !auto_import_stats.project_buckets.is_empty() {
                self.logger.log("\tProject buckets:");
                for bucket in &auto_import_stats.project_buckets {
                    self.logger.logf(&format!(
                        "\t\t{}{}:",
                        bucket.path,
                        if bucket.state.dirty() { " (dirty)" } else { "" }
                    ));
                    self.logger
                        .logf(&format!("\t\t\tFiles: {}", bucket.file_count));
                    self.logger
                        .logf(&format!("\t\t\tExports: {}", bucket.export_count));
                }
            }
            if !auto_import_stats.node_modules_buckets.is_empty() {
                self.logger.log("\tnode_modules buckets:");
                for bucket in &auto_import_stats.node_modules_buckets {
                    self.logger.logf(&format!(
                        "\t\t{}{}:",
                        bucket.path,
                        if bucket.state.dirty() { " (dirty)" } else { "" }
                    ));
                    // PORT: Go map order is random (log text only).
                    if let Some(dirty_packages) = bucket.state.dirty_packages_exported() {
                        for package_name in dirty_packages {
                            self.logger
                                .logf(&format!("\t\t\tNeeds granular update: {}", package_name));
                        }
                    }
                    if let Some(dependency_names) = &bucket.dependency_names {
                        self.logger.logf(&format!(
                            "\t\t\tCollected packages: {}",
                            dependency_names.len()
                        ));
                    } else {
                        self.logger
                            .logf("\t\t\tCollected packages: all, due to no package.json!");
                    }
                    // Go: bucket.PackageNames.Len() (0 for a nil set)
                    self.logger.logf(&format!(
                        "\t\t\tTotal packages: {}",
                        bucket.package_names.as_ref().map_or(0, |names| names.len())
                    ));
                    self.logger
                        .logf(&format!("\t\t\tFiles: {}", bucket.file_count));
                    self.logger
                        .logf(&format!("\t\t\tExports: {}", bucket.export_count));
                    match bucket.state.recursive_search_packages_exported() {
                        None => {
                            self.logger.log("\t\t\tRecursive search: all");
                        }
                        Some(packages) if !packages.is_empty() => {
                            self.logger.logf(&format!(
                                "\t\t\tRecursive search: {} packages",
                                packages.len()
                            ));
                        }
                        Some(_) => {
                            self.logger.log("\t\t\tRecursive search: none");
                        }
                    }
                }
            }
        }
    }

    // Go: project/session.go:1588 refreshInlayHintsIfNeeded
    pub fn refresh_inlay_hints_if_needed(
        &self,
        old_prefs: &lsutil::UserPreferences,
        new_prefs: &lsutil::UserPreferences,
    ) {
        if old_prefs.inlay_hints != new_prefs.inlay_hints {
            if let Err(err) = self
                .client
                .as_ref()
                .expect(NIL_DEREF)
                .refresh_inlay_hints(&self.background_ctx)
            {
                if self.options.logging_enabled {
                    self.logger
                        .logf(&format!("Error refreshing inlay hints: {}", err.error()));
                }
            }
        }
    }

    // Go: project/session.go:1596 refreshCodeLensIfNeeded
    pub fn refresh_code_lens_if_needed(
        &self,
        old_prefs: &lsutil::UserPreferences,
        new_prefs: &lsutil::UserPreferences,
    ) {
        if old_prefs.code_lens != new_prefs.code_lens {
            if let Err(err) = self
                .client
                .as_ref()
                .expect(NIL_DEREF)
                .refresh_code_lens(&self.background_ctx)
            {
                if self.options.logging_enabled {
                    self.logger
                        .logf(&format!("Error refreshing code lens: {}", err.error()));
                }
            }
        }
    }

    // Go: project/session.go:1604 refreshDiagnosticsIfNeeded
    pub fn refresh_diagnostics_if_needed(
        self: &Rc<Self>,
        old_prefs: &lsutil::UserPreferences,
        new_prefs: &lsutil::UserPreferences,
    ) {
        if old_prefs.custom_config_file_name != new_prefs.custom_config_file_name {
            self.schedule_diagnostics_refresh();
        }
    }

    // Go: project/session.go:1610 refreshATAIfNeeded
    pub fn refresh_ata_if_needed(
        self: &Rc<Self>,
        old_prefs: &lsutil::UserPreferences,
        new_prefs: &lsutil::UserPreferences,
    ) {
        if old_prefs.is_ata_disabled() && !new_prefs.is_ata_disabled() {
            // ATA was re-enabled; schedule a diagnostics refresh so the next snapshot update
            // re-triggers ATA for existing projects with the new setting.
            self.schedule_diagnostics_refresh();
        }
    }

    // Go: project/session.go:1618 publishProgramDiagnostics
    pub fn publish_program_diagnostics(
        &self,
        old_snapshot: &Rc<Snapshot>,
        new_snapshot: &Rc<Snapshot>,
    ) {
        if !self.options.push_diagnostics_enabled {
            return;
        }

        let ctx = self.background_ctx.clone();
        let old_projects = old_snapshot.project_collection.projects_by_path();
        let new_projects = new_snapshot.project_collection.projects_by_path();
        let old_open_projects = old_snapshot
            .project_collection
            .get_open_configured_projects();
        let new_open_projects = new_snapshot
            .project_collection
            .get_open_configured_projects();
        crate::frontend::core_ls_ext::diff_ordered_maps(
            &old_projects,
            &new_projects,
            |config_file_path: &tspath::Path, added_project| {
                if !should_publish_program_diagnostics(&added_project.borrow(), new_snapshot.id())
                    || !new_open_projects.contains(config_file_path)
                {
                    return;
                }
                let diagnostics = added_project.borrow().get_project_diagnostics(&ctx);
                self.publish_project_diagnostics(
                    &ctx,
                    config_file_path,
                    &diagnostics,
                    &new_snapshot.converters,
                );
            },
            |config_file_path: &tspath::Path, removed_project| {
                if removed_project.borrow().kind != Kind::CONFIGURED {
                    return;
                }
                self.publish_project_diagnostics(
                    &ctx,
                    config_file_path,
                    &[],
                    &old_snapshot.converters,
                );
            },
            |config_file_path: &tspath::Path, _old_project, new_project| {
                if !should_publish_program_diagnostics(&new_project.borrow(), new_snapshot.id())
                    || !new_open_projects.contains(config_file_path)
                {
                    return;
                }
                let diagnostics = new_project.borrow().get_project_diagnostics(&ctx);
                self.publish_project_diagnostics(
                    &ctx,
                    config_file_path,
                    &diagnostics,
                    &new_snapshot.converters,
                );
            },
        );
        // Sync diagnostics for projects whose open-file state changed without a program update.
        for (config_file_path, new_project) in &new_projects {
            if new_project.borrow().kind != Kind::CONFIGURED {
                continue;
            }
            if !old_projects.contains_key(config_file_path) {
                continue; // Handled by added project case above
            }
            let old_project = old_projects.get(config_file_path);
            let new_has_open_files = new_open_projects.contains(config_file_path);
            let old_has_open_files = old_open_projects.contains(config_file_path);
            if new_has_open_files
                && !old_has_open_files
                && (old_project.is_some_and(|old_project| Rc::ptr_eq(new_project, old_project))
                    || !should_publish_program_diagnostics(
                        &new_project.borrow(),
                        new_snapshot.id(),
                    ))
            {
                // Project reopened without a program update
                let diagnostics = new_project.borrow().get_project_diagnostics(&ctx);
                self.publish_project_diagnostics(
                    &ctx,
                    config_file_path,
                    &diagnostics,
                    &new_snapshot.converters,
                );
            } else if !new_has_open_files && old_has_open_files {
                // Project closed
                self.publish_project_diagnostics(
                    &ctx,
                    config_file_path,
                    &[],
                    &new_snapshot.converters,
                );
            }
        }
    }
}

// Go: project/session.go:1672 shouldPublishProgramDiagnostics
pub fn should_publish_program_diagnostics(p: &Project, snapshot_id: u64) -> bool {
    if p.kind != Kind::CONFIGURED || p.program.is_none() || p.program_last_update != snapshot_id {
        return false;
    }
    p.program_update_kind > ProgramUpdateKind::CLONED
}

impl Session {
    // Go: project/session.go:1679 publishProjectDiagnostics
    // PORT: Go `[]*ast.Diagnostic` is `&[Diagnostic]` (nil is empty).
    pub fn publish_project_diagnostics(
        &self,
        ctx: &Context,
        config_file_path: &str,
        diagnostics: &[Diagnostic],
        converters: &lsconv::Converters,
    ) {
        let mut lsp_diagnostics: Vec<lsproto::Diagnostic> = Vec::with_capacity(diagnostics.len());
        for diag in diagnostics {
            lsp_diagnostics.push(lsconv::diagnostic_to_lsp_push(ctx, converters, diag));
        }

        if let Err(err) = self.client.as_ref().expect(NIL_DEREF).publish_diagnostics(
            ctx,
            lsproto::PublishDiagnosticsParams {
                uri: lsconv::file_name_to_document_uri(config_file_path),
                diagnostics: lsp_diagnostics,
                ..Default::default()
            },
        ) {
            if self.options.logging_enabled {
                self.logger
                    .logf(&format!("Error publishing diagnostics: {}", err.error()));
            }
        }
    }

    // Go: project/session.go:1696 EnqueuePublishGlobalDiagnostics
    // EnqueuePublishGlobalDiagnostics schedules a background check for new accumulated
    // global diagnostics from checker pools, re-publishing tsconfig diagnostics if changed.
    // Multiple calls are coalesced into a single background task.
    pub fn enqueue_publish_global_diagnostics(self: &Rc<Self>) {
        if !self.options.push_diagnostics_enabled {
            return;
        }
        // Go: s.globalDiagPublishPending.CompareAndSwap(false, true)
        if !self.global_diag_publish_pending.get() {
            self.global_diag_publish_pending.set(true);
            let s = self.clone();
            self.background_queue
                .enqueue(&self.background_ctx, move |ctx| {
                    s.publish_global_diagnostics(ctx);
                });
        }
    }

    // Go: project/session.go:1705 publishGlobalDiagnostics
    pub fn publish_global_diagnostics(self: &Rc<Self>, ctx: &Context) {
        let snapshot = self.snapshot.borrow().clone();
        snapshot.ref_();

        for project in snapshot.project_collection.projects() {
            let project = project.borrow();
            if project.kind != Kind::CONFIGURED || project.checker_pool.is_none() {
                continue;
            }
            if project
                .checker_pool
                .as_ref()
                .expect(NIL_DEREF)
                .take_new_global_diagnostics()
            {
                let diagnostics = project.get_project_diagnostics(ctx);
                self.publish_project_diagnostics(
                    ctx,
                    &project.config_file_path,
                    &diagnostics,
                    &snapshot.converters,
                );
            }
        }

        // Go: defer snapshot.Deref(s); defer s.globalDiagPublishPending.Store(false)
        Snapshot::deref(&snapshot, self);
        self.global_diag_publish_pending.set(false);
    }

    // Go: project/session.go:1724 triggerATAForUpdatedProjects
    pub fn trigger_ata_for_updated_projects(self: &Rc<Self>, new_snapshot: &Rc<Snapshot>) {
        for project in new_snapshot.project_collection.projects() {
            if !project.borrow().should_trigger_ata(new_snapshot.id()) {
                continue;
            }
            let s = self.clone();
            self.background_queue
                .enqueue(&self.background_ctx, move |_ctx| {
                    let mut log_tree: Option<Rc<logging::LogTree>> = None;
                    if s.options.logging_enabled {
                        log_tree = logging::new_log_tree(&format!(
                            "Triggering ATA for project {}",
                            project.borrow().name()
                        ));
                    }

                    let typings_info = Rc::new(project.borrow().compute_typings_info());
                    let (request, project_name, project_display_name, config_file_path) = {
                        let p = project.borrow();
                        let request = ata::TypingsInstallRequest {
                            project_id: p.config_file_path.clone(),
                            typings_info: typings_info.clone(),
                            file_names: p
                                .program
                                .expect(NIL_DEREF)
                                .get_source_files()
                                .iter()
                                .map(|file| file.file_name().to_string())
                                .collect(),
                            project_root_path: p.current_directory.clone(),
                            compiler_options: Some(
                                p.command_line
                                    .as_ref()
                                    .expect(NIL_DEREF)
                                    .compiler_options()
                                    .clone(),
                            ),
                            current_directory: s.options.current_directory.clone(),
                            get_script_kind: Rc::new(|file_name: &str| {
                                crate::frontend::core_ext::get_script_kind_from_file_name(file_name)
                            }),
                            fs: s.fs.fs.clone(),
                            logger: log_tree.clone().map(|t| t as Rc<dyn logging::Logger>),
                        };
                        (
                            request,
                            p.name(),
                            p.display_name(&s.options.current_directory),
                            p.config_file_path.clone(),
                        )
                    };

                    if let Some(client) = s.client.as_ref() {
                        client.progress_start(
                            diag::Installing_types_for_0,
                            args![project_display_name],
                        );
                    }
                    let typings_installer = s.typings_installer.borrow().clone().expect(NIL_DEREF);
                    let result = typings_installer.install_typings_exported(&request);
                    if let Some(client) = s.client.as_ref() {
                        client.progress_finish(
                            diag::Installing_types_for_0,
                            args![project_display_name],
                        );
                    }
                    match result {
                        Err(err) => {
                            if log_tree.is_some() {
                                s.logger.log(&format!(
                                    "ATA installation failed for project {}: {}",
                                    project_name,
                                    err.error()
                                ));
                                s.logger.log(&log_tree.string());
                            }
                        }
                        Ok(result) => {
                            if result.typings_files != project.borrow().typings_files {
                                s.pending_ata_changes.borrow_mut().insert(
                                    config_file_path,
                                    Rc::new(ATAStateChange {
                                        project_id: tspath::Path::default(),
                                        typings_info: Some(typings_info),
                                        typings_files: result.typings_files,
                                        typings_files_to_watch: result.files_to_watch,
                                        logs: log_tree,
                                    }),
                                );
                                s.schedule_diagnostics_refresh();
                            }
                        }
                    }
                });
        }
    }

    // Go: project/session.go:1777 warmAutoImportCache
    // PORT: Go `defer cancel()` and `defer newSnapshot.Deref(s)` run on
    // every return; the port calls them on each path, in Go's defer order.
    //
    // PORT: the clone (the export extraction, which can take hundreds of
    // ms) runs as idle work (`gostd::local::go_idle`, `run_pending_warm`),
    // after the checks and the cancel setup that Go does first. The LSP
    // dispatch loop starts it only after a quiet period with no message, so
    // a request does not wait for it. Go runs the whole warm on a goroutine.
    // A file event or a newer warm cancels the context before or during the
    // clone (`WarmAutoImportPreempt`). A clone that has started runs to its
    // next cancel point, and its result is discarded, as Go's is. Its
    // registry build has more cancel points than Go's
    // (`autoimport::registry::DISCARD_ON_CANCEL_KEY`). A clone that has not
    // started is skipped: Go's would run and be discarded, and the only
    // trace it leaves is its snapshot id, which is taken here, where Go's
    // clone takes it.
    pub fn warm_auto_import_cache(
        self: &Rc<Self>,
        ctx: &Context,
        change: &SnapshotChange,
        _old_snapshot: &Rc<Snapshot>,
        new_snapshot: &Rc<Snapshot>,
    ) {
        if change.file_changes.changed.len() == 1 {
            let mut changed_file = lsproto::DocumentUri::default();
            for uri in &change.file_changes.changed {
                changed_file = uri.clone();
            }
            if !new_snapshot.fs.is_open_file(&changed_file.file_name()) {
                return;
            }
            let prefs = new_snapshot.user_preferences();
            if prefs.include_completions_for_module_exports.is_false() {
                return;
            }
            let Some(project) = new_snapshot.get_default_project(&changed_file) else {
                return;
            };
            if crate::ls::autoimport::Registry::is_prepared_for_importing_file(
                new_snapshot.auto_imports.as_deref(),
                &changed_file.file_name(),
                &project.borrow().config_file_path,
                &prefs,
            ) {
                return;
            }

            // Cancel any previous auto-import warming and create a new cancellable context.
            // Only publish the new cancel func if the derived context is still active,
            // and make the stored cancel func a no-op once that warming task is done.
            let previous_cancel = self.warm_auto_import_cancel.borrow().clone();
            if let Some(previous_cancel) = previous_cancel {
                previous_cancel();
            }
            let (warm_ctx, cancel) = gostd::context::with_cancel(ctx);
            if warm_ctx.err().is_none() {
                // PORT: the stored closure keeps the session logger (Go reads
                // `s.logger`, which never changes) instead of the session, so
                // it does not make a reference cycle through the session.
                let stored_ctx = warm_ctx.clone();
                let stored_cancel = cancel.clone();
                let logger = self.logger.clone();
                let file_name = changed_file.file_name();
                self.warm_auto_import_preempt.set(
                    warm_ctx.clone(),
                    cancel.clone(),
                    file_name.clone(),
                );
                *self.warm_auto_import_cancel.borrow_mut() = Some(Rc::new(move || {
                    if stored_ctx.err().is_some() {
                        return;
                    }
                    logger.logf(&format!(
                        "Cancelling auto-import warming for file {}",
                        file_name
                    ));
                    stored_cancel();
                }));
            }

            if warm_ctx.err().is_some() {
                cancel();
                return;
            }
            // Go: defer cancel()

            // Clone the snapshot with auto-imports using warmCtx so the expensive
            // extraction work is cancelled if a file change arrives.
            if !new_snapshot.try_ref() {
                cancel();
                return;
            }
            // Go: defer newSnapshot.Deref(s)

            // PORT: Go's clone would take its snapshot id now.
            let snapshot_id = self.snapshot_id.get() + 1;
            self.snapshot_id.set(snapshot_id);
            let warm = PendingWarm {
                ctx: warm_ctx,
                cancel,
                changed_file,
                new_snapshot: new_snapshot.clone(),
                snapshot_id,
            };
            // A pending warm here was cancelled above (`previous_cancel`).
            if let Some(previous) = self.warm_auto_import_pending.replace(Some(warm)) {
                self.end_pending_warm(previous);
            }
            if !self.warm_auto_import_queued.replace(true) {
                let s = self.clone();
                gostd::local::go_idle(Box::new(move || s.run_pending_warm()));
            }
        }
    }

    /// PORT: the part of Go `warmAutoImportCache` after `tryRef`, run as
    /// idle work for the pending warm (see `warm_auto_import_cache`).
    pub fn run_pending_warm(self: &Rc<Self>) {
        self.warm_auto_import_queued.set(false);
        let Some(warm) = self.warm_auto_import_pending.take() else {
            return;
        };
        if warm.ctx.err().is_some() {
            self.end_pending_warm(warm);
            return;
        }
        let PendingWarm {
            ctx: warm_ctx,
            cancel,
            changed_file,
            new_snapshot,
            snapshot_id,
        } = warm;

        let warm_change = SnapshotChange {
            reason: UpdateReason::REQUESTED_LANGUAGE_SERVICE_WITH_AUTO_IMPORTS,
            resource_request: ResourceRequest {
                documents: vec![changed_file.clone()],
                auto_imports: changed_file,
                ..Default::default()
            },
            ..Default::default()
        };
        // PORT: a cancelled warm drops its clone below (Go session.go:1844),
        // so its registry build may stop at more points than Go's
        // (`autoimport::registry::DISCARD_ON_CANCEL_KEY`). `build_ctx` is a
        // value child of `warm_ctx`, so it is cancelled exactly when
        // `warm_ctx` is.
        let build_ctx = gostd::context::with_value(
            &warm_ctx,
            &crate::ls::autoimport::registry::DISCARD_ON_CANCEL_KEY,
            (),
        );
        // PORT: the clone takes the id kept for it when the warm started.
        let next_snapshot_id = self.snapshot_id.replace(snapshot_id - 1);
        let cloned_snapshot = Snapshot::clone_(
            &new_snapshot,
            &build_ctx,
            warm_change,
            &new_snapshot.fs.overlays,
            self,
        );
        self.snapshot_id.set(next_snapshot_id);

        // If cancelled during clone, discard the incomplete result.
        if warm_ctx.err().is_some() {
            Snapshot::deref(&cloned_snapshot, self);
            Snapshot::deref(&new_snapshot, self);
            cancel();
            return;
        }

        // Conditionally adopt: if the session hasn't moved past newSnapshot,
        // promote the clone so future requests benefit from the warmed cache.
        self.adopt_snapshot_change(&new_snapshot, &cloned_snapshot);
        Snapshot::deref(&new_snapshot, self);
        cancel();
    }

    /// PORT: Go's deferred `newSnapshot.Deref(s)` and `cancel()` for a
    /// pending warm that ends without its clone.
    fn end_pending_warm(&self, warm: PendingWarm) {
        Snapshot::deref(&warm.new_snapshot, self);
        (warm.cancel)();
    }
}
