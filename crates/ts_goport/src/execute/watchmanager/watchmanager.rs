//! Go: internal/execute/watchmanager/watchmanager.go (fswatch directory
//! watches, event accumulation and DoCycle signaling for `tsc --watch` and
//! `tsc -b --watch`).
//!
//! PORT: threads. The frontend `Writer`, file system and backend are `Rc`
//! and stay on the dispatch thread. fswatch callbacks run on the debouncer
//! thread. So the Go `WatchManager` is split: `WatchManager` holds the
//! dispatch-thread fields, and `WatchManagerShared` (an `Arc`) holds the
//! fields that `onWatchEvents` and `handleWatchTerminated` touch
//! (`mu`, `watchedDirs`, the `doCycleCh` sender, `changedMu` and its data).
//! Those two methods live on `WatchManagerShared`. Their `DebugLog` and
//! `warnWriter` output goes to the process stdout: Go passes
//! `sys.Writer()`, which is `os.Stdout` for the real system, and the `Rc`
//! writer cannot cross threads.

use crate::execute::watchmanager::prelude::*;

use std::io::Write;
use std::sync::mpsc::{Receiver, RecvTimeoutError, SyncSender, sync_channel};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

use crate::execute::tsc::{Writer, write_str};
use crate::frontend::core_ls_ext;
use crate::frontend::tspath;
use crate::fswatch;
use crate::gostd::errors;

// Go: watchmanager.go:15 watchedDir
/// PORT: shared as `Arc<WatchedDir>`; Go compares `*watchedDir` pointers
/// (`Arc::ptr_eq`). Go sets `closer` after the watch starts, so it sits in a
/// `Mutex` (`None` is a nil closer).
pub struct WatchedDir {
    pub closer: Mutex<Option<Box<dyn fswatch::Watch>>>,
    pub recursive: bool,
}

impl WatchedDir {
    // PORT: Go `wd.closer.Close()` (the error is ignored).
    fn close_closer(&self) {
        if let Some(closer) = self.closer.lock().unwrap().as_ref() {
            let _ = closer.close();
        }
    }
}

// Go: watchmanager.go:28 WatchManager
/// WatchManager manages fswatch directory watches, event accumulation,
/// and DoCycle signaling. It is shared by the CLI watcher and the build
/// mode orchestrator.
///
/// Locking contract:
///   - Call Lock/Unlock around the entire DoCycle body.
///   - ReconcileWatches must be called under Lock.
///   - CloseAllWatches and handleWatchTerminated manage their own locking.
pub struct WatchManager {
    pub backend: Option<Rc<dyn WatchBackend>>,
    /// PORT: the receive side of Go `doCycleCh`.
    pub do_cycle_ch: Receiver<()>,

    /// DebugLog receives verbose watch diagnostics when non-nil
    pub debug_log: Option<Writer>,

    /// PORT: only `onWatchEvents` writes to it in Go; that runs on the
    /// callback thread and writes to the process stdout (see the file
    /// comment).
    pub warn_writer: Writer,
    pub dir_exists: Box<dyn Fn(&str) -> bool>,

    /// PORT: the fields the callback thread shares (see the file comment).
    pub shared: Arc<WatchManagerShared>,
}

/// PORT: the `WatchManager` fields that the fswatch callback thread
/// touches.
pub struct WatchManagerShared {
    /// Go `mu`. Go locks it in `Lock` and unlocks it in `Unlock`.
    pub mu: GoMutex,
    /// Go `watchedDirs` (guarded by `mu` in Go; the `Mutex` is Rust's
    /// data lock, taken only for short reads and writes).
    pub watched_dirs: Mutex<FxHashMap<String, Arc<WatchedDir>>>,
    /// PORT: the send side of Go `doCycleCh` (capacity 1).
    pub do_cycle_ch: SyncSender<()>,

    pub changed_mu: Mutex<WatchManagerChanged>,
}

/// PORT: the `WatchManager` fields that Go `changedMu` guards.
#[derive(Default)]
pub struct WatchManagerChanged {
    /// Go `map[string]fswatch.EventKind`; `None` is Go's nil map.
    pub changed_paths: Option<FxHashMap<String, fswatch::EventKind>>,
    pub changed_overflow: bool,
}

/// PORT: Go `sync.Mutex` that one method locks and another unlocks
/// (`Lock` and `Unlock` around a DoCycle body). A std `MutexGuard` cannot
/// cross those calls, so this is a flag and a condition variable.
#[derive(Default)]
pub struct GoMutex {
    locked: Mutex<bool>,
    cond: Condvar,
}

impl GoMutex {
    /// Go `m.Lock()`.
    pub fn lock(&self) {
        let mut locked = self.locked.lock().unwrap();
        while *locked {
            locked = self.cond.wait(locked).unwrap();
        }
        *locked = true;
    }

    /// Go `m.Unlock()`.
    pub fn unlock(&self) {
        let mut locked = self.locked.lock().unwrap();
        if !*locked {
            panic!("sync: unlock of unlocked mutex");
        }
        *locked = false;
        self.cond.notify_one();
    }
}

// Go: watchmanager.go:45 NewWatchManager
pub fn new_watch_manager(
    warn_writer: Writer,
    dir_exists: Box<dyn Fn(&str) -> bool>,
) -> WatchManager {
    let (do_cycle_tx, do_cycle_rx) = sync_channel::<()>(1);
    WatchManager {
        backend: None,
        do_cycle_ch: do_cycle_rx,
        debug_log: None,
        warn_writer,
        dir_exists,
        shared: Arc::new(WatchManagerShared {
            mu: GoMutex::default(),
            watched_dirs: Mutex::new(FxHashMap::default()),
            do_cycle_ch: do_cycle_tx,
            changed_mu: Mutex::new(WatchManagerChanged::default()),
        }),
    }
}

impl WatchManager {
    // Go: watchmanager.go:54 WatchManager.SetBackend
    pub fn set_backend(&mut self, b: Rc<dyn WatchBackend>) {
        self.backend = Some(b);
    }

    // Go: watchmanager.go:56 WatchManager.Backend
    pub fn backend(&self) -> Option<Rc<dyn WatchBackend>> {
        self.backend.clone()
    }

    // Go: watchmanager.go:58 WatchManager.EnsureDefaultBackend
    pub fn ensure_default_backend(&mut self) {
        if self.backend.is_none() {
            let fsw = fswatch::default();
            self.backend = Some(Rc::new(FsWatchBackend { inner: fsw.clone() }));
            if let Some(debug_log) = &self.debug_log {
                write_str(
                    debug_log,
                    &format!("[watch] using {} backend\n", fsw.name()),
                );
            }
        }
    }

    // Go: watchmanager.go:68 WatchManager.Lock
    pub fn lock(&self) {
        self.shared.mu.lock();
    }

    // Go: watchmanager.go:70 WatchManager.Unlock
    pub fn unlock(&self) {
        self.shared.mu.unlock();
    }

    // Go: watchmanager.go:72 WatchManager.DoCycleCh
    pub fn do_cycle_ch(&self) -> &Receiver<()> {
        &self.do_cycle_ch
    }

    // Go: watchmanager.go:74 WatchManager.DrainEvents
    /// PORT: Go returns a nil map when nothing changed; the port returns an
    /// empty map.
    pub fn drain_events(&self) -> (FxHashMap<String, fswatch::EventKind>, bool) {
        let mut changed = self.shared.changed_mu.lock().unwrap();
        let changed_paths = changed.changed_paths.take().unwrap_or_default();
        let overflow = changed.changed_overflow;
        changed.changed_overflow = false;
        drop(changed);
        (changed_paths, overflow)
    }

    // Go: watchmanager.go:84 WatchManager.ForceOverflow
    pub fn force_overflow(&self) {
        let mut changed = self.shared.changed_mu.lock().unwrap();
        changed.changed_overflow = true;
    }

    // Go: watchmanager.go:162 WatchManager.CloseAllWatches
    pub fn close_all_watches(&self) {
        self.shared.mu.lock();
        let closers: Vec<Arc<WatchedDir>> = {
            let mut watched_dirs = self.shared.watched_dirs.lock().unwrap();
            let mut closers = Vec::with_capacity(watched_dirs.len());
            for (_dir, wd) in watched_dirs.drain() {
                closers.push(wd);
            }
            closers
        };
        self.shared.mu.unlock();
        for c in &closers {
            c.close_closer();
        }
    }

    // Go: watchmanager.go:175 WatchManager.createDirWatch
    pub fn create_dir_watch(&self, dir: &str, recursive: bool) -> Result<(), GoError> {
        let entry = Arc::new(WatchedDir {
            closer: Mutex::new(None),
            recursive,
        });
        let shared = self.shared.clone();
        let identity = entry.clone();
        let cb_dir = dir.to_string();
        // PORT: the callback runs on the fswatch debouncer thread; it logs
        // to stdout when DebugLog was set when the watch was made (Go reads
        // DebugLog at event time; callers set it before the first watch).
        let debug_log = self.debug_log.is_some();
        let cb: fswatch::WatchCallback =
            Arc::new(move |events: Vec<fswatch::Event>, err: Option<GoError>| {
                if let Some(e) = &err {
                    if errors::is(e, &fswatch::ERR_WATCH_TERMINATED) {
                        shared.handle_watch_terminated(debug_log, &cb_dir, &identity);
                        return;
                    }
                }
                shared.on_watch_events(debug_log, events, err);
            });
        let ignore: Arc<dyn Fn(&str) -> bool + Send + Sync> = Arc::new(should_ignore_watch_path);
        let backend = self.backend.as_ref().expect("watchmanager: backend is set");
        let watch = match backend.watch_directory(dir, cb, recursive, Some(ignore)) {
            Ok(watch) => watch,
            Err(err) => {
                if let Some(debug_log) = &self.debug_log {
                    write_str(
                        debug_log,
                        &format!(
                            "[watch] failed to watch directory {}: {}\n",
                            dir,
                            err.error()
                        ),
                    );
                }
                return Err(errors::errorf(
                    format!("failed to watch directory {}: {}", dir, err.error()),
                    vec![err],
                ));
            }
        };
        *entry.closer.lock().unwrap() = Some(watch);
        self.shared
            .watched_dirs
            .lock()
            .unwrap()
            .insert(dir.to_string(), entry);
        Ok(())
    }

    // Go: watchmanager.go:196 WatchManager.ResolveDesiredDirs
    pub fn resolve_desired_dirs(
        &self,
        desired_dirs: &FxHashMap<String, bool>,
    ) -> FxHashMap<String, bool> {
        let mut resolved: FxHashMap<String, bool> =
            FxHashMap::with_capacity_and_hasher(desired_dirs.len(), Default::default());
        for (dir, recursive) in desired_dirs {
            let mut watch_dir = dir.clone();
            let mut watch_recursive = *recursive;
            while !(self.dir_exists)(&watch_dir) {
                let parent = tspath::get_directory_path(&watch_dir);
                if parent == watch_dir {
                    break;
                }
                watch_dir = parent;
                watch_recursive = false; // ancestor fallbacks are always non-recursive
            }
            if !(self.dir_exists)(&watch_dir) || !can_watch_directory(&watch_dir) {
                if let Some(debug_log) = &self.debug_log {
                    write_str(
                        debug_log,
                        &format!("[watch] no watchable ancestor for {dir}\n"),
                    );
                }
                continue;
            }
            if watch_dir != *dir {
                if let Some(debug_log) = &self.debug_log {
                    write_str(
                        debug_log,
                        &format!("[watch] resolved {dir} to ancestor {watch_dir}\n"),
                    );
                }
            }
            if let Some(existing) = resolved.get(&watch_dir).copied() {
                resolved.insert(watch_dir, existing || watch_recursive);
            } else {
                resolved.insert(watch_dir, watch_recursive);
            }
        }
        resolved
    }

    // Go: watchmanager.go:227 WatchManager.ReconcileWatches
    // PORT: Go ranges over `wm.watchedDirs` while the callbacks delete and
    // add entries (Go allows that). The port passes a copy of the map and
    // the callbacks change the live map; the entries a callback adds match
    // `desiredDirs`, so Go makes no further call for them either.
    pub fn reconcile_watches(&self, desired_dirs: &FxHashMap<String, bool>) -> Result<(), GoError> {
        if self.backend.is_none() {
            return Ok(());
        }

        let watch_err: RefCell<Option<GoError>> = RefCell::new(None);
        let watched_dirs: FxHashMap<String, Arc<WatchedDir>> =
            self.shared.watched_dirs.lock().unwrap().clone();
        let mut on_added = |dir: &String, recursive: &bool| {
            let recursive = *recursive;
            if let Some(debug_log) = &self.debug_log {
                write_str(
                    debug_log,
                    &format!("[watch] watching directory {dir} (recursive={recursive})\n"),
                );
            }
            if let Err(err) = self.create_dir_watch(dir, recursive) {
                let mut watch_err = watch_err.borrow_mut();
                if watch_err.is_none() {
                    *watch_err = Some(err);
                }
            }
        };
        let mut on_removed = |dir: &String, wd: &Arc<WatchedDir>| {
            if let Some(debug_log) = &self.debug_log {
                write_str(
                    debug_log,
                    &format!("[watch] closing stale dir watch: {dir}\n"),
                );
            }
            wd.close_closer();
            self.shared.watched_dirs.lock().unwrap().remove(dir);
        };
        let mut on_changed = |dir: &String, wd: &Arc<WatchedDir>, recursive: &bool| {
            let recursive = *recursive;
            if let Some(debug_log) = &self.debug_log {
                write_str(
                    debug_log,
                    &format!(
                        "[watch] recreating dir watch {dir} (recursive {}→{recursive})\n",
                        wd.recursive
                    ),
                );
            }
            wd.close_closer();
            self.shared.watched_dirs.lock().unwrap().remove(dir);
            if let Err(err) = self.create_dir_watch(dir, recursive) {
                let mut watch_err = watch_err.borrow_mut();
                if watch_err.is_none() {
                    *watch_err = Some(err);
                }
            }
        };
        core_ls_ext::diff_maps_func::<String, Arc<WatchedDir>, bool>(
            &watched_dirs,
            desired_dirs,
            |wd: &Arc<WatchedDir>, recursive: &bool| wd.recursive == *recursive,
            Some(&mut on_added),
            Some(&mut on_removed),
            Some(&mut on_changed),
        );
        match watch_err.into_inner() {
            Some(err) => Err(err),
            None => Ok(()),
        }
    }

    // Go: watchmanager.go:279 WatchManager.IsPathUnderWatch
    pub fn is_path_under_watch(&self, path: &str, opts: &tspath::ComparePathsOptions) -> bool {
        let watched_dirs = self.shared.watched_dirs.lock().unwrap();
        for dir in watched_dirs.keys() {
            if tspath::contains_path(dir, path, opts) {
                return true;
            }
        }
        false
    }

    // Go: watchmanager.go:288 WatchManager.RunLoop
    // PORT: Go selects on `ctx.Done()` and `doCycleCh`. The port waits on
    // the channel with a timeout and checks `ctx.err()` (PORTING "Go
    // runtime"). `doCycle` is the caller's DoCycle method value.
    pub fn run_loop(&self, ctx: &Context, do_cycle: &mut dyn FnMut()) {
        const CTX_POLL_INTERVAL: Duration = Duration::from_millis(50);
        loop {
            if ctx.err().is_some() {
                self.close_all_watches();
                return;
            }
            match self.do_cycle_ch.recv_timeout(CTX_POLL_INTERVAL) {
                Ok(()) => do_cycle(),
                Err(RecvTimeoutError::Timeout) => {}
                Err(RecvTimeoutError::Disconnected) => {
                    // PORT: cannot happen; `shared` keeps the sender alive.
                }
            }
        }
    }
}

impl WatchManagerShared {
    // Go: watchmanager.go:90 WatchManager.signalDoCycle
    pub fn signal_do_cycle(&self) {
        match self.do_cycle_ch.try_send(()) {
            Ok(()) => {
                // Signal sent; the DoCycle loop will pick it up.
            }
            Err(_) => {
                // A signal is already pending; coalesced.
            }
        }
    }

    // Go: watchmanager.go:99 WatchManager.onWatchEvents
    // PORT: runs on the fswatch callback thread. `debug_log` is whether Go
    // `wm.DebugLog` is non-nil; the text goes to the process stdout, as does
    // the `warnWriter` warning (see the file comment).
    pub fn on_watch_events(
        &self,
        debug_log: bool,
        events: Vec<fswatch::Event>,
        err: Option<GoError>,
    ) {
        if let Some(err) = err {
            if errors::is(&err, &fswatch::ERR_OVERFLOW) {
                if debug_log {
                    write_stdout("[watch] event overflow, triggering rebuild\n");
                }
                {
                    let mut changed = self.changed_mu.lock().unwrap();
                    changed.changed_overflow = true;
                }
                self.signal_do_cycle();
                return;
            }
            write_stdout(&format!("Warning: File watch error: {}\n", err.error()));
            return;
        }

        if !events.is_empty() {
            if debug_log {
                let mut text = format!("[watch] {} event(s): ", events.len());
                for (i, e) in events.iter().enumerate() {
                    if i > 0 {
                        text.push_str(", ");
                    }
                    if i >= 5 {
                        text.push_str(&format!("... and {} more", events.len() - i));
                        break;
                    }
                    text.push_str(&format!("{} {}", e.kind.string(), e.path));
                }
                text.push('\n');
                write_stdout(&text);
            }
            {
                let mut changed = self.changed_mu.lock().unwrap();
                let changed_paths = changed.changed_paths.get_or_insert_with(|| {
                    FxHashMap::with_capacity_and_hasher(events.len(), Default::default())
                });
                for e in &events {
                    changed_paths.insert(e.path.clone(), e.kind);
                }
            }
            self.signal_do_cycle();
        }
    }

    // Go: watchmanager.go:142 WatchManager.handleWatchTerminated
    // PORT: runs on the fswatch callback thread (see onWatchEvents).
    pub fn handle_watch_terminated(&self, debug_log: bool, dir: &str, identity: &Arc<WatchedDir>) {
        if debug_log {
            write_stdout(&format!("[watch] watch terminated: {dir}\n"));
        }
        let mut stale_closer: Option<Arc<WatchedDir>> = None;
        self.mu.lock();
        {
            let mut watched_dirs = self.watched_dirs.lock().unwrap();
            if let Some(wd) = watched_dirs.get(dir) {
                if Arc::ptr_eq(wd, identity) {
                    stale_closer = Some(wd.clone());
                    watched_dirs.remove(dir);
                }
            }
        }
        self.mu.unlock();
        if let Some(stale_closer) = stale_closer {
            stale_closer.close_closer();
        }
        {
            let mut changed = self.changed_mu.lock().unwrap();
            changed.changed_overflow = true;
        }
        self.signal_do_cycle();
    }
}

// Go: watchmanager.go:266 IsDirCoveredByWatch
pub fn is_dir_covered_by_watch(
    dirs: &FxHashMap<String, bool>,
    dir: &str,
    opts: &tspath::ComparePathsOptions,
) -> bool {
    for (wdir, recursive) in dirs {
        if *recursive {
            if tspath::contains_path(wdir, dir, opts) {
                return true;
            }
        } else if dir == wdir.as_str() {
            return true;
        }
    }
    false
}

// PORT: Go `fmt.Fprintf(w, ...)` on the callback thread, where `w` is the
// real system's `os.Stdout` (see the file comment). Errors are ignored as
// in Go.
fn write_stdout(text: &str) {
    let mut stdout = std::io::stdout();
    let _ = stdout.write_all(text.as_bytes());
    let _ = stdout.flush();
}
