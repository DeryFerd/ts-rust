//! Go: internal/fswatch/watcher.go (the `Watcher` API, the package
//! watchers, the shared backend base and the per-directory watch state).
//!
//! PORT: threads. Go runs one goroutine per backend event loop and one per
//! debouncer; callbacks run on the debouncer goroutine. The port uses
//! `std::thread` and shares state through `Arc`. Each Go `sync.Mutex` is a
//! `std::sync::Mutex` over the fields it guards (`*Locked` structs). A Go
//! `*dirWatch` map key is the `Arc` pointer (`Arc::as_ptr(..) as usize`).
//!
//! PORT: D-W1 (no `libc`, no `unsafe`). The Linux backends call the
//! `fswatch::unix` shim, whose syscalls are `unported!`. The kqueue,
//! FSEvents and Windows backends are not ported: their package watchers keep
//! a `None` factory, so `available()` is false, as on Linux in Go.

use crate::fswatch::prelude::*;

use std::any::Any;
use std::panic::AssertUnwindSafe;
use std::sync::{Arc, Condvar, LazyLock, Mutex, OnceLock, Weak};
use std::time::Duration;

use crate::frontend::vfs::osvfs::filepath_clean;
use crate::gostd::errors;

// Go: watcher.go:13 errNilCallback
pub static ERR_NIL_CALLBACK: LazyLock<GoError> =
    LazyLock::new(|| errors::new("fswatch: callback must not be nil"));

// Go: watcher.go:17 errRootPath
/// errRootPath is returned by WatchFile when the supplied path is a
/// filesystem root with no parent directory to watch.
pub static ERR_ROOT_PATH: LazyLock<GoError> =
    LazyLock::new(|| errors::new("fswatch: cannot watch a root path"));

// Go: watcher.go:21 errNotAbsolute
/// errNotAbsolute is returned by [Watcher.WatchDirectory] and
/// [Watcher.WatchFile] when the supplied path is not absolute.
pub static ERR_NOT_ABSOLUTE: LazyLock<GoError> =
    LazyLock::new(|| errors::new("fswatch: path must be absolute"));

// Go: watcher.go:27 ErrOverflow
/// ErrOverflow indicates that the kernel event queue overflowed and
/// some filesystem changes were missed. The watch remains
/// active; further events will continue to be delivered. Callers
/// should treat this as a signal to rescan the watched directory.
pub static ERR_OVERFLOW: LazyLock<GoError> =
    LazyLock::new(|| errors::new("fswatch: event overflow; some changes were missed"));

// Go: watcher.go:33 ErrWatchTerminated
/// ErrWatchTerminated indicates that the watch was terminated due to
/// an unrecoverable error (e.g. the watched directory was deleted or
/// the watch descriptor was revoked). No further events will be
/// delivered. Call Close to release remaining state.
pub static ERR_WATCH_TERMINATED: LazyLock<GoError> =
    LazyLock::new(|| errors::new("fswatch: watch terminated"));

// Go: watcher.go:37 ErrUnavailable
/// ErrUnavailable indicates that a requested watcher is not
/// available on the current platform.
pub static ERR_UNAVAILABLE: LazyLock<GoError> =
    LazyLock::new(|| errors::new("fswatch: watcher not available on this platform"));

// Go: watcher.go:45 Watcher
/// Watcher represents a filesystem watching implementation.
/// Use one of the constructor functions ([Inotify], [FSEvents], [Kqueue],
/// [Windows]) to obtain a value, or [Default] for the platform default.
///
/// All watchers exist on every platform. Subscribing with a watcher that
/// is not supported on the current OS returns [ErrUnavailable].
///
/// PORT: Go `WatchDirectory` checks `fn == nil`; a Rust `WatchCallback` is
/// never nil, so `ERR_NIL_CALLBACK` is not returned. Go returns the
/// `Watch` interface; the port returns `Box<dyn Watch>`.
pub trait Watcher: Send + Sync {
    /// Name returns a stable identifier ("inotify", "fsevents", "kqueue",
    /// "windows").
    fn name(&self) -> String;
    /// Available reports whether this watcher works on the current OS.
    fn available(&self) -> bool;
    /// HasFastRecursiveBackend reports whether this watcher supports efficient
    /// recursive watching without requiring a full userspace tree walk. This is
    /// true for Windows (ReadDirectoryChangesW subtree mode) and macOS FSEvents
    /// (inherently recursive), and false for all other backends.
    fn has_fast_recursive_backend(&self) -> bool;
    /// WatchDirectory watches dir for changes, calling fn with batched
    /// events. By default, only direct children are watched. Use
    /// [WithRecursive] to watch the entire directory tree.
    /// dir must be an absolute path to an existing directory.
    /// Returns [ErrUnavailable] if the watcher is not supported on
    /// the current platform.
    fn watch_directory(
        &self,
        dir: &str,
        fn_: WatchCallback,
        opts: &[Box<dyn WatchOption>],
    ) -> Result<Box<dyn Watch>, GoError>;
    /// WatchFile watches a single file for changes, calling fn with
    /// batched events. path must be an absolute path. The file does not
    /// need to exist at subscribe time; its creation will be reported.
    /// The parent directory must exist.
    ///
    /// Multiple WatchFile calls for files in the same directory
    /// share a single OS watch on the parent directory.
    ///
    /// If the parent directory is deleted, [ErrWatchTerminated] is
    /// delivered and the watch is dead. Unlike TypeScript's
    /// watchFile (which falls back to polling for missing entries),
    /// there is no automatic recovery. Callers that need to survive
    /// parent directory deletion should handle [ErrWatchTerminated]
    /// and re-subscribe when the directory is recreated.
    ///
    /// Returns [ErrUnavailable] if the watcher is not supported on
    /// the current platform.
    fn watch_file(&self, path: &str, fn_: WatchCallback) -> Result<Box<dyn Watch>, GoError>;
    fn unexported(&self);
}

// Go: watcher.go:85 WatchOption
/// WatchOption configures a watch.
pub trait WatchOption: Send + Sync {
    fn apply_watch_option(&self, opts: &mut WatchOptions);
}

// Go: watcher.go:89 watchOptions
#[derive(Clone, Default)]
pub struct WatchOptions {
    pub ignore: Option<Arc<dyn Fn(&str) -> bool + Send + Sync>>,
    pub recursive: bool,
}

// Go: watcher.go:94 ignoreOption
pub struct IgnoreOption {
    pub fn_: Arc<dyn Fn(&str) -> bool + Send + Sync>,
}

impl WatchOption for IgnoreOption {
    // Go: watcher.go:98 ignoreOption.applyWatchOption
    fn apply_watch_option(&self, opts: &mut WatchOptions) {
        opts.ignore = Some(self.fn_.clone());
    }
}

// Go: watcher.go:105 WithIgnore
/// WithIgnore returns a [WatchOption] that filters events before delivery.
/// If the function returns true for a path, events for that path are
/// silently dropped. The filtering is per-subscriber; multiple watches
/// on the same directory may have different ignore functions.
pub fn with_ignore(fn_: Arc<dyn Fn(&str) -> bool + Send + Sync>) -> Box<dyn WatchOption> {
    Box::new(IgnoreOption { fn_ })
}

// Go: watcher.go:110 recursiveOption
pub struct RecursiveOption;

impl WatchOption for RecursiveOption {
    // Go: watcher.go:112 recursiveOption.applyWatchOption
    fn apply_watch_option(&self, opts: &mut WatchOptions) {
        opts.recursive = true;
    }
}

// Go: watcher.go:125 WithRecursive
/// WithRecursive returns a [WatchOption] that enables recursive watching
/// of the entire directory tree. Without this option,
/// [Watcher.WatchDirectory] watches only direct children of dir.
///
/// In recursive mode, events for all descendants at any depth are
/// delivered. On inotify/fanotify, a watch descriptor is added for
/// every subdirectory. On kqueue, an fd is opened for every entry.
/// On Windows, bWatchSubtree=TRUE is passed to ReadDirectoryChangesW.
/// On FSEvents, the kernel is inherently recursive.
pub fn with_recursive() -> Box<dyn WatchOption> {
    Box::new(RecursiveOption)
}

// Go: watcher.go:131 Watch
/// Watch represents a live watch. Close stops watching
/// and releases resources. It is idempotent.
///
/// PORT: Go `io.Closer` users (watchmanager, lspwatcher) hold a
/// `Box<dyn Watch>`.
pub trait Watch: Send + Sync {
    fn close(&self) -> Result<(), GoError>;
    fn unexported(&self);
}

/// PORT: Go `error` in the callback. Plan decision D-CTX: one error type,
/// `GoError`; test sentinels with `errors::is(&err, &ERR_OVERFLOW)`.
pub type WatchError = GoError;

// Go: watcher.go:144 WatchCallback
/// WatchCallback receives batched filesystem events. Rapid changes
/// are coalesced before delivery.
///
/// For a given Watch, the callback is never invoked concurrently
/// with itself. It runs on a library goroutine, not the caller's.
///
/// When err is non-nil, use [errors.Is] to check for [ErrOverflow]
/// (recoverable) or [ErrWatchTerminated] (terminal).
///
/// PORT: Go `nil` events are an empty `Vec`.
pub type WatchCallback = Arc<dyn Fn(Vec<Event>, Option<WatchError>) + Send + Sync>;

/// PORT: Go `func() watcherImpl` factory.
pub type WatcherFactory = fn() -> Arc<dyn WatcherImpl>;

// Go: watcher.go:147 package-level watcher instances
// Package-level watcher instances. Platform init() functions set the factory.
//
// PORT: Go package vars set up by the platform `init()` functions. The
// port builds each one on first use and calls the Linux `init` there. The
// kqueue, FSEvents and Windows backends are not ported (D-W1): their
// factory stays `None`, as on Linux in Go.
pub static INOTIFY_WATCHER: LazyLock<Arc<WatcherStruct>> = LazyLock::new(|| {
    new_watcher("inotify", |w| {
        #[cfg(target_os = "linux")]
        crate::fswatch::inotify_linux::init(w);
    })
});
pub static FSEVENTS_WATCHER: LazyLock<Arc<WatcherStruct>> =
    LazyLock::new(|| new_watcher("fsevents", |_| {}));
pub static KQUEUE_WATCHER: LazyLock<Arc<WatcherStruct>> =
    LazyLock::new(|| new_watcher("kqueue", |_| {}));
pub static WINDOWS_WATCHER: LazyLock<Arc<WatcherStruct>> =
    LazyLock::new(|| new_watcher("windows", |_| {}));
pub static FANOTIFY_WATCHER: LazyLock<Arc<WatcherStruct>> = LazyLock::new(|| {
    new_watcher("fanotify", |w| {
        #[cfg(target_os = "linux")]
        crate::fswatch::fanotify_linux::init(w);
    })
});

// PORT: Go `&watcher{name: name}` composite literal, followed by the
// platform `init()` that sets the factory. The watcher also keeps a weak
// pointer to its own `Arc`, which Go gets from the `*watcher` receiver.
pub fn new_watcher(name: &str, init: impl FnOnce(&mut WatcherStruct)) -> Arc<WatcherStruct> {
    Arc::new_cyclic(|self_: &Weak<WatcherStruct>| {
        let mut w = WatcherStruct {
            name: name.to_string(),
            mu: Mutex::new(WatcherStructLocked::default()),
            factory: None,
            self_: self_.clone(),
        };
        init(&mut w);
        w
    })
}

// Go: watcher.go:158 AllWatchers
/// AllWatchers returns a fresh slice listing every watcher backend the package
/// knows about. Use [Watcher.Available] to check which ones work on the current
/// OS.
pub fn all_watchers() -> Vec<Arc<dyn Watcher>> {
    let inotify_watcher: Arc<dyn Watcher> = INOTIFY_WATCHER.clone();
    let fsevents_watcher: Arc<dyn Watcher> = FSEVENTS_WATCHER.clone();
    let kqueue_watcher: Arc<dyn Watcher> = KQUEUE_WATCHER.clone();
    let windows_watcher: Arc<dyn Watcher> = WINDOWS_WATCHER.clone();
    let fanotify_watcher: Arc<dyn Watcher> = FANOTIFY_WATCHER.clone();
    vec![
        inotify_watcher,
        fsevents_watcher,
        kqueue_watcher,
        windows_watcher,
        fanotify_watcher,
    ]
}

// Go: watcher.go:169 Inotify
/// Inotify returns the inotify watcher (Linux).
pub fn inotify() -> Arc<dyn Watcher> {
    INOTIFY_WATCHER.clone()
}

// Go: watcher.go:172 FSEvents
/// FSEvents returns the FSEvents watcher (macOS).
pub fn fs_events() -> Arc<dyn Watcher> {
    FSEVENTS_WATCHER.clone()
}

// Go: watcher.go:175 Kqueue
/// Kqueue returns the kqueue watcher (macOS, FreeBSD, and other BSDs).
pub fn kqueue() -> Arc<dyn Watcher> {
    KQUEUE_WATCHER.clone()
}

// Go: watcher.go:178 Windows
/// Windows returns the ReadDirectoryChangesW watcher (Windows).
pub fn windows() -> Arc<dyn Watcher> {
    WINDOWS_WATCHER.clone()
}

// Go: watcher.go:181 Fanotify
/// Fanotify returns the fanotify watcher (Linux, kernel ≥ 5.13).
pub fn fanotify() -> Arc<dyn Watcher> {
    FANOTIFY_WATCHER.clone()
}

// Go: watcher.go:184 Default
/// Default returns the recommended watcher for the current OS.
///
/// PORT: Go `runtime.GOOS` is `std::env::consts::OS` ("macos" for Go
/// "darwin"). On Linux this returns fanotify when the `fanotify_init` probe
/// succeeds and inotify when it fails, as Go does. On macOS and Windows Go
/// picks a fast recursive backend; those backends are not ported, so the
/// port diverges there.
pub fn default() -> Arc<dyn Watcher> {
    match std::env::consts::OS {
        "linux" => {
            if fanotify().available() {
                return fanotify();
            }
            inotify()
        }
        "macos" => {
            if fs_events().available() {
                return fs_events();
            }
            kqueue()
        }
        "windows" => windows(),
        "freebsd" | "openbsd" | "netbsd" | "dragonfly" => kqueue(),
        _ => new_watcher("unsupported", |_| {}),
    }
}

// Go: watcher.go:208 watcher
/// watcher is the concrete implementation of [Watcher]. Each platform
/// watcher is a package-level *watcher whose factory is set by the
/// platform's init() function.
///
/// PORT: named `WatcherStruct` because the Go interface `Watcher` and the
/// struct `watcher` have the same Rust name. Go `mu` guards the fields in
/// `WatcherStructLocked`. `factory` is set once, before the watcher is
/// shared.
pub struct WatcherStruct {
    pub name: String,
    pub mu: Mutex<WatcherStructLocked>,
    /// nil if not available on this platform
    pub factory: Option<WatcherFactory>,
    /// PORT: the `*watcher` receiver as an `Arc` (see `new_watcher`).
    pub self_: Weak<WatcherStruct>,
}

/// PORT: the `watcher` fields that Go `w.mu` guards.
#[derive(Default)]
pub struct WatcherStructLocked {
    pub impl_: Option<Arc<dyn WatcherImpl>>,
    /// Go `map[string]*dirWatch`; `None` is Go's nil map.
    pub dir_watches: Option<FxHashMap<String, Arc<DirWatch>>>,
    /// lazily created in getOrCreateDirWatch
    pub debounce: Option<Arc<Debounce>>,
}

impl WatcherStruct {
    // Go: watcher.go:218 watcher.String
    pub fn string(&self) -> String {
        self.name.clone()
    }

    // PORT: Go uses the `*watcher` receiver pointer; the port upgrades the
    // weak self pointer (the watcher is alive while `self` is borrowed).
    fn self_arc(&self) -> Arc<WatcherStruct> {
        self.self_.upgrade().expect("fswatch: watcher is alive")
    }

    // Go: watcher.go:232 watcher.getImpl
    pub fn get_impl(&self) -> Result<Arc<dyn WatcherImpl>, GoError> {
        let factory = {
            let w = self.mu.lock().unwrap();
            if let Some(impl_) = &w.impl_ {
                let impl_ = impl_.clone();
                return Ok(impl_);
            }
            self.factory
        };

        let Some(factory) = factory else {
            return Err(ERR_UNAVAILABLE.clone());
        };

        let impl_ = factory();
        impl_.run()?;

        let mut w = self.mu.lock().unwrap();
        let existing = w.impl_.clone();
        if let Some(existing) = existing {
            drop(w);
            impl_.shutdown();
            return Ok(existing);
        }
        w.impl_ = Some(impl_.clone());
        drop(w);
        Ok(impl_)
    }

    // Go: watcher.go:262 watcher.getOrCreateDirWatch
    pub fn get_or_create_dir_watch(&self, dir: &str, recursive: bool) -> Arc<DirWatch> {
        let mut w = self.mu.lock().unwrap();
        if w.dir_watches.is_none() {
            w.dir_watches = Some(FxHashMap::default());
        }
        if w.debounce.is_none() {
            w.debounce = Some(new_debounce());
        }
        let mut key = dir.to_string();
        if recursive {
            key = format!("{dir}\x00recursive");
        }
        if let Some(dw) = w.dir_watches.as_ref().unwrap().get(&key) {
            return dw.clone();
        }
        // PORT: Go sets `dw.recursive = recursive` right after newDirWatch,
        // before the dirWatch is shared; the port passes it in.
        let dw = new_dir_watch(dir, w.debounce.clone().unwrap(), recursive);
        w.dir_watches.as_mut().unwrap().insert(key, dw.clone());
        dw
    }

    // Go: watcher.go:284 watcher.removeDirWatch
    pub fn remove_dir_watch(&self, dw: &DirWatch) {
        let mut w = self.mu.lock().unwrap();
        let mut key = dw.dir.clone();
        if dw.recursive {
            key = format!("{}\x00recursive", dw.dir);
        }
        let same = match w.dir_watches.as_ref().and_then(|m| m.get(&key)) {
            Some(existing) => std::ptr::eq(Arc::as_ptr(existing), dw),
            None => false,
        };
        if same {
            w.dir_watches.as_mut().unwrap().remove(&key);
            dw.destroy_debounce();
        }
    }
}

impl Watcher for WatcherStruct {
    // Go: watcher.go:217 watcher.Name
    fn name(&self) -> String {
        self.name.clone()
    }

    // Go: watcher.go:219 watcher.Available
    fn available(&self) -> bool {
        self.factory.is_some()
    }

    // Go: watcher.go:220 watcher.unexported
    fn unexported(&self) {}

    // Go: watcher.go:223 watcher.HasFastRecursiveBackend
    /// HasFastRecursiveBackend implements [Watcher.HasFastRecursiveBackend].
    fn has_fast_recursive_backend(&self) -> bool {
        match self.name.as_str() {
            "windows" | "fsevents" => true,
            _ => false,
        }
    }

    // Go: watcher.go:297 watcher.WatchDirectory
    fn watch_directory(
        &self,
        dir: &str,
        fn_: WatchCallback,
        opts: &[Box<dyn WatchOption>],
    ) -> Result<Box<dyn Watch>, GoError> {
        // PORT: Go `if fn == nil { return nil, errNilCallback }`; a Rust
        // callback is never nil.
        if !self.available() {
            return Err(ERR_UNAVAILABLE.clone());
        }
        let mut dir = filepath_clean(dir);
        if !filepath_is_abs(&dir) {
            return Err(ERR_NOT_ABSOLUTE.clone());
        }
        dir = canonicalize_path(&dir);

        let mut sopts = WatchOptions::default();
        for o in opts {
            o.apply_watch_option(&mut sopts);
        }

        let dw = self.get_or_create_dir_watch(&dir, sopts.recursive);
        let (id, _) = dw.watch(fn_, sopts.ignore.clone());

        let impl_ = match self.get_impl() {
            Ok(impl_) => impl_,
            Err(err) => {
                dw.unwatch(id);
                dw.unref(self);
                return Err(err);
            }
        };
        if let Err(err) = impl_.watch_add(&dw) {
            dw.unwatch(id);
            dw.unref(self);
            return Err(err);
        }
        Ok(Box::new(WatchStruct {
            mu: Mutex::new(false),
            w: self.self_arc(),
            dw,
            impl_,
            id,
        }))
    }

    // Go: watcher.go:332 watcher.WatchFile
    fn watch_file(&self, path: &str, fn_: WatchCallback) -> Result<Box<dyn Watch>, GoError> {
        // PORT: Go `if fn == nil { return nil, errNilCallback }`; a Rust
        // callback is never nil.
        if !self.available() {
            return Err(ERR_UNAVAILABLE.clone());
        }
        let mut path = filepath_clean(path);
        if !filepath_is_abs(&path) {
            return Err(ERR_NOT_ABSOLUTE.clone());
        }
        path = canonicalize_path(&path);
        let dir = filepath_dir(&path);
        if dir == path {
            return Err(ERR_ROOT_PATH.clone());
        }

        self.watch_directory(&dir, file_callback(path, fn_), &[])
    }
}

// Go: path/filepath/path_unix.go IsAbs
// PORT: Go standard library (unix). The crate's `filepath_clean` is the
// unix `filepath.Clean` too.
fn filepath_is_abs(path: &str) -> bool {
    path.starts_with('/')
}

// Go: path/filepath/path.go Dir
// PORT: Go standard library (unix: `VolumeName` is empty).
fn filepath_dir(path: &str) -> String {
    let vol = "";
    let bytes = path.as_bytes();
    let mut i = bytes.len() as isize - 1;
    while i >= vol.len() as isize && bytes[i as usize] != b'/' {
        i -= 1;
    }
    let dir = filepath_clean(&path[vol.len()..(i + 1) as usize]);
    if dir == "." && vol.len() > 2 {
        // must be UNC
        return vol.to_string();
    }
    format!("{vol}{dir}")
}

// Go: watcher.go:356 fileCallback
/// fileCallback wraps a WatchCallback so it only sees events for the
/// specific target path. Errors are always forwarded (with any matching
/// events delivered alongside) so callers don't lose overflow signals
/// just because their target wasn't in the same batch.
pub fn file_callback(target: String, fn_: WatchCallback) -> WatchCallback {
    Arc::new(move |events: Vec<Event>, err: Option<GoError>| {
        let mut filtered: Vec<Event> = Vec::new();
        for e in events {
            if e.path == target {
                filtered.push(e);
            }
        }
        if !filtered.is_empty() || err.is_some() {
            fn_(filtered, err);
        }
    })
}

// Go: watcher.go:370 watch
/// PORT: named `WatchStruct` because the Go interface `Watch` and the
/// struct `watch` have the same Rust name. Go `mu` guards `cancelled`,
/// which is the `bool` inside `mu`.
pub struct WatchStruct {
    pub mu: Mutex<bool>,
    pub w: Arc<WatcherStruct>,
    pub dw: Arc<DirWatch>,
    pub impl_: Arc<dyn WatcherImpl>,
    pub id: u64,
}

impl Watch for WatchStruct {
    // Go: watcher.go:379 watch.Close
    fn close(&self) -> Result<(), GoError> {
        let mut cancelled = self.mu.lock().unwrap();
        if *cancelled {
            return Ok(());
        }
        *cancelled = true;
        let last = self.dw.unwatch(self.id);
        if last {
            self.impl_.watch_remove(&self.dw);
            self.dw.unref(&self.w);
        }
        Ok(())
    }

    // Go: watcher.go:394 watch.unexported
    fn unexported(&self) {}
}

// Go: watcher.go:397 watcherImpl
/// watcherImpl is the internal interface implemented by each platform watcher.
///
/// PORT: Go backends embed `watcherBase`, whose methods are promoted. The
/// default methods here forward to `base()` (the embedded value); a
/// backend overrides a method the way a Go backend declares its own.
pub trait WatcherImpl: Send + Sync {
    fn start(&self) -> Result<(), GoError>;
    fn run(&self) -> Result<(), GoError> {
        self.base().run()
    }
    fn shutdown(&self) {
        self.base().shutdown();
    }

    fn watch_add(&self, w: &Arc<DirWatch>) -> Result<(), GoError> {
        self.base().watch_add(w)
    }
    fn watch_remove(&self, w: &Arc<DirWatch>) {
        self.base().watch_remove(w);
    }
    fn handle_watcher_error(&self, err: DirWatchError) {
        self.base().handle_watcher_error(err);
    }

    fn subscribe(&self, w: &Arc<DirWatch>) -> Result<(), GoError>;
    fn close_watch(&self, w: &Arc<DirWatch>) -> Result<(), GoError>;

    /// PORT: the embedded Go `watcherBase`.
    fn base(&self) -> &WatcherBase;
}

/// PORT: Go `chan struct{}` that is only closed and received from (a
/// one-shot signal). Go replaces such a channel with `make` to reuse it;
/// the port makes a new `SignalChan`.
pub struct SignalChan {
    closed: Mutex<bool>,
    cond: Condvar,
}

impl Default for SignalChan {
    fn default() -> Self {
        SignalChan::new()
    }
}

impl SignalChan {
    /// Go `make(chan struct{})`.
    pub fn new() -> SignalChan {
        SignalChan {
            closed: Mutex::new(false),
            cond: Condvar::new(),
        }
    }

    /// Go `close(ch)`. Closing a closed channel panics, as in Go.
    pub fn close(&self) {
        let mut closed = self.closed.lock().unwrap();
        if *closed {
            panic!("close of closed channel");
        }
        *closed = true;
        self.cond.notify_all();
    }

    /// Go `select { case <-ch: ...; default: ... }`: true when closed.
    pub fn is_closed(&self) -> bool {
        *self.closed.lock().unwrap()
    }

    /// Go `<-ch`: blocks until the channel is closed.
    pub fn wait(&self) {
        let mut closed = self.closed.lock().unwrap();
        while !*closed {
            closed = self.cond.wait(closed).unwrap();
        }
    }

    /// Go `select { case <-ch: ...; case <-time.After(d): ... }`: true when
    /// the channel is closed before `d` passes.
    pub fn wait_timeout(&self, d: Duration) -> bool {
        let closed = self.closed.lock().unwrap();
        let (closed, _) = self
            .cond
            .wait_timeout_while(closed, d, |closed| !*closed)
            .unwrap();
        *closed
    }
}

// Go: watcher.go:412 watcherBase
/// watcherBase provides shared watch-tracking and lifecycle logic.
/// Concrete backends embed it and override subscribe/closeWatch/start.
///
/// PORT: Go `mu` guards `WatcherBaseLocked`. The Go backends also hold
/// `b.mu` (this lock, promoted) while they touch their own fields; the
/// port keeps those fields in a second mutex that is always taken after
/// this one.
#[derive(Default)]
pub struct WatcherBase {
    pub mu: Mutex<WatcherBaseLocked>,
    pub started: SignalChan,

    /// back-reference for virtual dispatch
    pub self_: OnceLock<Weak<dyn WatcherImpl>>,
}

/// PORT: the `watcherBase` fields that Go `b.mu` guards.
#[derive(Default)]
pub struct WatcherBaseLocked {
    /// Go `map[*dirWatch]struct{}`, keyed by the `Arc` pointer.
    pub subscriptions: FxHashMap<usize, Arc<DirWatch>>,
    pub start_err: Option<GoError>,
}

impl WatcherBase {
    // Go: watcher.go:421 watcherBase.init
    // PORT: `started` is made with the value (`Default`).
    pub fn init(&self, self_: Weak<dyn WatcherImpl>) {
        let _ = self.self_.set(self_);
        self.mu.lock().unwrap().subscriptions = FxHashMap::default();
    }

    // PORT: Go reads `b.self`; the port upgrades the weak back-reference.
    fn self_impl(&self) -> Arc<dyn WatcherImpl> {
        self.self_
            .get()
            .and_then(Weak::upgrade)
            .expect("fswatch: watcherBase.init was called and the backend is alive")
    }

    // Go: watcher.go:427 watcherBase.notifyStarted
    pub fn notify_started(&self) {
        if self.started.is_closed() {
            // Do nothing; already started.
        } else {
            self.started.close();
        }
    }

    // Go: watcher.go:436 watcherBase.shutdown
    pub fn shutdown(&self) {}

    // Go: watcher.go:438 watcherBase.run
    // PORT: the goroutine is a `std::thread`; Go's `recover()` is
    // `catch_unwind`, so an `unported!` panic in `start` becomes the start
    // error, as a Go panic does.
    pub fn run(&self) -> Result<(), GoError> {
        let self_impl = self.self_impl();
        std::thread::spawn(move || {
            let result = std::panic::catch_unwind(AssertUnwindSafe(|| self_impl.start()));
            match result {
                Ok(Ok(())) => {}
                Ok(Err(err)) => self_impl.base().handle_start_error(err),
                Err(r) => {
                    // Go: err, ok := r.(error); if !ok { err = fmt.Errorf("%v", r) }
                    let text = if let Some(s) = r.downcast_ref::<&str>() {
                        (*s).to_string()
                    } else if let Some(s) = r.downcast_ref::<String>() {
                        s.clone()
                    } else {
                        format!("{r:?}")
                    };
                    self_impl
                        .base()
                        .handle_start_error(errors::errorf(text, vec![]));
                }
            }
        });
        self.started.wait();
        let b = self.mu.lock().unwrap();
        match &b.start_err {
            Some(err) => Err(err.clone()),
            None => Ok(()),
        }
    }

    // Go: watcher.go:459 watcherBase.handleStartError
    pub fn handle_start_error(&self, err: GoError) {
        let subs: Vec<Arc<DirWatch>> = {
            let mut b = self.mu.lock().unwrap();
            b.start_err = Some(err.clone());
            let mut subs = Vec::with_capacity(b.subscriptions.len());
            for w in b.subscriptions.values() {
                subs.push(w.clone());
            }
            subs
        };
        for w in &subs {
            w.notify_error(err.clone());
        }
        self.notify_started();
    }

    // Go: watcher.go:473 watcherBase.watchAdd
    pub fn watch_add(&self, w: &Arc<DirWatch>) -> Result<(), GoError> {
        let mut b = self.mu.lock().unwrap();
        let key = Arc::as_ptr(w) as usize;
        if b.subscriptions.contains_key(&key) {
            return Ok(());
        }
        self.self_impl().subscribe(w)?;
        b.subscriptions.insert(key, w.clone());
        Ok(())
    }

    // Go: watcher.go:488 watcherBase.watchRemove
    pub fn watch_remove(&self, w: &Arc<DirWatch>) {
        let mut b = self.mu.lock().unwrap();
        let key = Arc::as_ptr(w) as usize;
        if !b.subscriptions.contains_key(&key) {
            return;
        }
        b.subscriptions.remove(&key);
        let _ = self.self_impl().close_watch(w);
    }

    // Go: watcher.go:499 watcherBase.handleWatcherError
    pub fn handle_watcher_error(&self, werr: DirWatchError) {
        self.watch_remove(&werr.dir_watch);
        let dir_watch = werr.dir_watch.clone();
        let text = format!("{}: {}", ERR_WATCH_TERMINATED.error(), werr.error());
        dir_watch.notify_error(errors::errorf(
            text,
            vec![ERR_WATCH_TERMINATED.clone(), werr.to_go_error()],
        ));
    }
}

// ----- dirWatch: per-directory watch state -------------------------

// Go: watcher.go:506 callback
#[derive(Clone)]
pub struct Callback {
    pub id: u64,
    pub fn_: WatchCallback,
    pub ignore: Option<Arc<dyn Fn(&str) -> bool + Send + Sync>>,
}

// Go: watcher.go:513 dirWatchError
/// dirWatchError associates an error with a specific directory watch.
#[derive(Clone)]
pub struct DirWatchError {
    pub err: GoError,
    pub dir_watch: Arc<DirWatch>,
}

impl DirWatchError {
    // Go: watcher.go:518 dirWatchError.Error
    pub fn error(&self) -> String {
        self.err.error()
    }

    // Go: watcher.go:519 dirWatchError.Unwrap
    pub fn unwrap(&self) -> GoError {
        self.err.clone()
    }

    /// PORT: Go returns the `*dirWatchError` as an `error`. The value keeps
    /// its `Error()` text, its `Unwrap()` result and its type
    /// (`errors::as_type::<DirWatchError>`).
    pub fn to_go_error(&self) -> GoError {
        errors::from_value_with_unwrap(self.clone(), self.unwrap())
    }
}

impl std::fmt::Display for DirWatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.error())
    }
}

impl std::fmt::Debug for DirWatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "dirWatchError({:?}, {:?})",
            self.dir_watch.dir,
            self.err.error()
        )
    }
}

/// PORT: Go compares `*dirWatchError` pointers. The port compares the
/// wrapped error value and the dirWatch pointer.
impl PartialEq for DirWatchError {
    fn eq(&self, other: &DirWatchError) -> bool {
        self.err == other.err && Arc::ptr_eq(&self.dir_watch, &other.dir_watch)
    }
}

// Go: watcher.go:523 dirWatch
/// dirWatch holds per-directory state: pending events, registered callbacks,
/// and a reference to the shared debouncer. Each watched directory has one.
///
/// PORT: Go `mu` guards the fields in `DirWatchLocked`. `state` is only
/// used by the fsevents, kqueue and Windows backends (not ported).
pub struct DirWatch {
    pub dir: String,
    pub recursive: bool,
    pub events: EventList,

    /// state stores per-directory platform-specific bookkeeping (fsevents, windows).
    pub state: Mutex<Option<Box<dyn Any + Send>>>,

    pub mu: Mutex<DirWatchLocked>,
}

/// PORT: the `dirWatch` fields that Go `dw.mu` guards.
#[derive(Default)]
pub struct DirWatchLocked {
    pub callbacks: Vec<Callback>,
    pub debounce: Option<Arc<Debounce>>,
    pub next_cbid: u64,
}

// Go: watcher.go:537 newDirWatch
// PORT: `recursive` is a parameter (see getOrCreateDirWatch). The debounce
// key is the dirWatch pointer.
pub fn new_dir_watch(dir: &str, db: Arc<Debounce>, recursive: bool) -> Arc<DirWatch> {
    let dw = Arc::new(DirWatch {
        dir: dir.to_string(),
        recursive,
        events: EventList::default(),
        state: Mutex::new(None),
        mu: Mutex::new(DirWatchLocked::default()),
    });
    dw.mu.lock().unwrap().debounce = Some(db.clone());
    let dw_cb = dw.clone();
    db.add(
        Arc::as_ptr(&dw) as usize,
        Arc::new(move || dw_cb.trigger_callbacks()),
    );
    dw
}

impl DirWatch {
    // Go: watcher.go:544 dirWatch.destroyDebounce
    pub fn destroy_debounce(&self) {
        let db = {
            let mut dw = self.mu.lock().unwrap();
            dw.debounce.take()
        };
        if let Some(db) = db {
            db.remove(self as *const DirWatch as usize);
        }
    }

    // Go: watcher.go:554 dirWatch.notify
    pub fn notify(&self) {
        let (has_cbs, has_events, has_error, db) = {
            let dw = self.mu.lock().unwrap();
            let has_cbs = !dw.callbacks.is_empty();
            let has_events = self.events.size() > 0;
            let has_error = self.events.has_error();
            (has_cbs, has_events, has_error, dw.debounce.clone())
        };

        if has_cbs && (has_events || has_error) {
            if let Some(db) = db {
                db.trigger();
            }
        }
    }

    // Go: watcher.go:567 dirWatch.notifyError
    pub fn notify_error(&self, err: GoError) {
        let cbs = {
            let mut dw = self.mu.lock().unwrap();
            let cbs = dw.callbacks.clone();
            dw.callbacks = Vec::new();
            cbs
        };
        for cb in &cbs {
            (cb.fn_)(Vec::new(), Some(err.clone()));
        }
    }

    // Go: watcher.go:577 dirWatch.triggerCallbacks
    pub fn trigger_callbacks(&self) {
        let (events, err, cbs, recursive) = {
            let dw = self.mu.lock().unwrap();
            let has_error = self.events.has_error();
            let has_events = self.events.size() > 0;
            if dw.callbacks.is_empty() || (!has_events && !has_error) {
                return;
            }
            let (events, err) = self.events.drain();
            let cbs = dw.callbacks.clone();
            let recursive = self.recursive;
            (events, err, cbs, recursive)
        };

        for cb in &cbs {
            let mut cb_events = events.clone();
            if cb.ignore.is_some() || !recursive {
                let mut filtered: Vec<Event> = Vec::with_capacity(events.len());
                for e in &events {
                    if let Some(ignore) = &cb.ignore {
                        if ignore(&e.path) {
                            continue;
                        }
                    }
                    if !recursive && !is_direct_child(&self.dir, &e.path) {
                        continue;
                    }
                    filtered.push(e.clone());
                }
                cb_events = filtered;
            }
            if !cb_events.is_empty() || err.is_some() {
                (cb.fn_)(cb_events, err.clone());
            }
        }
    }
}

// Go: watcher.go:613 isDirectChild
/// isDirectChild reports whether path is an immediate child of dir.
/// Both paths must be absolute. Returns false for path == dir.
pub fn is_direct_child(dir: &str, path: &str) -> bool {
    if !path.starts_with(dir) {
        return false;
    }
    let rest = &path.as_bytes()[dir.len()..];
    if rest.is_empty() {
        return false;
    }
    let separator = std::path::MAIN_SEPARATOR as u8;
    if rest[0] != b'/' && rest[0] != separator {
        return false;
    }
    let rest = &rest[1..];
    !rest.is_empty() && !rest.contains(&b'/') && !rest.contains(&separator)
}

impl DirWatch {
    // Go: watcher.go:628 dirWatch.watch
    pub fn watch(
        &self,
        fn_: WatchCallback,
        ignore: Option<Arc<dyn Fn(&str) -> bool + Send + Sync>>,
    ) -> (u64, bool) {
        let mut dw = self.mu.lock().unwrap();
        dw.next_cbid += 1;
        let id = dw.next_cbid;
        dw.callbacks.push(Callback { id, fn_, ignore });
        (id, true)
    }

    // Go: watcher.go:637 dirWatch.unwatch
    pub fn unwatch(&self, id: u64) -> bool {
        let mut dw = self.mu.lock().unwrap();
        for i in 0..dw.callbacks.len() {
            if dw.callbacks[i].id == id {
                dw.callbacks.remove(i);
                return dw.callbacks.is_empty();
            }
        }
        false
    }

    // Go: watcher.go:649 dirWatch.unref
    pub fn unref(&self, w: &WatcherStruct) {
        let empty = {
            let dw = self.mu.lock().unwrap();
            dw.callbacks.is_empty()
        };
        if empty {
            w.remove_dir_watch(self);
        }
    }
}
