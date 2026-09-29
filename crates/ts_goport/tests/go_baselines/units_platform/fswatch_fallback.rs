//! Go: `internal/fswatch/fallback_test.go` (added by tsgo#4661).
//!
//! PORT: Go builds `&fallbackWatcher{primary, secondary}` in the package;
//! the Rust `FallbackWatcher` fields are public for these tests. Go's
//! `Fanotify().(*fallbackWatcher)` type assertion is a pointer comparison
//! with the package watcher `FANOTIFY_FALLBACK_WATCHER`.

use std::sync::{Arc, Mutex};

use ts_goport::fswatch::{
    self, ERR_FILESYSTEM_UNSUPPORTED, ERR_UNAVAILABLE, FallbackWatcher, Watch, WatchCallback,
    WatchDirectoryRequest, WatchOption, Watcher,
};
use ts_goport::gostd::{GoError, errors};

/// The fields of `fakeFallbackWatcher` that Go `mu` guards.
#[derive(Default)]
struct FakeFallbackState {
    watched: Vec<String>,
    closed: Vec<String>,
}

// Go: fallback_test.go:12 fakeFallbackWatch
/// PORT: Go points at the whole `fakeFallbackWatcher`; the watch only needs
/// its guarded state, which is shared through an `Arc`.
struct FakeFallbackWatch {
    watcher: Arc<Mutex<FakeFallbackState>>,
    dir: String,
}

impl Watch for FakeFallbackWatch {
    // Go: fallback_test.go:17 fakeFallbackWatch.Close
    fn close(&self) -> Result<(), GoError> {
        self.watcher.lock().unwrap().closed.push(self.dir.clone());
        Ok(())
    }

    // Go: fallback_test.go:24 fakeFallbackWatch.unexported
    fn unexported(&self) {}
}

// Go: fallback_test.go:26 fakeFallbackWatcher
struct FakeFallbackWatcher {
    mu: Arc<Mutex<FakeFallbackState>>,
    name: String,
    fail_with: Option<GoError>,
    fail_dir: Option<Box<dyn Fn(&str) -> bool + Send + Sync>>,
}

impl FakeFallbackWatcher {
    fn new(
        name: &str,
        fail_with: Option<GoError>,
        fail_dir: Option<Box<dyn Fn(&str) -> bool + Send + Sync>>,
    ) -> Arc<FakeFallbackWatcher> {
        Arc::new(FakeFallbackWatcher {
            mu: Arc::new(Mutex::new(FakeFallbackState::default())),
            name: name.to_string(),
            fail_with,
            fail_dir,
        })
    }

    // Go: fallback_test.go:39 fakeFallbackWatcher.shouldFail
    fn should_fail(&self, dir: &str) -> bool {
        self.fail_with.is_some() && self.fail_dir.as_ref().is_none_or(|fail_dir| fail_dir(dir))
    }

    /// Go `fmt.Errorf("%s: %w", w.name, w.failWith)`.
    fn fail_error(&self) -> GoError {
        let fail_with = self.fail_with.clone().expect("shouldFail checked failWith");
        errors::errorf(
            format!("{}: {}", self.name, fail_with.error()),
            vec![fail_with],
        )
    }

    // Go: fallback_test.go:75 fakeFallbackWatcher.watchedDirs
    fn watched_dirs(&self) -> Vec<String> {
        let mut dirs = self.mu.lock().unwrap().watched.clone();
        dirs.sort();
        dirs
    }

    // Go: fallback_test.go:83 fakeFallbackWatcher.closedDirs
    fn closed_dirs(&self) -> Vec<String> {
        let mut dirs = self.mu.lock().unwrap().closed.clone();
        dirs.sort();
        dirs
    }
}

impl Watcher for FakeFallbackWatcher {
    // Go: fallback_test.go:35 fakeFallbackWatcher.Name
    fn name(&self) -> String {
        self.name.clone()
    }

    // Go: fallback_test.go:36 fakeFallbackWatcher.Available
    fn available(&self) -> bool {
        true
    }

    // Go: fallback_test.go:37 fakeFallbackWatcher.HasFastRecursiveBackend
    fn has_fast_recursive_backend(&self) -> bool {
        false
    }

    // Go: fallback_test.go:43 fakeFallbackWatcher.WatchDirectory
    fn watch_directory(
        &self,
        dir: &str,
        _fn: WatchCallback,
        _opts: &[Box<dyn WatchOption>],
    ) -> Result<Box<dyn Watch>, GoError> {
        let mut state = self.mu.lock().unwrap();
        if self.should_fail(dir) {
            return Err(self.fail_error());
        }
        state.watched.push(dir.to_string());
        Ok(Box::new(FakeFallbackWatch {
            watcher: self.mu.clone(),
            dir: dir.to_string(),
        }))
    }

    // Go: fallback_test.go:53 fakeFallbackWatcher.WatchDirectories
    fn watch_directories(
        &self,
        requests: &[WatchDirectoryRequest<'_>],
    ) -> Result<Vec<Box<dyn Watch>>, GoError> {
        let mut state = self.mu.lock().unwrap();
        for request in requests {
            if self.should_fail(&request.dir) {
                return Err(self.fail_error());
            }
        }
        let mut watches: Vec<Box<dyn Watch>> = Vec::with_capacity(requests.len());
        for request in requests {
            state.watched.push(request.dir.clone());
            watches.push(Box::new(FakeFallbackWatch {
                watcher: self.mu.clone(),
                dir: request.dir.clone(),
            }));
        }
        Ok(watches)
    }

    // Go: fallback_test.go:69 fakeFallbackWatcher.WatchFile
    fn watch_file(&self, path: &str, fn_: WatchCallback) -> Result<Box<dyn Watch>, GoError> {
        self.watch_directory(path, fn_, &[])
    }

    // Go: fallback_test.go:73 fakeFallbackWatcher.unexported
    fn unexported(&self) {}
}

/// Go `func([]Event, error) {}`.
fn noop() -> WatchCallback {
    Arc::new(|_, _| {})
}

/// Go `WatchDirectoryRequest{Dir: dir, Callback: func([]Event, error) {}}`.
fn request(dir: &str) -> WatchDirectoryRequest<'static> {
    WatchDirectoryRequest {
        dir: dir.to_string(),
        callback: noop(),
        options: &[],
    }
}

/// Go `t.Cleanup(func() { for _, watch := range watches { _ = watch.Close() } })`.
fn close_all(watches: &[Box<dyn Watch>]) {
    for watch in watches {
        let _ = watch.close();
    }
}

// Go: fallback_test.go:91 TestFallbackWatcherRoutesUnsupportedDirectories
#[test]
fn test_fallback_watcher_routes_unsupported_directories() {
    let primary = FakeFallbackWatcher::new(
        "fanotify",
        Some(ERR_FILESYSTEM_UNSUPPORTED.clone()),
        Some(Box::new(|dir: &str| dir.starts_with("/mnt/fuse"))),
    );
    let secondary = FakeFallbackWatcher::new("inotify", None, None);
    let watcher = FallbackWatcher {
        primary: primary.clone(),
        secondary: secondary.clone(),
    };

    let requests = [
        request("/project"),
        request("/project/src"),
        request("/mnt/fuse/deps"),
        request("/mnt/fuse/deps/a"),
    ];
    let watches = watcher
        .watch_directories(&requests)
        .unwrap_or_else(|err| panic!("WatchDirectories: {}", err.error()));

    let (got, want) = (primary.watched_dirs(), ["/project", "/project/src"]);
    assert!(got == want, "primary watched {got:?}, want {want:?}");
    let (got, want) = (
        secondary.watched_dirs(),
        ["/mnt/fuse/deps", "/mnt/fuse/deps/a"],
    );
    assert!(got == want, "secondary watched {got:?}, want {want:?}");
    close_all(&watches);
}

// Go: fallback_test.go:126 TestFallbackWatcherDoesNotFallbackForUnrelatedError
#[test]
fn test_fallback_watcher_does_not_fallback_for_unrelated_error() {
    let primary = FakeFallbackWatcher::new("fanotify", Some(ERR_UNAVAILABLE.clone()), None);
    let secondary = FakeFallbackWatcher::new("inotify", None, None);
    let watcher = FallbackWatcher {
        primary,
        secondary: secondary.clone(),
    };

    let err = watcher.watch_directory("/project", noop(), &[]).err();
    assert!(
        err.as_ref()
            .is_some_and(|err| errors::is(err, &ERR_UNAVAILABLE)),
        "WatchDirectory error = {:?}, want ErrUnavailable",
        err.as_ref().map(GoError::error)
    );
    let got = secondary.watched_dirs();
    assert!(got.is_empty(), "secondary watched {got:?}, want no watches");
}

// Go: fallback_test.go:142 TestFallbackWatcherDoesNotUseSecondaryOnHappyPath
#[test]
fn test_fallback_watcher_does_not_use_secondary_on_happy_path() {
    let primary = FakeFallbackWatcher::new("fanotify", None, None);
    let secondary = FakeFallbackWatcher::new(
        "inotify",
        Some(errors::new("secondary should not be used")),
        None,
    );
    let watcher = FallbackWatcher {
        primary,
        secondary: secondary.clone(),
    };

    let watches = watcher
        .watch_directories(&[request("/project"), request("/project/src")])
        .unwrap_or_else(|err| panic!("WatchDirectories: {}", err.error()));
    let got = secondary.watched_dirs();
    assert!(got.is_empty(), "secondary watched {got:?}, want no watches");
    close_all(&watches);
}

// Go: fallback_test.go:166 TestFallbackWatcherRollsBackRoutedWatchesOnFailure
#[test]
fn test_fallback_watcher_rolls_back_routed_watches_on_failure() {
    let primary = FakeFallbackWatcher::new(
        "fanotify",
        Some(ERR_FILESYSTEM_UNSUPPORTED.clone()),
        Some(Box::new(|dir: &str| dir != "/project")),
    );
    let secondary = FakeFallbackWatcher::new(
        "inotify",
        Some(ERR_UNAVAILABLE.clone()),
        Some(Box::new(|dir: &str| dir == "/broken")),
    );
    let watcher = FallbackWatcher {
        primary: primary.clone(),
        secondary: secondary.clone(),
    };

    let err = watcher
        .watch_directories(&[
            request("/project"),
            request("/mnt/fuse"),
            request("/broken"),
        ])
        .err();
    assert!(
        err.as_ref()
            .is_some_and(|err| errors::is(err, &ERR_UNAVAILABLE)),
        "WatchDirectories error = {:?}, want ErrUnavailable",
        err.as_ref().map(GoError::error)
    );
    let (got, want) = (primary.closed_dirs(), ["/project"]);
    assert!(got == want, "primary closed {got:?}, want {want:?}");
    let (got, want) = (secondary.closed_dirs(), ["/mnt/fuse"]);
    assert!(got == want, "secondary closed {got:?}, want {want:?}");
}

// Go: fallback_test.go:197 TestFanotifyUsesInternalInotifyFallback
#[test]
fn test_fanotify_uses_internal_inotify_fallback() {
    let fanotify = fswatch::fanotify();
    let fallback: &Arc<FallbackWatcher> = &fswatch::FANOTIFY_FALLBACK_WATCHER;
    assert!(
        std::ptr::addr_eq(Arc::as_ptr(&fanotify), Arc::as_ptr(fallback)),
        "Fanotify() = {}, want *fallbackWatcher",
        fanotify.name()
    );
    assert!(
        std::ptr::addr_eq(
            Arc::as_ptr(&fallback.primary),
            Arc::as_ptr(&*fswatch::FANOTIFY_WATCHER)
        ),
        "Fanotify primary = {}, want package fanotify watcher",
        fallback.primary.name()
    );
    assert!(
        std::ptr::addr_eq(
            Arc::as_ptr(&fallback.secondary),
            Arc::as_ptr(&*fswatch::INOTIFY_WATCHER)
        ),
        "Fanotify secondary = {}, want package inotify watcher",
        fallback.secondary.name()
    );
}
