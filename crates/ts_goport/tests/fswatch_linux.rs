//! The Linux file watcher on the real kernel (Go internal/fswatch
//! `TestWatchFileCreate` and `TestSubscribeSubfileUpdate`, default backend
//! only). `fswatch::default()` is inotify here: the rustix shim has no
//! fanotify, so fanotify is never available.
#![cfg(target_os = "linux")]

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::mpsc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use ts_goport::fswatch::{self, Event, EventKind};

fn tmp_dir(name: &str) -> PathBuf {
    let n = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir =
        std::env::temp_dir().join(format!("goport-fswatch-{name}-{}-{n}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    dir.canonicalize().unwrap()
}

/// Watches `dir` and returns the watch and a receiver of its event batches.
fn watch(dir: &Path, recursive: bool) -> (Box<dyn fswatch::Watch>, mpsc::Receiver<Vec<Event>>) {
    let (tx, rx) = mpsc::channel();
    let tx = std::sync::Mutex::new(tx);
    let cb: fswatch::WatchCallback = Arc::new(move |events, err| {
        assert!(err.is_none(), "watch error: {err:?}");
        let _ = tx.lock().unwrap().send(events);
    });
    let opts: Vec<Box<dyn fswatch::WatchOption>> = if recursive {
        vec![fswatch::with_recursive()]
    } else {
        vec![]
    };
    let w = fswatch::default()
        .watch_directory(dir.to_str().unwrap(), cb, &opts)
        .expect("watch_directory");
    (w, rx)
}

/// Waits up to 5 seconds for an event of `kind` on `path`.
fn expect_event(rx: &mpsc::Receiver<Vec<Event>>, kind: EventKind, path: &Path) {
    let want = path.to_str().unwrap();
    let deadline = std::time::Instant::now() + Duration::from_secs(5);
    let mut seen = Vec::new();
    while let Some(left) = deadline.checked_duration_since(std::time::Instant::now()) {
        let Ok(batch) = rx.recv_timeout(left) else {
            break;
        };
        if batch.iter().any(|e| e.kind == kind && e.path == want) {
            return;
        }
        seen.extend(
            batch
                .into_iter()
                .map(|e| format!("{:?} {}", e.kind, e.path)),
        );
    }
    panic!("no {kind:?} event for {want}; saw {seen:?}");
}

#[test]
fn default_watcher_is_inotify() {
    assert_eq!(fswatch::default().name(), "inotify");
    assert!(fswatch::default().available());
}

#[test]
fn file_create_is_an_update() {
    let dir = tmp_dir("create");
    let (w, rx) = watch(&dir, false);
    let f = dir.join("a.ts");
    fs::write(&f, "hello").unwrap();
    expect_event(&rx, EventKind::Update, &f);
    w.close().unwrap();
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn recursive_watch_sees_a_subdirectory_file_update() {
    let dir = tmp_dir("subfile");
    let sub = dir.join("src");
    fs::create_dir(&sub).unwrap();
    let f = sub.join("b.ts");
    fs::write(&f, "v1").unwrap();
    let (w, rx) = watch(&dir, true);
    fs::write(&f, "v2-longer").unwrap();
    expect_event(&rx, EventKind::Update, &f);
    w.close().unwrap();
    fs::remove_dir_all(&dir).unwrap();
}
