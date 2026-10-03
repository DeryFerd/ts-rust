//! Go: `internal/fswatch/fsevents_darwin_shared_test.go` and
//! `fsevents_darwin_nfd_test.go` (darwin), for the FSEvents backend
//! (`fswatch::fsevents_darwin`, on the `notify` crate). Go's files share the
//! package of `watcher_test.go`, so this is a child module of
//! `fswatch_watcher.rs` and uses its helpers.
//!
//! PORT: Go runs these tests with `*testing.T`; the port runs each body
//! with `run_with_retry`, as the other fswatch tests.
//!
//! Not ported: the tests of CoreFoundation case folding and of the
//! case-insensitive volume query (`TestFSEventsConsolidatedDifferentCasing`,
//! `TestFSEventsConsolidatedExpansion`, `TestFSEventsExpansionRouting`,
//! `TestFSEventsLazyPathFolding`, `TestDarwinWatchFileComparison`,
//! `TestNativePathComparerKeys`, `TestPathComparerVolumeQueryError`,
//! `TestFSEventsDifferentCasing`, `TestFSEventsWatchFileDifferentCasing`,
//! `TestNativePathFold`, `TestFSEventsExpansionAliases` and
//! `TestFSEventsFoldDistinctNames`): the port has no native path folding
//! (PORTING.md, "Not ported"). `TestCallbackASMTouchesOnlySafeRegisters`
//! tests Go's assembly trampoline. `TestNormalizeNFC`,
//! `TestNormalizeNFCASCIIFastPath` and `TestIsASCII` are unit tests in
//! `src/fswatch/canonicalize_darwin.rs`.

use super::*;

use ts_goport::fswatch::fsevents_darwin::{
    FSEVENTS_PATHS_PER_STREAM, FsEventsBackend, FseventsState, FseventsWatchSnapshot,
    fs_events_display_path, fs_events_overflow_matches, new_fs_events_backend,
    start_fs_events_streams, watches_for_fs_events_paths,
};
use ts_goport::fswatch::{RECURSIVE_CONSOLIDATE_THRESHOLD, new_watcher};

// Go: fsevents_darwin_nfd_test.go:26 nfcE and nfdE
const NFC_E: &str = "\u{00e9}";
const NFD_E: &str = "e\u{0301}";

fn run(name: &str, body: &(dyn Fn(&T) + Sync)) {
    if let Err(err) = run_with_retry(name, body) {
        panic!("{name}: {err}");
    }
}

// Go: fsevents_darwin_shared_test.go:17 newTestFSEventsWatcher
/// A watcher with its own FSEvents backend.
fn new_test_fs_events_watcher() -> Arc<dyn Watcher> {
    new_watcher("fsevents", |w| {
        w.factory = Some(|| -> Arc<dyn WatcherImpl> { new_fs_events_backend() });
    })
}

/// The backend of `shared_stream_watcher`, which Go reads through the
/// `impl` pointer of newTestFSEventsWatcher.
static SHARED_STREAM_IMPL: Mutex<Option<Arc<FsEventsBackend>>> = Mutex::new(None);

fn shared_stream_watcher() -> Arc<dyn Watcher> {
    new_watcher("fsevents", |w| {
        w.factory = Some(|| -> Arc<dyn WatcherImpl> {
            let b = new_fs_events_backend();
            *SHARED_STREAM_IMPL.lock().unwrap() = Some(b.clone());
            b
        });
    })
}

/// A dirWatch with only the fields that the routing tests set.
fn routing_dir_watch(t: &T, dir: &str, physical_dir: &str, ignore_case: bool) -> Arc<DirWatch> {
    let w = new_dir_watch(
        dir,
        physical_dir,
        new_debounce(),
        false,
        PathComparer { ignore_case },
    );
    let w2 = w.clone();
    t.cleanup(move || w2.destroy_debounce());
    w
}

fn snapshot(w: Arc<DirWatch>) -> FseventsWatchSnapshot {
    FseventsWatchSnapshot {
        w,
        state: Arc::new(FseventsState::default()),
    }
}

// Go: fsevents_darwin_shared_test.go:28 TestFSEventsSharedStreamAcrossWatches
#[test]
fn test_fs_events_shared_stream_across_watches() {
    run("TestFSEventsSharedStreamAcrossWatches", &|t| {
        let watcher = shared_stream_watcher();
        let root = new_t_tmp_dir(t);
        let mut subs = Vec::new();
        for i in 0..5 {
            let dir = join(&root, &format!("dir{i}"));
            mkdir_all(&dir);
            let sub = watcher
                .watch_directory(&dir, noop_callback(), &[])
                .unwrap_or_else(|e| fatal(e.error()));
            subs.push(Arc::<dyn Watch>::from(sub));
        }
        let closing = subs.clone();
        t.cleanup(move || {
            for sub in closing {
                let _ = sub.close();
            }
        });

        let b = SHARED_STREAM_IMPL
            .lock()
            .unwrap()
            .clone()
            .expect("the backend");
        let (stream_count, watch_count) = (b.stream_count(), b.watch_count());
        if stream_count != 1 {
            fatal(format!(
                "expected one shared FSEvents stream, got {stream_count}"
            ));
        }
        if watch_count != subs.len() {
            fatal(format!(
                "expected {} logical watches, got {watch_count}",
                subs.len()
            ));
        }
    });
}

// Go: fsevents_darwin_shared_test.go:65 TestFSEventsSharedStreamRoutesEvents
#[test]
fn test_fs_events_shared_stream_routes_events() {
    run("TestFSEventsSharedStreamRoutesEvents", &|t| {
        let watcher = new_test_fs_events_watcher();
        let root = new_t_tmp_dir(t);
        let dir_a = join(&root, "a");
        let dir_b = join(&root, "b");
        mkdir_all(&dir_a);
        mkdir_all(&dir_b);

        sleep(pre_subscribe_sleep(&watcher));
        let rec_a = Recorder::for_watcher(t, &watcher);
        let sub_a: Arc<dyn Watch> = Arc::from(
            watcher
                .watch_directory(&dir_a, rec_a.callback(), &[])
                .unwrap_or_else(|e| fatal(e.error())),
        );
        let s = sub_a.clone();
        t.cleanup(move || {
            let _ = s.close();
        });

        let rec_b = Recorder::for_watcher(t, &watcher);
        let sub_b: Arc<dyn Watch> = Arc::from(
            watcher
                .watch_directory(&dir_b, rec_b.callback(), &[])
                .unwrap_or_else(|e| fatal(e.error())),
        );
        let s = sub_b.clone();
        t.cleanup(move || {
            let _ = s.close();
        });
        sleep(settle_sleep(&watcher));

        let file_a = join(&dir_a, "file.ts");
        write_file(&file_a, "export {}");
        expect_contains(&rec_a, UPDATE, &file_a);
        assert_no_events_for_path(
            &rec_b.drain_quiet(ms(500)),
            &file_a,
            "sibling watch saw event",
        );

        let file_b = join(&dir_b, "file.ts");
        write_file(&file_b, "export {}");
        expect_contains(&rec_b, UPDATE, &file_b);
        assert_no_events_for_path(
            &rec_a.drain_quiet(ms(500)),
            &file_b,
            "sibling watch saw event",
        );
    });
}

// Go: fsevents_darwin_shared_test.go:111 setupFSEventsConsolidatedParent
fn setup_fs_events_consolidated_parent(t: &T) -> (Arc<dyn Watcher>, String) {
    let watcher = new_test_fs_events_watcher();
    let parent = join(&new_t_tmp_dir(t), "parent");
    let mut subs: Vec<Arc<dyn Watch>> = Vec::new();
    for i in 0..RECURSIVE_CONSOLIDATE_THRESHOLD {
        let dir = join(&parent, &format!("pkg{i}"));
        mkdir_all(&dir);
        let sub = watcher
            .watch_directory(&dir, noop_callback(), &[])
            .unwrap_or_else(|e| fatal(e.error()));
        subs.push(Arc::from(sub));
    }
    t.cleanup(move || {
        for sub in subs {
            let _ = sub.close();
        }
    });
    (watcher, parent)
}

// Go: fsevents_darwin_shared_test.go:141 TestFSEventsConsolidatedWatchValidatesLogicalRoot
#[test]
fn test_fs_events_consolidated_watch_validates_logical_root() {
    run("TestFSEventsConsolidatedWatchValidatesLogicalRoot", &|t| {
        let (watcher, parent) = setup_fs_events_consolidated_parent(t);

        if let Ok(sub) = watcher.watch_directory(&join(&parent, "missing"), noop_callback(), &[]) {
            let _ = sub.close();
            fatal("expected error subscribing to missing consolidated child");
        }

        let file = join(&parent, "file");
        write_file(&file, "x");
        if let Ok(sub) = watcher.watch_directory(&file, noop_callback(), &[]) {
            let _ = sub.close();
            fatal("expected error subscribing to file consolidated child");
        }
    });
}

// Go: fsevents_darwin_shared_test.go:161 TestFSEventsConsolidatedWatchTerminatesLogicalRoot
#[test]
fn test_fs_events_consolidated_watch_terminates_logical_root() {
    run("TestFSEventsConsolidatedWatchTerminatesLogicalRoot", &|t| {
        let (watcher, parent) = setup_fs_events_consolidated_parent(t);

        let watched = join(&parent, "watched");
        mkdir_all(&watched);
        let r = Recorder::for_watcher(t, &watcher);
        let sub: Arc<dyn Watch> = Arc::from(
            watcher
                .watch_directory(&watched, r.callback(), &[with_recursive()])
                .unwrap_or_else(|e| fatal(e.error())),
        );
        let s = sub.clone();
        t.cleanup(move || {
            let _ = s.close();
        });
        sleep(settle_sleep(&watcher));

        remove_all(&watched);
        expect_event_sequence(&r, &[w(DELETE, &watched)]);

        let deadline = Instant::now() + r.deadline();
        while Instant::now() < deadline && r.err_count() == 0 {
            sleep(ms(20));
        }
        let errs = r.take_errs();
        if !errs
            .iter()
            .any(|err| errors::is(err, &ERR_WATCH_TERMINATED))
        {
            let errs: Vec<String> = errs.iter().map(|err| err.error()).collect();
            fatal(format!(
                "expected ErrWatchTerminated after watched dir delete, got errs={errs:?}"
            ));
        }
    });
}

// Go: fsevents_darwin_shared_test.go:203 TestFSEventsSharedStreamFallsBackToChunks
#[test]
fn test_fs_events_shared_stream_falls_back_to_chunks() {
    run("TestFSEventsSharedStreamFallsBackToChunks", &|t| {
        let count = FSEVENTS_PATHS_PER_STREAM * 2 + 1;
        let watches: Vec<FseventsWatchSnapshot> = (0..count)
            .map(|i| {
                let dir = format!("/watch/dir{i:04}");
                snapshot(routing_dir_watch(t, &dir, &dir, false))
            })
            .collect();

        let calls = RefCell::new(Vec::new());
        let watch_calls = RefCell::new(Vec::new());
        let streams = start_fs_events_streams(&watches, |paths, stream_watches| {
            calls.borrow_mut().push(paths.len());
            watch_calls.borrow_mut().push(stream_watches.len());
            if calls.borrow().len() == 1 {
                return Err(errors::new("error starting FSEvents stream"));
            }
            Ok(())
        })
        .unwrap_or_else(|e| fatal(e.error()));
        if streams.len() != 3 {
            fatal(format!("expected 3 chunked streams, got {}", streams.len()));
        }
        let want_calls = vec![
            count,
            FSEVENTS_PATHS_PER_STREAM,
            FSEVENTS_PATHS_PER_STREAM,
            1,
        ];
        assert_eq!(*calls.borrow(), want_calls, "startStream calls");
        assert_eq!(*watch_calls.borrow(), want_calls, "startStream watch calls");
    });
}

// Go: fsevents_darwin_shared_test.go:240 TestWatchesForFSEventsPaths
#[test]
fn test_watches_for_fs_events_paths() {
    run("TestWatchesForFSEventsPaths", &|t| {
        let watches: Vec<FseventsWatchSnapshot> = ["/watch/a", "/watch/b", "/watch/c"]
            .into_iter()
            .map(|dir| snapshot(routing_dir_watch(t, dir, dir, false)))
            .collect();

        let got = watches_for_fs_events_paths(
            &watches,
            &["/watch/a".to_string(), "/watch/c".to_string()],
        );
        let mut got_paths: Vec<String> = got.iter().map(|w| w.w.physical_dir.clone()).collect();
        got_paths.sort();
        assert_eq!(
            got_paths,
            ["/watch/a", "/watch/c"],
            "watchesForFSEventsPaths"
        );
    });
}

// Go: fsevents_darwin_shared_test.go:265 TestFSEventsOverflowMatchesWatch
#[test]
fn test_fs_events_overflow_matches_watch() {
    run("TestFSEventsOverflowMatchesWatch", &|t| {
        let w = routing_dir_watch(t, "/logical/root", "/physical/root", false);
        let cases = [
            ("physical root", "/physical/root", true),
            ("physical descendant", "/physical/root/sub", true),
            ("physical ancestor", "/physical", true),
            ("logical root", "/logical/root", true),
            ("logical descendant", "/logical/root/sub", true),
            ("logical ancestor", "/logical", true),
            ("unrelated", "/other/root", false),
            ("sibling prefix", "/physical/root2", false),
        ];
        let mut failures = crate::units_platform::Failures::new("TestFSEventsOverflowMatchesWatch");
        for (name, raw_path, want) in cases {
            failures.check_eq(name, fs_events_overflow_matches(&w, raw_path), want);
        }
        failures.finish();
    });
}

// Go: fsevents_darwin_shared_test.go:296 TestFSEventsCaseSensitiveRouting
#[test]
fn test_fs_events_case_sensitive_routing() {
    run("TestFSEventsCaseSensitiveRouting", &|t| {
        let mut errs = Vec::new();
        for ignore_case in [false, true] {
            let w = routing_dir_watch(t, "/logical/root", "/physical/root", ignore_case);
            for root in ["/PHYSICAL/ROOT", "/LOGICAL/ROOT"] {
                for suffix in ["", "/File.ts", "/Nested/File.ts"] {
                    let got = fs_events_display_path(&w, &format!("{root}{suffix}"));
                    if got.is_some() != ignore_case
                        || got
                            .as_ref()
                            .is_some_and(|path| *path != format!("{}{suffix}", w.dir))
                    {
                        errs.push(format!(
                            "display path for {:?}, ignoreCase={ignore_case}: got {got:?}",
                            format!("{root}{suffix}")
                        ));
                    }
                }
                if fs_events_overflow_matches(&w, &format!("{root}/Nested")) != ignore_case {
                    errs.push(format!(
                        "overflow descendant {root:?}, ignoreCase={ignore_case}"
                    ));
                }
                let parent = &root[..root.rfind('/').unwrap_or(0).max(1)];
                if fs_events_overflow_matches(&w, parent) != ignore_case {
                    errs.push(format!(
                        "overflow ancestor {root:?}, ignoreCase={ignore_case}"
                    ));
                }
                if fs_events_display_path(&w, &format!("{root}2/File.ts")).is_some() {
                    errs.push(format!(
                        "matched sibling of {root:?}, ignoreCase={ignore_case}"
                    ));
                }
                if fs_events_overflow_matches(&w, &format!("{root}2")) {
                    errs.push(format!(
                        "overflow matched sibling of {root:?}, ignoreCase={ignore_case}"
                    ));
                }
            }
        }
        if !errs.is_empty() {
            fatal(errs.join("\n"));
        }
    });
}

// Go: fsevents_darwin_nfd_test.go:120 TestFSEventsNFDOnDiskNFCSubscribe
#[test]
fn test_fs_events_nfd_on_disk_nfc_subscribe() {
    run("TestFSEventsNFDOnDiskNFCSubscribe", &|t| {
        let parent = new_t_tmp_dir(t);
        let nfd_dir = join(&parent, &format!("caf{NFD_E}-dir"));
        let nfc_dir = join(&parent, &format!("caf{NFC_E}-dir"));
        mkdir(&nfd_dir);

        let (r, _) = subscribe_for(t, &nfc_dir, &fswatch::fs_events());

        let nfc_child = join(&nfc_dir, "hello.txt");
        write_file(&nfc_child, "hi");

        let got = r.next(r.deadline());
        if got.is_empty() {
            fatal("no events received");
        }
        for e in &got {
            if e.path != nfc_child {
                fatal(format!(
                    "event path not in subscriber's (NFC) form:\n  want: {nfc_child:?}\n  got:  {:?}",
                    e.path
                ));
            }
        }
    });
}

// Go: fsevents_darwin_nfd_test.go:155 TestFSEventsNFDOnDiskNFCWatchFile
#[test]
fn test_fs_events_nfd_on_disk_nfc_watch_file() {
    run("TestFSEventsNFDOnDiskNFCWatchFile", &|t| {
        let dir = new_t_tmp_dir(t);
        let nfd_target = join(&dir, &format!("r{NFD_E}sum{NFD_E}.txt"));
        let nfc_target = join(&dir, &format!("r{NFC_E}sum{NFC_E}.txt"));

        let (r, _) = subscribe_file_for(t, &nfc_target, &fswatch::fs_events());

        write_file(&nfd_target, "hi");

        let got = r.next(r.deadline());
        if got.is_empty() {
            fatal(
                "WatchFile delivered no events: FSEvents reported the path in its on-disk (NFD) form and the e.Path == path filter in WatchFile dropped it",
            );
        }
        for e in &got {
            if e.path != nfc_target {
                fatal(format!(
                    "event path mismatch:\n  want: {nfc_target:?}\n  got:  {:?}",
                    e.path
                ));
            }
        }
    });
}
