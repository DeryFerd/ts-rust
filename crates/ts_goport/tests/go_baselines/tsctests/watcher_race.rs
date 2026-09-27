//! Go: internal/execute/tsctests/watcher_race_test.go (watcher concurrency
//! tests).
//!
//! PORT: Go calls `DoCycle` from many goroutines at once and relies on
//! `go test -race`. The `execute::watcher::Watcher` holds `Rc`s and is not
//! `Send`, so Rust already rejects concurrent `DoCycle` calls at compile
//! time. Each test keeps Go's operations and counts. The file writes and
//! removes of the Go goroutines run on threads through the `Send` `MapFs`
//! handle (Go `sys.fsFromFileMap()` is the iovfs view over it, which is
//! `MapFs::fs`). All `DoCycle` calls of the Go goroutines run on the test
//! thread while those writer threads run.
//!
//! PORT: the compiler runs in this process with the OS override for the
//! test system, which is for the whole process. So each test runs in a
//! child process of its own (`run_test_in_child`).

use std::rc::Rc;
use std::sync::mpsc::{self, RecvTimeoutError};
use std::thread;
use std::time::Duration;

use ts_goport::execute::tsc::{CommandLineResult, ExitStatus, Watcher};
use ts_goport::gostd::{Context, context};

use crate::support::child::{command_line_in_process, new_in_process_test_sys, run_test_in_child};
use crate::support::runner::{FileMap, TscInput};
use crate::support::test_sys::TestSys;
use crate::support::vfstest::MapFile;

/// The stack of the thread that runs the build in
/// `build_watch_stops_when_context_is_cancelled` (as child.rs).
const STACK_SIZE: usize = 1 << 30;

/// Go `FileMap{...}` literal.
fn file_map<const N: usize>(entries: [(&str, MapFile); N]) -> FileMap {
    entries
        .into_iter()
        .map(|(path, file)| (path.to_string(), file))
        .collect()
}

/// Go `execute.CommandLine(ctx, sys, args, sys)`, run in this process.
fn command_line(ctx: &Context, sys: &Rc<TestSys>, args: &[&str]) -> CommandLineResult {
    let args: Vec<String> = args.iter().map(|arg| arg.to_string()).collect();
    command_line_in_process(ctx, sys, &args)
}

/// PORT: `n` `DoCycle` calls of Go goroutines, run on the test thread (the
/// watcher is not `Send`).
fn do_cycles(w: &mut dyn Watcher, n: usize) {
    for _ in 0..n {
        w.do_cycle();
    }
}

// Go: watcher_race_test.go:18 createTestWatcher
/// createTestWatcher sets up a minimal project with a tsconfig and
/// returns a Watcher ready for concurrent testing, plus the TestSys
/// for file manipulation.
///
/// PORT: Go also asserts `result.Watcher.(*execute.Watcher)`. The
/// `tsc::Watcher` trait object has no downcast, and the tests only call
/// `do_cycle`, so this returns the trait object.
fn create_test_watcher() -> (Box<dyn Watcher>, Rc<TestSys>) {
    let input = TscInput {
        files: file_map([
            (
                "/home/src/workspaces/project/a.ts",
                "const a: number = 1;".into(),
            ),
            (
                "/home/src/workspaces/project/b.ts",
                r#"import { a } from "./a"; export const b = a;"#.into(),
            ),
            ("/home/src/workspaces/project/tsconfig.json", "{}".into()),
        ]),
        command_line_args: vec!["--watch".to_string()],
        ..Default::default()
    };
    let sys = new_in_process_test_sys(&input, &["--watch"]);
    let result = command_line(&context::background(), &sys, &["--watch"]);
    let w = result
        .watcher
        .expect("expected Watcher to be non-nil in watch mode");
    (w, sys)
}

// Go: watcher_race_test.go:44 TestWatcherConcurrentDoCycle
/// TestWatcherConcurrentDoCycle calls DoCycle from multiple goroutines
/// while modifying source files, exposing data races on Watcher fields
/// such as configModified, program, config, and the underlying
/// FileWatcher state. Run with -race to detect.
#[test]
fn watcher_concurrent_do_cycle() {
    run_test_in_child(
        "tsctests::watcher_race::watcher_concurrent_do_cycle",
        || {
            let (mut w, sys) = create_test_watcher();
            let map_fs = sys.map_fs();

            thread::scope(|s| {
                for i in 0..8 {
                    let map_fs = map_fs.clone();
                    s.spawn(move || {
                        let fs = map_fs.fs();
                        for j in 0..10 {
                            let _ = fs.write_file(
                                "/home/src/workspaces/project/a.ts",
                                &format!("const a: number = {};", i * 10 + j),
                            );
                        }
                    });
                }
                // The DoCycle calls of the 8 goroutines above.
                do_cycles(w.as_mut(), 8 * 10);
            });
        },
    );
}

// Go: watcher_race_test.go:70 TestWatcherDoCycleWithConcurrentStateReads
/// TestWatcherDoCycleWithConcurrentStateReads calls DoCycle from
/// multiple goroutines, some modifying files and some not, to test
/// concurrent access to all Watcher and FileWatcher state.
#[test]
fn watcher_do_cycle_with_concurrent_state_reads() {
    run_test_in_child(
        "tsctests::watcher_race::watcher_do_cycle_with_concurrent_state_reads",
        || {
            let (mut w, sys) = create_test_watcher();
            let map_fs = sys.map_fs();

            thread::scope(|s| {
                // DoCycle goroutines
                for i in 0..4 {
                    let map_fs = map_fs.clone();
                    s.spawn(move || {
                        let fs = map_fs.fs();
                        for j in 0..15 {
                            let _ = fs.write_file(
                                "/home/src/workspaces/project/a.ts",
                                &format!("const a: number = {};", i * 15 + j),
                            );
                        }
                    });
                }
                // The DoCycle calls of the 4 goroutines above, then of the 8 state
                // reader goroutines (50 rounds of 4 calls each).
                do_cycles(w.as_mut(), 4 * 15 + 8 * 50 * 4);
            });
        },
    );
}

// Go: watcher_race_test.go:109 TestWatcherConcurrentFileChangesAndDoCycle
/// TestWatcherConcurrentFileChangesAndDoCycle creates, modifies, and
/// deletes files from multiple goroutines while DoCycle runs, testing
/// races between FS mutations and watch state updates.
#[test]
fn watcher_concurrent_file_changes_and_do_cycle() {
    run_test_in_child(
        "tsctests::watcher_race::watcher_concurrent_file_changes_and_do_cycle",
        || {
            let (mut w, sys) = create_test_watcher();
            let map_fs = sys.map_fs();

            thread::scope(|s| {
                // File creators
                for i in 0..4 {
                    let map_fs = map_fs.clone();
                    s.spawn(move || {
                        let fs = map_fs.fs();
                        for j in 0..20 {
                            let path = format!("/home/src/workspaces/project/gen_{i}_{j}.ts");
                            let _ = fs.write_file(&path, &format!("export const x{i}_{j} = {j};"));
                        }
                    });
                }

                // File deleters
                {
                    let map_fs = map_fs.clone();
                    s.spawn(move || {
                        let fs = map_fs.fs();
                        for j in 0..20 {
                            let _ =
                                fs.remove(&format!("/home/src/workspaces/project/gen_0_{j}.ts"));
                        }
                    });
                }

                // DoCycle callers
                do_cycles(w.as_mut(), 4 * 10);
            });
        },
    );
}

// Go: watcher_race_test.go:152 TestWatcherRapidConfigChanges
/// TestWatcherRapidConfigChanges modifies tsconfig.json rapidly from
/// multiple goroutines while DoCycle runs, testing races on
/// config-related fields (configModified, configHasErrors,
/// configFilePaths, config, extendedConfigCache).
#[test]
fn watcher_rapid_config_changes() {
    run_test_in_child(
        "tsctests::watcher_race::watcher_rapid_config_changes",
        || {
            let (mut w, sys) = create_test_watcher();
            let map_fs = sys.map_fs();

            const CONFIGS: [&str; 4] = [
                "{}",
                r#"{"compilerOptions": {"strict": true}}"#,
                r#"{"compilerOptions": {"target": "ES2020"}}"#,
                r#"{"compilerOptions": {"noEmit": true}}"#,
            ];

            thread::scope(|s| {
                // Config modifiers + DoCycle
                for i in 0..3 {
                    let map_fs = map_fs.clone();
                    s.spawn(move || {
                        let fs = map_fs.fs();
                        for j in 0..10 {
                            let _ = fs.write_file(
                                "/home/src/workspaces/project/tsconfig.json",
                                CONFIGS[(i + j) % CONFIGS.len()],
                            );
                        }
                    });
                }

                // Concurrent source file modifications
                for i in 0..2 {
                    let map_fs = map_fs.clone();
                    s.spawn(move || {
                        let fs = map_fs.fs();
                        for j in 0..15 {
                            let _ = fs.write_file(
                                "/home/src/workspaces/project/a.ts",
                                &format!("const a: number = {};", i * 15 + j),
                            );
                        }
                    });
                }

                // The DoCycle calls of the config and source goroutines above, then
                // of the 4 state reader goroutines (30 rounds of 2 calls each).
                do_cycles(w.as_mut(), 3 * 10 + 2 * 15 + 4 * 30 * 2);
            });
        },
    );
}

// Go: watcher_race_test.go:211 TestWatcherConcurrentDoCycleNoChanges
/// TestWatcherConcurrentDoCycleNoChanges calls DoCycle from many
/// goroutines when no files have changed, testing the early-return
/// path where WatchState is read and HasChanges is called.
#[test]
fn watcher_concurrent_do_cycle_no_changes() {
    run_test_in_child(
        "tsctests::watcher_race::watcher_concurrent_do_cycle_no_changes",
        || {
            let (mut w, _sys) = create_test_watcher();

            // The DoCycle calls of the 16 goroutines.
            do_cycles(w.as_mut(), 16 * 50);
        },
    );
}

// Go: watcher_race_test.go:231 TestWatcherAlternatingModifyAndDoCycle
/// TestWatcherAlternatingModifyAndDoCycle alternates between modifying
/// a file and calling DoCycle from different goroutines, creating a
/// realistic scenario where the file watcher detects changes mid-cycle.
#[test]
fn watcher_alternating_modify_and_do_cycle() {
    run_test_in_child(
        "tsctests::watcher_race::watcher_alternating_modify_and_do_cycle",
        || {
            let (mut w, sys) = create_test_watcher();
            let map_fs = sys.map_fs();

            thread::scope(|s| {
                // Writer goroutine: continuously modifies files
                {
                    let map_fs = map_fs.clone();
                    s.spawn(move || {
                        let fs = map_fs.fs();
                        for j in 0..100 {
                            let _ = fs.write_file(
                                "/home/src/workspaces/project/a.ts",
                                &format!("const a: number = {j};"),
                            );
                        }
                    });
                }

                // The DoCycle calls of the 4 DoCycle goroutines, then of the 4 state
                // reader goroutines.
                do_cycles(w.as_mut(), 4 * 25 + 4 * 100);
            });
        },
    );
}

// Go: watcher_race_test.go:268 TestBuildWatchStopsWhenContextIsCancelled
///
/// PORT: Go builds `sys` on the test goroutine and runs CommandLine on
/// another goroutine. `TestSys` is not `Send`, so the thread builds the same
/// `TestSys` from the input. The result's watcher is not `Send` either, so
/// the thread sends the status and whether the watcher is set. A panic in
/// that thread ends the channel; Go would crash the test binary instead.
#[test]
fn build_watch_stops_when_context_is_cancelled() {
    run_test_in_child(
        "tsctests::watcher_race::build_watch_stops_when_context_is_cancelled",
        || {
            let input = TscInput {
                files: file_map([
                    (
                        "/home/src/workspaces/project/tsconfig.json",
                        r#"{"compilerOptions":{"composite":true},"files":["index.ts"]}"#.into(),
                    ),
                    (
                        "/home/src/workspaces/project/index.ts",
                        "export const x = 1;".into(),
                    ),
                ]),
                ..Default::default()
            };
            let (ctx, cancel) = context::with_cancel(&context::background());
            cancel();

            let (result_tx, result_rx) = mpsc::sync_channel::<(ExitStatus, bool)>(1);
            const ARGS: [&str; 4] = ["--build", "--watch", "--watchInterval", "60000"];
            thread::Builder::new()
                .stack_size(STACK_SIZE)
                .spawn(move || {
                    let sys = new_in_process_test_sys(&input, &ARGS);
                    let result = command_line(&ctx, &sys, &ARGS);
                    let _ = result_tx.send((result.status, result.watcher.is_some()));
                })
                .expect("spawn the build thread");

            match result_rx.recv_timeout(Duration::from_secs(2)) {
                Ok((status, has_watcher)) => {
                    assert_eq!(status, ExitStatus::Success);
                    assert!(has_watcher);
                }
                Err(RecvTimeoutError::Timeout) => {
                    panic!("build watch did not stop after context cancellation")
                }
                Err(RecvTimeoutError::Disconnected) => {
                    panic!("build watch panicked before it returned a result")
                }
            }
        },
    );
}
