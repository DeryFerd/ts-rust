//! Port of internal/execute/tsctests/contentmapper_watch_test.go (tsgo#4712):
//! the content mapper process lifecycle of `tsc -b`, `tsc -w` and
//! `tsc -b -w`, and the watch rebuilds that mapper files cause.
//!
//! PORT: the compiler runs in this process with the OS override for the
//! test system, which is for the whole process. So each test runs in a
//! child process of its own (`run_test_in_child`), as in watcher_race.rs.
//! Go's `t.Run` subtests of `TestContentMapperWatchLifecycle` are two
//! tests here for the same reason.
//!
//! PORT: Go `<-closed` blocks until the test times out. Here the wait has a
//! deadline (`CLOSED_WAIT`) so that a missing close fails the test.

use std::rc::Rc;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::mpsc::{self, Receiver, SyncSender};
use std::sync::{Arc, Once};
use std::time::{Duration, SystemTime};

use ts_goport::contentmapper::{self, ProcessExitState};
use ts_goport::execute;
use ts_goport::execute::execute_tsc::command_line;
use ts_goport::execute::tsc::compile::{ErrorWriter, System, Writer};
use ts_goport::execute::tsc::{CommandLineResult, ExitStatus, Watcher};
use ts_goport::execute::watcher::set_test_watch_backend;
use ts_goport::frontend::vfs::Fs;
use ts_goport::fswatch::{Event, EventKind};
use ts_goport::gostd::{Context, GoError, context};
use ts_goport::ipc;

use crate::support::child::{ChildHooks, new_in_process_test_sys, run_test_in_child};
use crate::support::contentmappertest::{self, ProjectLifecycle};
use crate::support::runner::{FileMap, TscInput};
use crate::support::test_sys::TestSys;
use crate::support::vfstest::MapFile;

/// How long a test waits for a mapper process close that Go waits for
/// with `<-closed`.
const CLOSED_WAIT: Duration = Duration::from_secs(30);

/// Go `FileMap{...}` literal.
fn file_map<const N: usize>(entries: [(&str, MapFile); N]) -> FileMap {
    entries
        .into_iter()
        .map(|(path, file)| (path.to_string(), file))
        .collect()
}

// Go: contentmapper_watch_test.go:20 recordingContentMapperSystem
// PORT: Go embeds `*TestSys`; every method but `Spawn` calls the test
// system.
struct RecordingContentMapperSystem {
    test_sys: Rc<TestSys>,
    spawner: Rc<RecordingContentMapperSpawner>,
}

impl System for RecordingContentMapperSystem {
    fn writer(&self) -> Writer {
        System::writer(&*self.test_sys)
    }
    fn error_writer(&self) -> ErrorWriter {
        System::error_writer(&*self.test_sys)
    }
    fn fs(&self) -> Rc<dyn Fs> {
        System::fs(&*self.test_sys)
    }
    fn default_library_path(&self) -> String {
        System::default_library_path(&*self.test_sys)
    }
    fn get_current_directory(&self) -> String {
        System::get_current_directory(&*self.test_sys)
    }
    fn write_output_is_tty(&self) -> bool {
        System::write_output_is_tty(&*self.test_sys)
    }
    fn get_width_of_terminal(&self) -> i32 {
        System::get_width_of_terminal(&*self.test_sys)
    }
    fn get_environment_variable(&self, name: &str) -> String {
        System::get_environment_variable(&*self.test_sys, name)
    }
    // Go: contentmapper_watch_test.go:25 recordingContentMapperSystem.Spawn
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn std::io::Write + Send>>,
    ) -> Result<Arc<dyn ProcessExitState>, GoError> {
        contentmapper::Spawner::spawn(&*self.spawner, command, dir, stderr)
    }
    fn now(&self) -> SystemTime {
        System::now(&*self.test_sys)
    }
    fn since_start(&self) -> Duration {
        System::since_start(&*self.test_sys)
    }
}

// Go: contentmapper_watch_test.go:29 recordingContentMapperSpawner
// PORT: Go `closed chan<- struct{}` (nil when no test waits) is an
// `Option` of the sender of a bounded channel.
struct RecordingContentMapperSpawner {
    inner: Rc<dyn contentmapper::Spawner>,
    spawns: AtomicI32,
    closes: Arc<AtomicI32>,
    closed: Option<SyncSender<()>>,
}

impl RecordingContentMapperSpawner {
    fn new(inner: Rc<dyn contentmapper::Spawner>, closed: Option<SyncSender<()>>) -> Self {
        RecordingContentMapperSpawner {
            inner,
            spawns: AtomicI32::new(0),
            closes: Arc::new(AtomicI32::new(0)),
            closed,
        }
    }

    fn spawns(&self) -> i32 {
        self.spawns.load(Ordering::SeqCst)
    }

    fn closes(&self) -> i32 {
        self.closes.load(Ordering::SeqCst)
    }
}

impl contentmapper::Spawner for RecordingContentMapperSpawner {
    // Go: contentmapper_watch_test.go:36 recordingContentMapperSpawner.Spawn
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn std::io::Write + Send>>,
    ) -> Result<Arc<dyn ProcessExitState>, GoError> {
        let process = contentmapper::Spawner::spawn(&*self.inner, command, dir, stderr)?;
        self.spawns.fetch_add(1, Ordering::SeqCst);
        Ok(Arc::new(RecordingContentMapperProcess {
            inner: process,
            closes: self.closes.clone(),
            closed: self.closed.clone(),
            once: Once::new(),
        }))
    }
}

// Go: contentmapper_watch_test.go:45 recordingContentMapperProcess
// PORT: Go embeds the `io.ReadWriteCloser`, which has no `ExitCode`
// method, so the host sees no exit state: the default `exit_code`.
struct RecordingContentMapperProcess {
    inner: Arc<dyn ProcessExitState>,
    closes: Arc<AtomicI32>,
    closed: Option<SyncSender<()>>,
    once: Once,
}

impl ipc::ReadWriteCloser for RecordingContentMapperProcess {
    fn read(&self, buf: &mut [u8]) -> std::io::Result<usize> {
        ipc::ReadWriteCloser::read(&*self.inner, buf)
    }

    fn write(&self, buf: &[u8]) -> std::io::Result<usize> {
        ipc::ReadWriteCloser::write(&*self.inner, buf)
    }

    fn flush(&self) -> std::io::Result<()> {
        ipc::ReadWriteCloser::flush(&*self.inner)
    }

    // Go: contentmapper_watch_test.go:52 recordingContentMapperProcess.Close
    fn close(&self) -> Result<(), GoError> {
        let mut result = Ok(());
        self.once.call_once(|| {
            self.closes.fetch_add(1, Ordering::SeqCst);
            result = ipc::ReadWriteCloser::close(&*self.inner);
            if let Some(closed) = &self.closed {
                let _ = closed.send(());
            }
        });
        result
    }
}

impl ProcessExitState for RecordingContentMapperProcess {}

/// Go `newTestSys(input, false)` and the recording system around it.
fn new_recording_system(
    input: &TscInput,
    inner: Rc<dyn contentmapper::Spawner>,
    closed: Option<SyncSender<()>>,
) -> (Rc<TestSys>, Rc<RecordingContentMapperSystem>) {
    let test_sys = new_in_process_test_sys(input);
    let sys = Rc::new(RecordingContentMapperSystem {
        test_sys: test_sys.clone(),
        spawner: Rc::new(RecordingContentMapperSpawner::new(inner, closed)),
    });
    (test_sys, sys)
}

/// Go `execute.CommandLine(ctx, sys, args, testSys)`.
fn command_line_with(
    ctx: &Context,
    sys: &Rc<RecordingContentMapperSystem>,
    args: &[&str],
) -> CommandLineResult {
    set_test_watch_backend(sys.test_sys.mock_watch_backend().clone());
    let args: Vec<String> = args.iter().map(|arg| (*arg).to_string()).collect();
    let hooks = ChildHooks {
        testing: sys.test_sys.clone(),
    };
    command_line(ctx, sys.clone() as Rc<dyn System>, &args, &hooks)
}

/// Go `testSys.mockWatchBackend.SendEvents([]fswatch.Event{{Kind: fswatch.EventUpdate, Path: path}, ...})`.
fn send_updates(test_sys: &TestSys, paths: &[&str]) {
    test_sys.mock_watch_backend().send_events(
        paths
            .iter()
            .map(|path| Event {
                kind: EventKind::Update,
                path: (*path).to_string(),
            })
            .collect(),
    );
}

/// Go `result.Watcher.(*execute.Watcher)`.
fn as_execute_watcher(w: &dyn Watcher) -> &execute::watcher::Watcher {
    w.as_any()
        .downcast_ref::<execute::watcher::Watcher>()
        .expect("the watcher is an *execute.Watcher")
}

/// Go `<-closed`, with a deadline (see the module comment).
fn wait_closed(closed: &Receiver<()>) {
    closed
        .recv_timeout(CLOSED_WAIT)
        .expect("a content mapper process close");
}

// Go: contentmapper_watch_test.go:64 TestContentMapperBuildLifecycle
#[test]
fn content_mapper_build_lifecycle() {
    run_test_in_child(
        "tsctests::contentmapper_watch::content_mapper_build_lifecycle",
        || {
            let input = TscInput {
                files: file_map([
                    (
                        "/home/src/workspaces/project/tsconfig.json",
                        r#"{
			"compilerOptions": { "composite": true },
			"contentMappers": [{ "package": "mapper", "extensions": [".vue"] }]
		}"#
                        .into(),
                    ),
                    (
                        "/home/src/workspaces/project/app.vue",
                        "export const app = 1;".into(),
                    ),
                    (
                        "/home/src/workspaces/project/node_modules/mapper/package.json",
                        contentmappertest::package_json(contentmappertest::VERBATIM_MAPPER).into(),
                    ),
                ]),
                ..Default::default()
            };
            let (_test_sys, sys) =
                new_recording_system(&input, contentmappertest::new_spawner(), None);

            let result = command_line_with(
                &context::background(),
                &sys,
                &["--build", "--runExternalCode"],
            );
            assert!(result.watcher.is_none());
            assert_eq!(sys.spawner.spawns(), 1);
            assert_eq!(sys.spawner.closes(), 1);
        },
    );
}

// Go: contentmapper_watch_test.go:84 TestContentMapperBuildIdentityFailureExitStatus
#[test]
fn content_mapper_build_identity_failure_exit_status() {
    run_test_in_child(
        "tsctests::contentmapper_watch::content_mapper_build_identity_failure_exit_status",
        || {
            const PACKAGE_JSON_PATH: &str =
                "/home/src/workspaces/project/node_modules/mapper/package.json";
            let input = TscInput {
                files: file_map([
                    (
                        "/home/src/workspaces/project/tsconfig.json",
                        r#"{
			"compilerOptions": { "composite": true },
			"contentMappers": [{ "package": "mapper", "extensions": [".vue"] }]
		}"#
                        .into(),
                    ),
                    (
                        "/home/src/workspaces/project/app.vue",
                        "export const app = 1;".into(),
                    ),
                    (
                        PACKAGE_JSON_PATH,
                        contentmappertest::package_json(contentmappertest::DYNAMIC_VERBATIM_MAPPER)
                            .into(),
                    ),
                ]),
                ..Default::default()
            };
            let (test_sys, sys) =
                new_recording_system(&input, contentmappertest::new_spawner(), None);
            let args = ["--build", "--runExternalCode"];
            let result = command_line_with(&context::background(), &sys, &args);
            assert_eq!(result.status, ExitStatus::Success);

            test_sys.write_file_no_error(
                PACKAGE_JSON_PATH,
                r#"{
		"name": "mapper",
		"version": "1.0.0",
		"typescript": { "contentMapper": { "exec": ["missing-mapper"], "dynamicConfig": true } }
	}"#,
            );
            let result = command_line_with(&context::background(), &sys, &args);
            assert_eq!(result.status, ExitStatus::DiagnosticsPresentOutputsSkipped);
        },
    );
}

// Go: contentmapper_watch_test.go:113 TestContentMapperWatchLifecycle
fn content_mapper_watch_lifecycle(args: &[&str]) {
    const CONFIG_FILE_NAME: &str = "/home/src/workspaces/project/tsconfig.json";
    let input = TscInput {
        files: file_map([
            (
                CONFIG_FILE_NAME,
                r#"{
					"compilerOptions": { "composite": true },
					"contentMappers": [{ "package": "mapper-a", "extensions": [".vue"] }]
				}"#
                .into(),
            ),
            (
                "/home/src/workspaces/project/app.vue",
                "export const app = 1;".into(),
            ),
            (
                "/home/src/workspaces/project/node_modules/mapper-a/package.json",
                contentmappertest::package_json(contentmappertest::VERBATIM_MAPPER).into(),
            ),
            (
                "/home/src/workspaces/project/node_modules/mapper-b/package.json",
                contentmappertest::package_json(contentmappertest::VERBATIM_MAPPER)
                    .replacen(r#""version": "1.0.0""#, r#""version": "2.0.0""#, 1)
                    .into(),
            ),
        ]),
        ..Default::default()
    };
    let (closed_tx, closed) = mpsc::sync_channel::<()>(3);
    let (test_sys, sys) =
        new_recording_system(&input, contentmappertest::new_spawner(), Some(closed_tx));
    let (ctx, cancel) = context::with_cancel(&context::background());

    let result = command_line_with(&ctx, &sys, args);
    let mut w = result.watcher.expect("result.Watcher != nil");
    assert_eq!(sys.spawner.spawns(), 1);
    assert_eq!(sys.spawner.closes(), 0);

    test_sys.write_file_no_error(
        CONFIG_FILE_NAME,
        r#"{
				"compilerOptions": { "composite": true },
				"contentMappers": [{ "package": "mapper-b", "extensions": [".vue"] }]
			}"#,
    );
    send_updates(&test_sys, &[CONFIG_FILE_NAME]);
    w.do_cycle();

    assert_eq!(sys.spawner.spawns(), 2);
    assert_eq!(sys.spawner.closes(), 1);
    wait_closed(&closed);

    test_sys.write_file_no_error(
        CONFIG_FILE_NAME,
        r#"{ "compilerOptions": { "composite": true } }"#,
    );
    send_updates(&test_sys, &[CONFIG_FILE_NAME]);
    w.do_cycle();

    assert_eq!(sys.spawner.closes(), 2);
    wait_closed(&closed);

    test_sys.write_file_no_error(
        CONFIG_FILE_NAME,
        r#"{
				"compilerOptions": { "composite": true },
				"contentMappers": [{ "package": "mapper-a", "extensions": [".vue"] }]
			}"#,
    );
    send_updates(&test_sys, &[CONFIG_FILE_NAME]);
    w.do_cycle();

    assert_eq!(sys.spawner.spawns(), 3);
    assert_eq!(sys.spawner.closes(), 2);
    cancel();
    let closed_after_cancellation = closed.recv_timeout(Duration::from_secs(1)).is_ok();
    assert!(
        closed_after_cancellation,
        "content mapper process was not closed after cancellation"
    );
    assert_eq!(sys.spawner.closes(), 3);
}

// Go: contentmapper_watch_test.go:113 TestContentMapperWatchLifecycle, subtest "watch"
#[test]
fn content_mapper_watch_lifecycle_watch() {
    run_test_in_child(
        "tsctests::contentmapper_watch::content_mapper_watch_lifecycle_watch",
        || content_mapper_watch_lifecycle(&["--watch", "--runExternalCode"]),
    );
}

// Go: contentmapper_watch_test.go:113 TestContentMapperWatchLifecycle, subtest "build watch"
#[test]
fn content_mapper_watch_lifecycle_build_watch() {
    run_test_in_child(
        "tsctests::contentmapper_watch::content_mapper_watch_lifecycle_build_watch",
        || content_mapper_watch_lifecycle(&["--build", "--watch", "--runExternalCode"]),
    );
}

// Go: contentmapper_watch_test.go:187 TestContentMapperSupplementalCollisionWatch
#[test]
fn content_mapper_supplemental_collision_watch() {
    run_test_in_child(
        "tsctests::contentmapper_watch::content_mapper_supplemental_collision_watch",
        || {
            const SUPPLEMENTAL_FILE_NAME: &str = "/home/src/workspaces/project/app.vue.0.ts";
            let input = TscInput {
                files: file_map([
                    (
                        "/home/src/workspaces/project/tsconfig.json",
                        r#"{
			"compilerOptions": { "noLib": true },
			"contentMappers": [{ "package": "mapper", "extensions": [".vue"] }]
		}"#
                        .into(),
                    ),
                    (
                        "/home/src/workspaces/project/app.vue",
                        "declare const value: number;".into(),
                    ),
                    (
                        "/home/src/workspaces/project/node_modules/mapper/package.json",
                        contentmappertest::package_json(contentmappertest::SUPPLEMENTAL_MAPPER)
                            .into(),
                    ),
                ]),
                ..Default::default()
            };
            let (test_sys, sys) =
                new_recording_system(&input, contentmappertest::new_spawner(), None);
            let (ctx, cancel) = context::with_cancel(&context::background());

            let result = command_line_with(&ctx, &sys, &["--watch", "--runExternalCode"]);
            let mut w = result
                .watcher
                .expect("expected Watcher to be non-nil in watch mode");
            let full_builds = as_execute_watcher(w.as_ref()).full_builds();

            test_sys.write_file_no_error(SUPPLEMENTAL_FILE_NAME, "export {};\n");
            send_updates(&test_sys, &[SUPPLEMENTAL_FILE_NAME]);
            w.do_cycle();
            assert_eq!(
                as_execute_watcher(w.as_ref()).full_builds(),
                full_builds + 1,
                "creating a supplemental filename collision must force a full rebuild"
            );

            assert!(
                test_sys
                    .fs_from_file_map()
                    .remove(SUPPLEMENTAL_FILE_NAME)
                    .is_ok(),
                "Remove({SUPPLEMENTAL_FILE_NAME})"
            );
            send_updates(&test_sys, &[SUPPLEMENTAL_FILE_NAME]);
            w.do_cycle();
            assert_eq!(
                as_execute_watcher(w.as_ref()).full_builds(),
                full_builds + 2,
                "removing a supplemental filename collision must force a full rebuild"
            );
            cancel();
        },
    );
}

// Go: contentmapper_watch_test.go:219 TestDynamicContentMapperWatchDependency
#[test]
fn dynamic_content_mapper_watch_dependency() {
    run_test_in_child(
        "tsctests::contentmapper_watch::dynamic_content_mapper_watch_dependency",
        || {
            const MAPPER_CONFIG_FILE_NAME: &str = "/home/src/workspaces/project/mapper.config.json";
            let input = TscInput {
                files: file_map([
                    (
                        "/home/src/workspaces/project/tsconfig.json",
                        r#"{
			"compilerOptions": { "composite": true },
			"contentMappers": [{ "package": "mapper", "extensions": [".vue"] }]
		}"#
                        .into(),
                    ),
                    (MAPPER_CONFIG_FILE_NAME, r#"{ "version": 1 }"#.into()),
                    (
                        "/home/src/workspaces/project/app.vue",
                        "export const app = 1;".into(),
                    ),
                    (
                        "/home/src/workspaces/project/node_modules/mapper/package.json",
                        contentmappertest::package_json(contentmappertest::DYNAMIC_VERBATIM_MAPPER)
                            .into(),
                    ),
                ]),
                ..Default::default()
            };
            let lifecycle = Arc::new(ProjectLifecycle::default());
            let (test_sys, sys) = new_recording_system(
                &input,
                contentmappertest::new_spawner_with_project_lifecycle(lifecycle.clone()),
                None,
            );
            let (ctx, cancel) = context::with_cancel(&context::background());

            let result = command_line_with(&ctx, &sys, &["--watch", "--runExternalCode"]);
            let mut w = result
                .watcher
                .expect("expected Watcher to be non-nil in watch mode");
            let full_builds = as_execute_watcher(w.as_ref()).full_builds();

            test_sys.write_file_no_error(MAPPER_CONFIG_FILE_NAME, r#"{ "version": 2 }"#);
            send_updates(&test_sys, &[MAPPER_CONFIG_FILE_NAME]);
            w.do_cycle();

            assert_eq!(
                as_execute_watcher(w.as_ref()).full_builds(),
                full_builds + 1
            );
            assert_eq!(lifecycle.opens.load(Ordering::SeqCst), 2);
            assert_eq!(lifecycle.closes.load(Ordering::SeqCst), 1);
            assert_eq!(sys.spawner.spawns(), 1);
            assert_eq!(sys.spawner.closes(), 0);
            cancel();
        },
    );
}

// Go: contentmapper_watch_test.go:253 TestContentMapperMixedWatchBatchForcesFullRebuild
#[test]
fn content_mapper_mixed_watch_batch_forces_full_rebuild() {
    run_test_in_child(
        "tsctests::contentmapper_watch::content_mapper_mixed_watch_batch_forces_full_rebuild",
        || {
            const MAPPED_FILE_NAME: &str = "/home/src/workspaces/project/app.vue";
            const MAIN_FILE_NAME: &str = "/home/src/workspaces/project/main.ts";
            let input = TscInput {
                files: file_map([
                    (
                        "/home/src/workspaces/project/tsconfig.json",
                        r#"{
			"compilerOptions": { "noLib": true },
			"contentMappers": [{ "package": "mapper", "extensions": [".vue"] }]
		}"#
                        .into(),
                    ),
                    (MAPPED_FILE_NAME, "export const marker = 1 as const;".into()),
                    (
                        MAIN_FILE_NAME,
                        r#"import { marker } from "./app.vue"; const check: 1 = marker;"#.into(),
                    ),
                    (
                        "/home/src/workspaces/project/node_modules/mapper/package.json",
                        contentmappertest::package_json(contentmappertest::VERBATIM_MAPPER).into(),
                    ),
                ]),
                ..Default::default()
            };
            let (test_sys, sys) =
                new_recording_system(&input, contentmappertest::new_spawner(), None);
            // Go: testSys.currentWrite.Reset()
            test_sys.set_output_bytes(Vec::new());
            let (ctx, cancel) = context::with_cancel(&context::background());

            let result = command_line_with(
                &ctx,
                &sys,
                &["--watch", "--pretty", "false", "--runExternalCode"],
            );
            let mut w = result
                .watcher
                .expect("expected Watcher to be non-nil in watch mode");
            let (fast_builds, full_builds) = {
                let w = as_execute_watcher(w.as_ref());
                (w.fast_path_builds(), w.full_builds())
            };
            test_sys.set_output_bytes(Vec::new());
            test_sys.write_file_no_error(MAPPED_FILE_NAME, "export const marker = 2 as const;");
            test_sys.write_file_no_error(
                MAIN_FILE_NAME,
                r#"import { marker } from "./app.vue"; const check: 2 = marker;"#,
            );
            send_updates(&test_sys, &[MAPPED_FILE_NAME, MAIN_FILE_NAME]);
            w.do_cycle();

            assert_eq!(
                as_execute_watcher(w.as_ref()).full_builds(),
                full_builds + 1
            );
            assert_eq!(
                as_execute_watcher(w.as_ref()).fast_path_builds(),
                fast_builds
            );
            let output = test_sys.output_text();
            assert!(
                !output.contains("Type '1' is not assignable to type '2'"),
                "{output}"
            );
            cancel();
        },
    );
}

// Go: contentmapper_watch_test.go:294 TestDynamicContentMapperBuildWatchDependency
#[test]
fn dynamic_content_mapper_build_watch_dependency() {
    run_test_in_child(
        "tsctests::contentmapper_watch::dynamic_content_mapper_build_watch_dependency",
        || {
            const MAPPER_CONFIG_FILE_NAME: &str = "/home/src/workspaces/project/mapper.config.json";
            let input = TscInput {
                files: file_map([
                    (
                        "/home/src/workspaces/project/tsconfig.json",
                        r#"{
			"compilerOptions": { "composite": true },
			"contentMappers": [{ "package": "mapper", "extensions": [".vue"] }]
		}"#
                        .into(),
                    ),
                    (MAPPER_CONFIG_FILE_NAME, r#"{ "version": 1 }"#.into()),
                    (
                        "/home/src/workspaces/project/app.vue",
                        "export const app = 1;".into(),
                    ),
                    (
                        "/home/src/workspaces/project/node_modules/mapper/package.json",
                        contentmappertest::package_json(contentmappertest::DYNAMIC_VERBATIM_MAPPER)
                            .into(),
                    ),
                ]),
                ..Default::default()
            };
            let lifecycle = Arc::new(ProjectLifecycle::default());
            let (test_sys, sys) = new_recording_system(
                &input,
                contentmappertest::new_spawner_with_project_lifecycle(lifecycle.clone()),
                None,
            );
            let (ctx, cancel) = context::with_cancel(&context::background());

            let result =
                command_line_with(&ctx, &sys, &["--build", "--watch", "--runExternalCode"]);
            let mut w = result.watcher.expect("expected a build watcher");
            assert_eq!(lifecycle.opens.load(Ordering::SeqCst), 1);

            test_sys.write_file_no_error(MAPPER_CONFIG_FILE_NAME, r#"{ "version": 2 }"#);
            send_updates(&test_sys, &[MAPPER_CONFIG_FILE_NAME]);
            w.do_cycle();

            assert_eq!(lifecycle.opens.load(Ordering::SeqCst), 2);
            assert_eq!(lifecycle.closes.load(Ordering::SeqCst), 1);
            assert_eq!(sys.spawner.spawns(), 1);
            assert_eq!(sys.spawner.closes(), 0);
            cancel();
        },
    );
}

// Go: contentmapper_watch_test.go:326 TestContentMapperBuildWatchSharedLifecycle
#[test]
fn content_mapper_build_watch_shared_lifecycle() {
    run_test_in_child(
        "tsctests::contentmapper_watch::content_mapper_build_watch_shared_lifecycle",
        || {
            const MAPPER_CONFIG: &str = r#"{
		"compilerOptions": { "composite": true },
		"contentMappers": [{ "package": "mapper", "extensions": [".vue"] }]
	}"#;
            let input = TscInput {
                files: file_map([
                    (
                        "/home/src/workspaces/project/tsconfig.json",
                        r#"{
			"files": [],
			"references": [{ "path": "a" }, { "path": "b" }]
		}"#
                        .into(),
                    ),
                    (
                        "/home/src/workspaces/project/a/tsconfig.json",
                        MAPPER_CONFIG.into(),
                    ),
                    (
                        "/home/src/workspaces/project/a/app.vue",
                        "export const a = 1;".into(),
                    ),
                    (
                        "/home/src/workspaces/project/b/tsconfig.json",
                        MAPPER_CONFIG.into(),
                    ),
                    (
                        "/home/src/workspaces/project/b/app.vue",
                        "export const b = 1;".into(),
                    ),
                    (
                        "/home/src/workspaces/project/node_modules/mapper/package.json",
                        contentmappertest::package_json(contentmappertest::VERBATIM_MAPPER).into(),
                    ),
                ]),
                ..Default::default()
            };
            let (test_sys, sys) =
                new_recording_system(&input, contentmappertest::new_spawner(), None);
            let (ctx, cancel) = context::with_cancel(&context::background());

            let result =
                command_line_with(&ctx, &sys, &["--build", "--watch", "--runExternalCode"]);
            let mut w = result.watcher.expect("result.Watcher != nil");
            assert_eq!(sys.spawner.spawns(), 1);
            assert_eq!(sys.spawner.closes(), 0);

            for project in ["a", "b"] {
                let config_file_name =
                    format!("/home/src/workspaces/project/{project}/tsconfig.json");
                test_sys.write_file_no_error(
                    &config_file_name,
                    r#"{ "compilerOptions": { "composite": true } }"#,
                );
                send_updates(&test_sys, &[config_file_name.as_str()]);
                w.do_cycle();
                if project == "a" {
                    assert_eq!(sys.spawner.closes(), 0);
                } else {
                    assert_eq!(sys.spawner.closes(), 1);
                }
            }
            cancel();
        },
    );
}
