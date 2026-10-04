//! Resolve ahead (src/frontend/compiler/resolve_ahead.rs). Not a Go test:
//! the port's language server loads resolve the keys of the previous load
//! on worker threads. A load whose loader takes every worker answer that
//! passes the check (`Mode::Force`) must give the same program, module
//! resolutions, seen files, missing directories and cached files as a load
//! whose loader resolves every key itself (`Mode::Off`).
//!
//! Resolve ahead runs only on the OS file system, so each test writes a
//! project to a temp directory and runs with no OS override (not
//! `child_test!`, which installs one).

use std::collections::BTreeSet;
use std::rc::Rc;

use ts_goport::frontend::bundled;
use ts_goport::frontend::compiler::resolve_ahead::{self, LoadStats, Mode};
use ts_goport::frontend::tspath;
use ts_goport::frontend::vfs::osvfs_fs;
use ts_goport::lsp::lsproto;
use ts_goport::project::{self, Session, SessionInit, SessionOptions};

use super::projecttestutil;
use super::util::{CHANGED, bg, close, edit, generate_file_events, open, program, uri};

/// A test in a child process with no OS override, with the environment
/// variables `$env` set.
macro_rules! os_child_test {
    ($(#[$meta:meta])* fn $name:ident() $body:block) => {
        os_child_test!(env &[]; $(#[$meta])* fn $name() $body);
    };
    (env $env:expr; $(#[$meta:meta])* fn $name:ident() $body:block) => {
        $(#[$meta])*
        #[test]
        fn $name() {
            let path = concat!(module_path!(), "::", stringify!($name));
            let test = path.split_once("::").map_or(path, |(_, rest)| rest);
            crate::support::child::run_test_in_child_with_env(test, $env, || $body);
        }
    };
}

const INDEX: &str = r#"import { a } from "./a";
import { b } from "./sub/b";
import { c } from "../lib/c";
import { p } from "pkg";
import { o } from "pkg/other";
import { m } from "@scope/lib";
import { x } from "./missing/x";
import { y } from "not-installed";
export const all = [a, b, c, p, o, m, x, y];
"#;

/// The project of every test: relative imports, a file outside `include`,
/// packages with `types` and `exports`, a missing directory and a missing
/// package.
const FILES: &[(&str, &str)] = &[
    (
        "tsconfig.json",
        r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler", "noLib": true, "strict": true }, "include": ["src"] }"#,
    ),
    ("src/index.ts", INDEX),
    ("src/a.ts", "export const a = 1;"),
    ("src/sub/b.ts", "export const b = 2;"),
    ("src/sub/d.ts", "export const d = 6;"),
    ("lib/c.ts", "export const c = 3;"),
    (
        "node_modules/pkg/package.json",
        r#"{ "name": "pkg", "version": "1.0.0", "types": "index.d.ts" }"#,
    ),
    (
        "node_modules/pkg/index.d.ts",
        "export declare const p: number;",
    ),
    (
        "node_modules/pkg/other.d.ts",
        "export declare const o: number;",
    ),
    (
        "node_modules/@scope/lib/package.json",
        r#"{ "name": "@scope/lib", "version": "2.0.0", "exports": { ".": { "types": "./dist/main.d.ts" } } }"#,
    ),
    (
        "node_modules/@scope/lib/dist/main.d.ts",
        "export declare const m: number;",
    ),
];

/// A new temp directory with `FILES`, its real path.
fn make_project(label: &str) -> String {
    let root = std::env::temp_dir().join(format!(
        "ts_goport_resolve_ahead_{}_{label}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    for (name, text) in FILES {
        write(&root.to_string_lossy(), name, text);
    }
    std::fs::canonicalize(&root)
        .unwrap()
        .to_string_lossy()
        .replace('\\', "/")
}

fn write(root: &str, name: &str, text: &str) {
    let path = std::path::Path::new(root).join(name);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

fn file_uri(root: &str, name: &str) -> String {
    format!("file://{root}/{name}")
}

/// A session on the OS file system in `root`, with no client, watch or
/// typings installer.
fn os_session(root: &str) -> Rc<Session> {
    project::new_session(&SessionInit {
        background_ctx: bg(),
        options: Rc::new(SessionOptions {
            current_directory: root.to_string(),
            default_library_path: bundled::lib_path(),
            typings_location: String::new(),
            position_encoding: lsproto::PositionEncodingKind::UTF8,
            watch_enabled: false,
            logging_enabled: false,
            ..projecttestutil::session_options(root)
        }),
        fs: bundled::wrap_fs(osvfs_fs()),
        client: None,
        logger: None,
        npm_executor: None,
        spawner: None,
        content_mapper_logger: None,
        parse_cache: None,
        content_mapped_parse_cache: None,
    })
}

/// What a program load leaves: the program's files and module resolutions,
/// the files that its host saw, the directories that it found missing and
/// the snapshot's cached files. Paths are relative to the project root.
#[derive(Debug, PartialEq, Eq)]
struct Observed {
    files: Vec<String>,
    missing_files: Vec<String>,
    resolutions: BTreeSet<String>,
    seen: BTreeSet<String>,
    missing_directories: BTreeSet<String>,
    cached_files: BTreeSet<String>,
}

fn observe(session: &Rc<Session>, root: &str) -> Observed {
    let relative = |name: &str| name.replace(root, "<root>");
    let snapshot = session.snapshot();
    let config = tspath::to_path(&format!("{root}/tsconfig.json"), root, true);
    let project = snapshot
        .project_collection
        .configured_project(&config)
        .expect("configured project");
    let project = project.borrow();
    let processed = &project.program.as_ref().expect("program").processed_files;
    let host = project.host.as_ref().expect("host");
    let paths = |set: &rustc_hash::FxHashSet<tspath::Path>| -> BTreeSet<String> {
        set.iter().map(|path| relative(path.as_str())).collect()
    };
    let mut resolutions = BTreeSet::new();
    for (file, cache) in processed.resolved_modules.iter() {
        for (key, module) in cache {
            resolutions.insert(relative(&format!(
                "{} {key:?} -> {} {} {} {:?} {} {} {:?}",
                file.as_str(),
                module.resolved_file_name,
                module.original_path,
                module.extension,
                module.package_id,
                module.is_external_library_import,
                module.resolved_using_ts_extension,
                module.resolution_diagnostics,
            )));
        }
    }
    Observed {
        files: processed
            .files
            .iter()
            .map(|file| relative(file.file_name()))
            .collect(),
        missing_files: processed
            .missing_files
            .iter()
            .map(|name| relative(name))
            .collect(),
        resolutions,
        seen: paths(
            &host
                .source_fs
                .seen_files
                .borrow()
                .as_ref()
                .unwrap()
                .borrow(),
        ),
        missing_directories: paths(
            &host
                .source_fs
                .missing_directories
                .as_ref()
                .unwrap()
                .borrow(),
        ),
        cached_files: snapshot
            .fs
            .cache_files
            .keys()
            .map(|path| relative(path.as_str()))
            .collect(),
    }
}

/// Runs `steps` on a new copy of the project in `mode`, and returns what
/// the last load left and its resolve-ahead counts. `steps` gets the
/// session and the project root and makes the loads.
fn run(
    label: &str,
    mode: Mode,
    steps: &dyn Fn(&Rc<Session>, &str),
) -> (Observed, Option<LoadStats>) {
    let root = make_project(&format!("{label}_{mode:?}"));
    resolve_ahead::set_mode(Some(mode));
    let session = os_session(&root);
    steps(&session, &root);
    let observed = observe(&session, &root);
    let stats = resolve_ahead::last_stats();
    resolve_ahead::set_mode(None);
    drop(session);
    std::fs::remove_dir_all(&root).unwrap();
    (observed, stats)
}

/// Runs `steps` with the loader resolving every key itself and with the
/// workers resolving every key first, and checks that the loads are the
/// same. Returns the resolve-ahead counts of the last load.
fn same_with_and_without(label: &str, steps: &dyn Fn(&Rc<Session>, &str)) -> LoadStats {
    let (serial, serial_stats) = run(label, Mode::Off, steps);
    let (ahead, stats) = run(label, Mode::Force, steps);
    assert_eq!(serial_stats, None, "resolve ahead ran in mode 0");
    assert_eq!(ahead, serial);
    let stats = stats.expect("no resolve-ahead load");
    assert!(stats.keys > 0, "{stats:?}");
    stats
}

/// Opens `src/index.ts` (the first load records its keys).
fn open_index(session: &Rc<Session>, root: &str) {
    open(session, &file_uri(root, "src/index.ts"), INDEX);
    program(session, &file_uri(root, "src/index.ts"));
}

/// Adds an import at the top of `src/index.ts` (version 2), which makes a
/// new program load.
fn add_import(session: &Rc<Session>, root: &str) {
    edit_index(session, root, 2, "import { d } from \"./sub/d\";\n");
}

/// Puts `text` at the top of `src/index.ts` as `version`, and loads the
/// program.
fn edit_index(session: &Rc<Session>, root: &str, version: i32, text: &str) {
    let uri = file_uri(root, "src/index.ts");
    edit(session, &uri, version, (0, 0), (0, 0), text);
    program(session, &uri);
}

/// The counts of the last resolve-ahead load on this thread.
fn last_stats() -> LoadStats {
    resolve_ahead::last_stats().expect("no resolve-ahead load")
}

/// Ends this test process when the test has not ended after `seconds`, so
/// a load that waits forever fails the test.
fn watchdog(seconds: u64) {
    use std::io::Write;
    std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_secs(seconds));
        // stdout: a test can close stderr, and `eprintln!` panics there.
        let _ = writeln!(
            std::io::stdout(),
            "watchdog: the test did not end in {seconds} s"
        );
        std::process::exit(3);
    });
}

os_child_test! {
    /// An import edit: every key of the previous load is taken, and the
    /// load is the same as a serial one.
    fn takes_every_answer_of_an_unchanged_project() {
        let stats = same_with_and_without("unchanged", &|session, root| {
            open_index(session, root);
            add_import(session, root);
        });
        assert_eq!(stats.loader.rejected, 0, "{stats:?}");
        assert_eq!(stats.loader.taken, stats.keys, "{stats:?}");
        assert_eq!(stats.new_keys, stats.keys + 1, "{stats:?}");
    }
}

os_child_test! {
    env &[("GOPORT_RESOLVE_AHEAD_THREADS", "1")];
    /// One worker resolves every key, so its package.json cache has the
    /// package.json of `pkg` when it resolves `pkg/other`. The answer must
    /// still list the calls of that read (debug builds check each taken
    /// answer against a new resolver's calls, `debug_check_answer`).
    fn one_worker_lists_the_package_json_reads_of_its_cache() {
        let stats = same_with_and_without("oneworker", &|session, root| {
            open_index(session, root);
            add_import(session, root);
        });
        assert_eq!(stats.loader.taken, stats.keys, "{stats:?}");
    }
}

os_child_test! {
    env &[("GOPORT_RESOLVE_AHEAD_THREADS", "1")];
    /// The one worker keeps the package.json parse of `@scope/lib` from
    /// the second load. Its directory is removed with no watch event, so
    /// the snapshot still has the package.json, but Go's lookup asks
    /// whether the directory exists and finds no package: the worker must
    /// not answer from the kept parse.
    fn a_kept_package_json_of_a_removed_directory_is_not_used() {
        let stats = same_with_and_without("keptgone", &|session, root| {
            open_index(session, root);
            add_import(session, root);
            std::fs::remove_dir_all(format!("{root}/node_modules/@scope/lib")).unwrap();
            let uri = file_uri(root, "src/index.ts");
            edit(
                session,
                &uri,
                3,
                (0, 0),
                (0, 0),
                "import { b as b2 } from \"./sub/b\";\n",
            );
            program(session, &uri);
        });
        assert!(stats.loader.missing >= 1, "{stats:?}");
    }
}

os_child_test! {
    /// The edit removes the import of `../lib/c`: the workers resolve its
    /// key, the loader never asks for it, and its file is not seen.
    fn an_untaken_answer_adds_no_seen_file() {
        let stats = same_with_and_without("untaken", &|session, root| {
            open_index(session, root);
            let uri = file_uri(root, "src/index.ts");
            edit(session, &uri, 2, (2, 0), (3, 0), "");
            program(session, &uri);
            let observed = observe(session, root);
            assert!(!observed.seen.contains("<root>/lib/c.ts"), "{observed:?}");
            assert!(observed.files.iter().all(|file| !file.ends_with("lib/c.ts")));
        });
        assert_eq!(stats.loader.taken + 1, stats.keys, "{stats:?}");
    }
}

os_child_test! {
    /// The disk changes between the loads with no watch event, so the
    /// snapshot still has the old texts and files: a changed package.json,
    /// a deleted source file, a new file in a new directory, a removed
    /// package directory. The workers see the new disk, and the check
    /// rejects each answer that the snapshot would make in another way.
    fn rejects_answers_that_the_snapshot_files_contradict() {
        let stats = same_with_and_without("disk", &|session, root| {
            open_index(session, root);
            write(
                root,
                "node_modules/pkg/package.json",
                r#"{ "name": "pkg", "version": "1.0.1", "types": "other.d.ts" }"#,
            );
            std::fs::remove_file(format!("{root}/src/a.ts")).unwrap();
            write(root, "src/missing/x.ts", "export const x = 4;");
            std::fs::remove_dir_all(format!("{root}/node_modules/@scope/lib")).unwrap();
            add_import(session, root);
        });
        assert!(stats.loader.rejected >= 2, "{stats:?}");
        assert!(stats.loader.taken > 0, "{stats:?}");
    }
}

os_child_test! {
    /// More than `EXCESSIVE_CHANGE_THRESHOLD` watch events in node_modules
    /// (an npm install) mark the cached node_modules files for a reload.
    /// The loader's own lookup would reload them (and drop the cached file
    /// that is gone), so the check rejects the answers that look them up
    /// until the loader has reloaded them.
    fn rejects_an_answer_whose_cached_file_needs_a_reload() {
        let stats = same_with_and_without("reload", &|session, root| {
            open_index(session, root);
            write(
                root,
                "node_modules/pkg/package.json",
                r#"{ "name": "pkg", "version": "1.0.2", "types": "other.d.ts" }"#,
            );
            std::fs::remove_file(format!("{root}/node_modules/@scope/lib/dist/main.d.ts")).unwrap();
            let mut events =
                generate_file_events(1001, &file_uri(root, "node_modules/pkg/f%d.d.ts"), CHANGED);
            events.push(Some(lsproto::FileEvent {
                uri: uri(&file_uri(root, "node_modules/pkg/package.json")),
                type_: CHANGED,
            }));
            session.did_change_watched_files(&bg(), &events);
            add_import(session, root);
        });
        assert!(stats.loader.rejected >= 1, "{stats:?}");
    }
}

os_child_test! {
    /// Open files that are not on disk: a new file in a new directory, which
    /// the workers see through the open file paths, and an open
    /// package.json, whose text the workers do not have (its answers are
    /// not shared).
    fn open_files_over_the_disk() {
        let stats = same_with_and_without("open", &|session, root| {
            open(session, &file_uri(root, "src/newdir/z.ts"), "export const z = 5;");
            open(
                session,
                &file_uri(root, "node_modules/pkg/package.json"),
                r#"{ "name": "pkg", "version": "1.0.3", "types": "other.d.ts" }"#,
            );
            let text = format!("import {{ z }} from \"./newdir/z\";\n{INDEX}");
            open(session, &file_uri(root, "src/index.ts"), &text);
            program(session, &file_uri(root, "src/index.ts"));
            add_import(session, root);
            let observed = observe(session, root);
            assert!(
                observed
                    .resolutions
                    .iter()
                    .any(|resolution| resolution.contains("\"./newdir/z\"")
                        && resolution.contains("-> <root>/src/newdir/z.ts")),
                "{observed:?}"
            );
        });
        assert!(stats.loader.taken > 0, "{stats:?}");
        assert!(stats.loader.missing > 0, "{stats:?}");
    }
}

os_child_test! {
    /// A rejected answer makes the workers drop what they keep (the known
    /// files and the package.json parses). When a load on another thread
    /// has the workers at the next load, the next load that has them must
    /// still start with none.
    fn a_rejected_answer_drops_the_kept_state_while_the_workers_are_taken() {
        let root = make_project("heldreject");
        resolve_ahead::set_mode(Some(Mode::Force));
        let session = os_session(&root);
        open_index(&session, &root);
        add_import(&session, &root);
        resolve_ahead::wait_for_frees();
        // An npm install: the cached node_modules files need a reload, so
        // the check rejects the answers that look them up.
        let events =
            generate_file_events(1001, &file_uri(&root, "node_modules/pkg/f%d.d.ts"), CHANGED);
        session.did_change_watched_files(&bg(), &events);
        edit_index(&session, &root, 3, "import { b as b2 } from \"./sub/b\";\n");
        let stats = last_stats();
        assert!(stats.loader.rejected >= 1, "{stats:?}");
        assert!(stats.known_files > 0, "{stats:?}");
        resolve_ahead::wait_for_frees();
        let held = resolve_ahead::hold_workers();
        edit_index(&session, &root, 4, "import { a as a2 } from \"./a\";\n");
        let stats = last_stats();
        assert_eq!(stats.loader.taken, 0, "the workers ran: {stats:?}");
        drop(held);
        edit_index(&session, &root, 5, "import { c as c2 } from \"../lib/c\";\n");
        let stats = last_stats();
        assert!(stats.loader.taken > 0, "{stats:?}");
        assert_eq!(stats.known_files, 0, "{stats:?}");
        resolve_ahead::set_mode(None);
        drop(session);
        std::fs::remove_dir_all(&root).unwrap();
    }
}

os_child_test! {
    /// A worker that panics outside a resolution (a port bug; a test hook
    /// makes one) must not make a load that waits for the workers
    /// (`Mode::Force`) wait forever, nor leave the pool: that load resolves
    /// its keys itself, and the next load takes every answer again. The
    /// workers panic after they resolved their keys, so their answers are
    /// there: the load takes none of them (`AheadQueue::fail`).
    fn a_worker_panic_outside_a_resolution_makes_the_load_serial() {
        watchdog(120);
        let stats = same_with_and_without("panic", &|session, root| {
            open_index(session, root);
            resolve_ahead::inject_worker_panic(true);
            add_import(session, root);
            resolve_ahead::inject_worker_panic(false);
            if let Some(stats) = resolve_ahead::last_stats() {
                assert!(stats.worker_panic, "{stats:?}");
                assert_eq!(stats.loader.taken, 0, "{stats:?}");
            }
            edit_index(session, root, 3, "import { b as b2 } from \"./sub/b\";\n");
        });
        assert!(!stats.worker_panic, "{stats:?}");
        assert_eq!(stats.loader.taken, stats.keys, "{stats:?}");
    }
}

os_child_test! {
    env &[("GOPORT_RESOLVE_AHEAD_STATS", "1")];
    /// The debug log (`GOPORT_RESOLVE_AHEAD_STATS=1`) writes to stderr. When
    /// stderr is a pipe with no reader, each write fails (EPIPE). A worker
    /// that caught a panic logs it before it counts itself out of the job
    /// (`run_task`), so a write that panics (R162: `eprintln!`) ends the
    /// worker there, and a load that waits for the workers (`Mode::Force`)
    /// waits forever. The load must resolve its keys itself, and the next
    /// load must take every answer, so no worker left the pool.
    #[cfg(unix)]
    fn a_worker_panic_logs_to_a_closed_stderr_and_the_load_goes_on() {
        watchdog(120);
        close_stderr();
        let root = make_project("closedstderr");
        resolve_ahead::set_mode(Some(Mode::Force));
        let session = os_session(&root);
        open_index(&session, &root);
        resolve_ahead::inject_worker_panic(true);
        add_import(&session, &root);
        resolve_ahead::inject_worker_panic(false);
        let stats = last_stats();
        assert!(stats.worker_panic, "{stats:?}");
        assert_eq!(stats.loader.taken, 0, "{stats:?}");
        edit_index(&session, &root, 3, "import { b as b2 } from \"./sub/b\";\n");
        let stats = last_stats();
        assert!(!stats.worker_panic, "{stats:?}");
        assert_eq!(stats.loader.taken, stats.keys, "{stats:?}");
        resolve_ahead::set_mode(None);
        drop(session);
        std::fs::remove_dir_all(&root).unwrap();
    }
}

/// Makes stderr a pipe with no reader, so each write to it fails with EPIPE
/// (a Rust program ignores SIGPIPE). A closed fd 2 would not do: the
/// standard library drops writes to it (EBADF) with no error.
#[cfg(unix)]
fn close_stderr() {
    let (reader, writer) = std::io::pipe().expect("a pipe");
    drop(reader);
    rustix::stdio::dup2_stderr(&writer).expect("stderr to the pipe");
}

/// The project of `a_released_project_drops_the_kept_state` in `other/`,
/// with its own package.
const OTHER_MAIN: &str =
    "import { q } from \"./q\";\nimport { r } from \"opkg\";\nexport const both = [q, r];\n";
const OTHER_FILES: &[(&str, &str)] = &[
    (
        "other/tsconfig.json",
        r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler", "noLib": true, "strict": true }, "include": ["src"] }"#,
    ),
    ("other/src/main.ts", OTHER_MAIN),
    ("other/src/q.ts", "export const q = 1;"),
    (
        "other/node_modules/opkg/package.json",
        r#"{ "name": "opkg", "version": "1.0.0", "types": "index.d.ts" }"#,
    ),
    (
        "other/node_modules/opkg/index.d.ts",
        "export declare const r: number;",
    ),
];

os_child_test! {
    /// The workers keep the files that the answers of a project's loads
    /// found, from load to load of the project. When the project's
    /// programs are released (its only open file is closed and the file of
    /// another project opens), they drop them: the next job, of the other
    /// project, starts with no known file.
    fn a_released_project_drops_the_kept_state() {
        let root = make_project("released");
        for (name, text) in OTHER_FILES {
            write(&root, name, text);
        }
        resolve_ahead::set_mode(Some(Mode::Force));
        let session = os_session(&root);
        open_index(&session, &root);
        add_import(&session, &root);
        resolve_ahead::wait_for_frees();
        edit_index(&session, &root, 3, "import { b as b2 } from \"./sub/b\";\n");
        let stats = last_stats();
        assert!(stats.known_files > 0, "{stats:?}");
        close(&session, &file_uri(&root, "src/index.ts"));
        let main = file_uri(&root, "other/src/main.ts");
        open(&session, &main, OTHER_MAIN);
        program(&session, &main);
        let config = tspath::to_path(&format!("{root}/tsconfig.json"), &root, true);
        assert!(
            session
                .snapshot()
                .project_collection
                .configured_project(&config)
                .is_none(),
            "the first project is still open"
        );
        resolve_ahead::wait_for_frees();
        edit(&session, &main, 2, (0, 0), (0, 0), "import { q as q2 } from \"./q\";\n");
        program(&session, &main);
        let stats = last_stats();
        assert!(stats.loader.taken > 0, "{stats:?}");
        assert_eq!(stats.known_files, 0, "{stats:?}");
        resolve_ahead::set_mode(None);
        drop(session);
        std::fs::remove_dir_all(&root).unwrap();
    }
}

/// The import of `rpkg`, a package whose node_modules directory is a
/// symlink (`symlinked_rpkg`).
const RPKG_INDEX: &str = "import { r } from \"rpkg\";\n";

/// Adds `store/rpkg` and `store/rpkg2`, two copies of a package, and
/// `node_modules/rpkg`, a symlink to the first.
#[cfg(unix)]
fn symlinked_rpkg(root: &str) {
    for copy in ["rpkg", "rpkg2"] {
        write(
            root,
            &format!("store/{copy}/package.json"),
            r#"{ "name": "rpkg", "version": "1.0.0", "types": "index.d.ts" }"#,
        );
        write(
            root,
            &format!("store/{copy}/index.d.ts"),
            "export declare const r: number;",
        );
    }
    point_rpkg(root, "rpkg");
}

/// Points the symlink `node_modules/rpkg` to `store/<copy>`.
#[cfg(unix)]
fn point_rpkg(root: &str, copy: &str) {
    let link = format!("{root}/node_modules/rpkg");
    let _ = std::fs::remove_file(&link);
    std::os::unix::fs::symlink(format!("{root}/store/{copy}"), &link).unwrap();
}

/// The resolution of `name` in `src/index.ts`: the resolved file name and
/// the original path, relative to the project root.
#[cfg(unix)]
fn resolution(session: &Rc<Session>, root: &str, name: &str) -> (String, String) {
    let program = program(session, &file_uri(root, "src/index.ts"));
    let index = tspath::to_path(&format!("{root}/src/index.ts"), root, true);
    let modules = program
        .processed_files
        .resolved_modules
        .get(&index)
        .expect("resolutions of src/index.ts");
    let (_, module) = modules
        .iter()
        .find(|(key, _)| key.name == name)
        .unwrap_or_else(|| panic!("no resolution of {name}"));
    let relative = |name: &str| name.replace(root, "<root>");
    (
        relative(&module.resolved_file_name),
        relative(&module.original_path),
    )
}

os_child_test! {
    /// The disk changes during a load: after the workers resolved the keys
    /// of the previous load and before the loader starts (a test hook), a
    /// new directory gets a file, a package gets a new file and a package
    /// symlink points to another copy. The loader takes the worker answers,
    /// which saw the old disk, and then resolves new keys that make the
    /// same `directory_exists`, `file_exists` and `realpath` calls. As in Go,
    /// whose snapshot caches the first answer of each call, each such call
    /// must give the answer that the load took, so the program has one
    /// answer for each path.
    #[cfg(unix)]
    fn a_load_has_one_answer_per_path_when_the_disk_changes_during_it() {
        let root = make_project("onepath");
        symlinked_rpkg(&root);
        resolve_ahead::set_mode(Some(Mode::Force));
        let session = os_session(&root);
        let uri = file_uri(&root, "src/index.ts");
        open(&session, &uri, &format!("{INDEX}{RPKG_INDEX}"));
        program(&session, &uri);
        let changed_root = root.clone();
        resolve_ahead::set_after_workers(Some(Rc::new(move || {
            let root = &changed_root;
            write(root, "src/missing/x.ts", "export const x = 4;");
            write(root, "node_modules/pkg/other.ts", "export const o = 5;");
            point_rpkg(root, "rpkg2");
        })));
        edit(
            &session,
            &uri,
            2,
            (10, 0),
            (10, 0),
            "import { x as x2 } from \"./missing/x.js\";\n\
             import { o as o2 } from \"pkg/other.js\";\n\
             import { r as r2 } from \"rpkg/index.js\";\n",
        );
        program(&session, &uri);
        resolve_ahead::set_after_workers(None);
        let stats = last_stats();
        assert_eq!(stats.loader.taken, stats.keys, "{stats:?}");
        assert_eq!(stats.loader.rejected, 0, "{stats:?}");
        for (taken, own) in [
            ("./missing/x", "./missing/x.js"),
            ("pkg/other", "pkg/other.js"),
            ("rpkg", "rpkg/index.js"),
        ] {
            assert_eq!(
                resolution(&session, &root, own).0,
                resolution(&session, &root, taken).0,
                "{own} and {taken}"
            );
        }
        assert_eq!(
            resolution(&session, &root, "rpkg"),
            (
                "<root>/store/rpkg/index.d.ts".to_string(),
                "<root>/node_modules/rpkg/index.d.ts".to_string()
            )
        );
        resolve_ahead::set_mode(None);
        drop(session);
        std::fs::remove_dir_all(&root).unwrap();
    }
}

os_child_test! {
    /// A load takes the answers of the workers, and the workers' parses of
    /// the package.json files stay on the workers. A later lookup of the
    /// program's resolver (`Program::get_package_json_info`, as auto-imports
    /// make) must find the package.json lookups of the taken answers, as Go's
    /// one cache of the load's resolutions has them. Here the disk changed
    /// after the load and the snapshot's lookup cache is empty, so only the
    /// load job's lookups (`AheadLookupLayer`) give the taken answers; a disk
    /// call would find the new disk. `broken` has a
    /// package.json but no types file, and `not-installed` has no directory;
    /// no file of the program is in them, so the loader did not look them up
    /// itself.
    fn a_later_package_json_lookup_uses_the_taken_answers() {
        let root = make_project("pjlookup");
        write(
            &root,
            "node_modules/broken/package.json",
            r#"{ "name": "broken", "version": "1.0.0", "types": "gone.d.ts" }"#,
        );
        resolve_ahead::set_mode(Some(Mode::Force));
        let session = os_session(&root);
        let uri = file_uri(&root, "src/index.ts");
        open(
            &session,
            &uri,
            &format!("{INDEX}import {{ z }} from \"broken\";\n"),
        );
        program(&session, &uri);
        edit_index(&session, &root, 2, "import { d } from \"./sub/d\";\n");
        let stats = last_stats();
        assert_eq!(stats.loader.taken, stats.keys, "{stats:?}");
        let program = program(&session, &uri);
        let broken = format!("{root}/node_modules/broken/package.json");
        let not_installed = format!("{root}/node_modules/not-installed/package.json");
        let resolver = program
            .processed_files
            .resolver
            .as_ref()
            .and_then(|resolver| resolver.as_default_resolver())
            .expect("the default resolver");
        for name in [&broken, &not_installed] {
            assert!(
                resolver.caches.package_json_info_cache.get(name).is_none(),
                "the loader looked up {name} itself"
            );
        }
        std::fs::remove_dir_all(format!("{root}/node_modules/broken")).unwrap();
        write(
            &root,
            "node_modules/not-installed/package.json",
            r#"{ "name": "not-installed", "version": "1.0.0" }"#,
        );
        let snapshot = session.snapshot();
        let config = tspath::to_path(&format!("{root}/tsconfig.json"), &root, true);
        let project = snapshot
            .project_collection
            .configured_project(&config)
            .expect("configured project");
        let source = project
            .borrow()
            .host
            .as_ref()
            .expect("host")
            .source_fs
            .source
            .borrow()
            .clone();
        let lookups = source.fs();
        ts_goport::frontend::vfs::Fs::as_any(&*lookups)
            .and_then(|fs| fs.downcast_ref::<project::snapshotfs::CachedLayeredFileSystem>())
            .expect("the snapshot's lookup cache")
            .fs
            .clear_cache();
        let info = program
            .get_package_json_info(&broken)
            .expect("the package.json of broken");
        let (name, _) = info
            .get_contents()
            .expect("contents")
            .header_fields
            .name
            .get_value();
        assert_eq!(name, "broken");
        assert!(
            program.get_package_json_info(&not_installed).is_none(),
            "a package.json in a directory that the load found missing"
        );
        resolve_ahead::set_mode(None);
        drop(program);
        drop(project);
        drop(snapshot);
        drop(session);
        std::fs::remove_dir_all(&root).unwrap();
    }
}
