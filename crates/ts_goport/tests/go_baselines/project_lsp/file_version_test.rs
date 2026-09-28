//! PORT: no Go counterpart. Go's GC frees a `*ast.SourceFile` when no
//! program and no parse cache entry holds it. Here the language server
//! gives each new version of a path that it published before a
//! `FileVersion` (lsshells M3a): the parse holds it, and so do the tables
//! of each program version that has the file. It dies with its last holder.
//! The first version of a file and every CLI publish stay static.

use std::rc::Rc;
use std::sync::mpsc;

use ts_goport::ast::{
    dead_file_versions, file_version_probe, file_versions_made, free_file_versions,
    source_file_info,
};
use ts_goport::core::Node;
use ts_goport::frontend::compiler::NewProgram;
use ts_goport::lsp::lsproto;
use ts_goport::program::{self, ls_program};
use ts_goport::project::Session;

use super::projecttestutil::{FileMap, files, wrapped_map_fs};
use super::util::*;

const CONFIG: &str = "/home/projects/TS/p1/tsconfig.json";
const INDEX_URI: &str = "file:///home/projects/TS/p1/index.ts";
const INDEX_FILE: &str = "/home/projects/TS/p1/index.ts";
const INDEX_TEXT: &str = "import { a } from './a';\nexport const x = a + 1;";
const A_FILE: &str = "/home/projects/TS/p1/a.ts";

fn p1_files() -> FileMap {
    files(&[
        (CONFIG, "{}"),
        (INDEX_FILE, INDEX_TEXT),
        (A_FILE, "export const a = 1;"),
        ("/home/projects/TS/p1/b.ts", "export const b = 1;"),
    ])
}

/// A session with index.ts open and its program loaded.
fn open_p1() -> Rc<Session> {
    let session = bare_session(p1_files());
    open(&session, INDEX_URI, INDEX_TEXT);
    let _ = language_service(&session, INDEX_URI);
    session
}

/// Replaces the `1` of `INDEX_TEXT` (a body edit, which clones the
/// program) and loads the program. The snapshot change releases the old
/// program, and its files leave the parse cache.
fn body_edit(session: &Rc<Session>, version: i32, digit: &str) {
    edit(session, INDEX_URI, version, (1, 21), (1, 22), digit);
    let _ = language_service(session, INDEX_URI);
    session.wait_for_background_tasks();
}

/// Adds an import to index.ts (a new program load) and loads the program.
fn import_edit(session: &Rc<Session>, version: i32) {
    edit(
        session,
        INDEX_URI,
        version,
        (0, 0),
        (0, 0),
        "import { b } from './b';\n",
    );
    let _ = language_service(session, INDEX_URI);
    session.wait_for_background_tasks();
}

/// The root of `name` in `p`.
fn root(p: &NewProgram, name: &str) -> Node {
    p.get_source_file(name)
        .unwrap_or_else(|| panic!("{name} is in the program"))
        .root
}

child_test! {
    // Each edit of index.ts makes a freeable version. A version dies when
    // the programs that have it are released and its parse leaves the
    // parse cache, so N edits leave one live version. The first version of
    // index.ts and the unchanged a.ts stay static and readable.
    fn edited_file_versions_die_with_their_last_holder() {
        let session = open_p1();
        let first = root(&program(&session, INDEX_URI), INDEX_FILE);
        assert!(free_file_versions(), "a session process frees file versions");
        assert!(file_version_probe(first).is_none(), "the first version is static");

        body_edit(&session, 2, "2");
        let p2 = program(&session, INDEX_URI);
        let second = file_version_probe(root(&p2, INDEX_FILE))
            .expect("the edited version of a published path is freeable");
        assert!(file_version_probe(root(&p2, A_FILE)).is_none(), "a.ts is static");
        drop(p2);

        body_edit(&session, 3, "3");
        let third = file_version_probe(root(&program(&session, INDEX_URI), INDEX_FILE))
            .expect("the edited version is freeable");
        assert!(second.is_freed(), "the version of a released program is not freed");
        assert!(!third.is_freed());

        import_edit(&session, 4);
        let p4 = program(&session, INDEX_URI);
        let fourth = file_version_probe(root(&p4, INDEX_FILE)).expect("the edited version is freeable");
        assert!(third.is_freed(), "the version of a released clone is not freed");
        assert!(!fourth.is_freed());
        assert_eq!((file_versions_made(), dead_file_versions()), (3, 2));

        assert_eq!(sem_diag_count(&p4, INDEX_FILE), 0);
        assert_eq!(source_file_info(first).file_name, INDEX_FILE);
    }
}

child_test! {
    // A holder of the frontend program keeps its file versions through the
    // parse. A thread seeded from a program version keeps them through the
    // version's tables after the release and after the frontend program
    // goes. Each version dies when its last holder lets go.
    fn program_and_seeded_thread_keep_file_versions() {
        let session = open_p1();
        body_edit(&session, 2, "2");
        let p2 = program(&session, INDEX_URI);
        let second = file_version_probe(root(&p2, INDEX_FILE)).expect("freeable");

        body_edit(&session, 3, "3");
        assert!(!second.is_freed(), "the held program keeps its file version");
        drop(p2);
        assert!(second.is_freed(), "the program's file version is not freed");

        let p3 = program(&session, INDEX_URI);
        let third = file_version_probe(root(&p3, INDEX_FILE)).expect("freeable");
        let (start, started) = mpsc::channel::<()>();
        let reader = {
            let _program = ls_program::enter(&p3);
            program::spawn_seeded_thread(move || {
                started.recv().expect("the test thread sends start");
                program::get_source_file(INDEX_FILE).is_some()
            })
        };
        drop(p3);

        body_edit(&session, 4, "4");
        assert!(!third.is_freed(), "the seeded thread keeps the file version");
        start.send(()).expect("the seeded thread waits");
        assert!(reader.join().expect("the seeded thread reads the released version"));
        assert!(third.is_freed(), "the file version outlives the seeded thread");
    }
}

const JS_URI: &str = "file:///home/projects/TS/p2/index.js";
const JS_FILE: &str = "/home/projects/TS/p2/index.js";
const JS_TEXT: &str = "/** @type {number} */\nexport const x = 1;\nconst y = ;\n";

child_test! {
    // A freeable version keeps no parse: its `GoFile` reads copies of the
    // parse diagnostics and the JSDoc cache, which stay after the version
    // dies.
    fn dead_file_version_reads_diagnostics_and_js_doc() {
        let session = bare_session(files(&[
            (
                "/home/projects/TS/p2/tsconfig.json",
                r#"{"compilerOptions": {"allowJs": true, "checkJs": true}}"#,
            ),
            (JS_FILE, JS_TEXT),
        ]));
        open_kind(&session, JS_URI, JS_TEXT, lsproto::LanguageKind::JAVA_SCRIPT);
        let _ = program(&session, JS_URI);
        edit(&session, JS_URI, 2, (1, 17), (1, 18), "2");
        let (probe, root, statement) = {
            let p = program(&session, JS_URI);
            let root = root(&p, JS_FILE);
            let probe = file_version_probe(root).expect("the edited version is freeable");
            (probe, root, root.statements().get(0))
        };
        let diagnostics = |root: Node| -> Vec<(i32, i32, i32)> {
            source_file_info(root)
                .diagnostics
                .iter()
                .map(|d| (d.code, d.pos, d.end))
                .collect()
        };
        let before = diagnostics(root);
        assert!(!before.is_empty(), "index.js has a parse error");
        assert_eq!(statement.js_doc(root).len(), 1);

        edit(&session, JS_URI, 3, (1, 17), (1, 18), "3");
        let live = program(&session, JS_URI);
        session.wait_for_background_tasks();
        assert!(probe.is_freed(), "the version of the released program is not freed");

        let _program = ls_program::enter(&live);
        assert_eq!(diagnostics(root), before);
        assert_eq!(statement.js_doc(root).len(), 1);
    }
}

child_test! {
    // A CLI process (no session) frees no file version: its publishes are
    // all static.
    fn cli_process_makes_no_file_versions() {
        let _fs = wrapped_map_fs(p1_files(), false);
        let program = program::try_load(CONFIG)
            .unwrap_or_else(|error| panic!("cannot load {CONFIG}: {error}"));
        assert!(!free_file_versions());
        assert_eq!(file_versions_made(), 0);
        assert!(
            program
                .source_files()
                .all(|file| file_version_probe(file.root).is_none())
        );
    }
}
