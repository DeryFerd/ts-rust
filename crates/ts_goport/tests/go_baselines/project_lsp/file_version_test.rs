//! PORT: no Go counterpart. Go's GC frees a `*ast.SourceFile` when no
//! program and no parse cache entry holds it. Here the language server
//! gives each new version of a path that it published before a
//! `FileVersion` (lsshells M3a): the parse holds it, and so do the tables
//! of each program version that has the file. It dies with its last holder,
//! and its store and `GoFile` die with it (M3b); a later read of it panics.
//! The first version of a file and every CLI publish stay static.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;
use std::sync::mpsc;

use ts_goport::ast::{
    dead_file_versions, file_version_probe, file_versions_made, free_file_versions,
    source_file_ecma_line_map, source_file_get_declaration_map, source_file_get_name_table,
    source_file_imports, source_file_info,
};
use ts_goport::astdata::SyntaxKind;
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

/// The panic message of `read`, or `None` when it does not panic.
fn panic_message(read: impl FnOnce()) -> Option<String> {
    let payload = catch_unwind(AssertUnwindSafe(read)).err()?;
    Some(
        payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_default(),
    )
}

child_test! {
    // A freeable version keeps no parse: its `GoFile` owns copies of the
    // parse diagnostics and the JSDoc cache, and its JSDoc slice reads the
    // cache at each use. When the version dies they go with it, and a read
    // of its store or `GoFile` panics (a stale read never reads other data).
    // Its node columns are leaked in its node shell (lsshells M3 repair), so
    // a stale node read gives the data of that node.
    fn freeable_version_owns_its_lists_and_a_stale_read_panics() {
        let session = bare_session(files(&[
            (
                "/home/projects/TS/p2/tsconfig.json",
                r#"{"compilerOptions": {"allowJs": true, "checkJs": true}}"#,
            ),
            (JS_FILE, JS_TEXT),
        ]));
        open_kind(&session, JS_URI, JS_TEXT, lsproto::LanguageKind::JAVA_SCRIPT);
        let first = root(&program(&session, JS_URI), JS_FILE);
        let diagnostics = |root: Node| -> Vec<(i32, i32, i32)> {
            source_file_info(root)
                .diagnostics
                .iter()
                .map(|d| (d.code, d.pos, d.end))
                .collect()
        };
        let static_diagnostics = diagnostics(first);
        assert!(!static_diagnostics.is_empty(), "index.js has a parse error");

        edit(&session, JS_URI, 2, (1, 17), (1, 18), "2");
        let (probe, edited, statement) = {
            let p = program(&session, JS_URI);
            let root = root(&p, JS_FILE);
            let probe = file_version_probe(root).expect("the edited version is freeable");
            (probe, root, root.statements().get(0))
        };
        // The edit keeps every length, so the positions do not change.
        assert_eq!(diagnostics(edited), static_diagnostics);
        let jsdoc = statement.js_doc(edited);
        assert_eq!(jsdoc.len(), 1);
        assert_eq!(jsdoc.get(0).kind(), SyntaxKind::JsDoc);
        let statement_kind = statement.kind();

        edit(&session, JS_URI, 3, (1, 17), (1, 18), "3");
        let live = program(&session, JS_URI);
        session.wait_for_background_tasks();
        assert!(probe.is_freed(), "the version of the released program is not freed");

        let _program = ls_program::enter(&live);
        let stale = format!("file version {} is released", edited.file_index());
        let info = panic_message(|| {
            let _ = source_file_info(edited).file_name.len();
        });
        assert_eq!(info.as_deref(), Some(stale.as_str()), "a GoFile read of a dead version");
        let flags = panic_message(|| {
            let _ = statement.flags();
        });
        assert_eq!(flags.as_deref(), Some(stale.as_str()), "a binder read of a dead version");
        assert_eq!(statement.kind(), statement_kind, "a node column read of a dead version");
        assert_eq!(diagnostics(root(&live, JS_FILE)), static_diagnostics);
        assert_eq!(diagnostics(first), static_diagnostics, "the first version is static");
    }
}

/// The nodes of the tree of `root` in `for_each_child` order.
fn tree(root: Node) -> Vec<Node> {
    fn walk(n: Node, out: &mut Vec<Node>) {
        out.push(n);
        n.for_each_child(|child| {
            walk(child, out);
            false
        });
    }
    let mut out = Vec::new();
    walk(root, &mut out);
    out
}

/// What the accessors give for one node.
#[derive(Debug, PartialEq)]
struct NodeFacts {
    kind: SyntaxKind,
    pos: i32,
    end: i32,
    flags: u32,
    parent_kind: SyntaxKind,
    /// The text of an identifier, else empty.
    text: String,
    has_symbol: bool,
    has_flow_node: bool,
}

/// The `NodeFacts` of `n`.
fn node_facts(n: Node) -> NodeFacts {
    let parent = n.parent();
    NodeFacts {
        kind: n.kind(),
        pos: n.pos(),
        end: n.end(),
        flags: n.flags().0,
        parent_kind: if parent.is_nil() {
            SyntaxKind::Unknown
        } else {
            parent.kind()
        },
        text: if n.kind() == SyntaxKind::Identifier {
            n.text().to_string()
        } else {
            String::new()
        },
        has_symbol: n.symbol().is_some(),
        has_flow_node: n.flow_node().is_some(),
    }
}

const TWIN_FILE: &str = "/home/projects/TS/p1/twin.ts";
/// `INDEX_TEXT` after `body_edit(.., "2")`.
const EDITED_TEXT: &str = "import { a } from './a';\nexport const x = a + 2;";

child_test! {
    // Twin files: twin.ts has the text of index.ts after an edit, so its
    // static first version and the freeable edited version of index.ts are
    // twin parses. Every accessor gives the same answer on both: node
    // columns, binder data, file info, line map, name table, declaration
    // map, imports and diagnostics.
    fn twin_parses_answer_the_same() {
        let mut map = p1_files();
        map.extend(files(&[(TWIN_FILE, EDITED_TEXT)]));
        let session = bare_session(map);
        open(&session, INDEX_URI, INDEX_TEXT);
        let _ = language_service(&session, INDEX_URI);
        body_edit(&session, 2, "2");
        let p2 = program(&session, INDEX_URI);
        assert_eq!(text(&p2, INDEX_FILE), EDITED_TEXT);
        let (edited, twin) = (root(&p2, INDEX_FILE), root(&p2, TWIN_FILE));
        assert!(file_version_probe(edited).is_some(), "the edited version is freeable");
        assert!(file_version_probe(twin).is_none(), "twin.ts is static");

        let (a, b) = (tree(edited), tree(twin));
        assert_eq!(a.len(), b.len());
        for (&a, &b) in a.iter().zip(&b) {
            assert_eq!(node_facts(a), node_facts(b), "node {a:?} and its twin {b:?}");
        }
        let info = |root: Node| {
            let info = source_file_info(root);
            (
                info.is_declaration_file,
                info.diagnostics.len(),
                info.external_module_indicator.is_some(),
            )
        };
        assert_eq!(info(edited), info(twin));
        let imports = |root: Node| -> Vec<String> {
            source_file_imports(root)
                .iter()
                .map(|n| n.text().to_string())
                .collect()
        };
        assert_eq!(imports(edited), imports(twin));
        assert_eq!(*source_file_ecma_line_map(edited), *source_file_ecma_line_map(twin));
        assert_eq!(*source_file_get_name_table(edited), *source_file_get_name_table(twin));
        let declarations = |root: Node| -> Vec<String> {
            let mut names: Vec<String> =
                source_file_get_declaration_map(root).keys().cloned().collect();
            names.sort();
            names
        };
        assert_eq!(declarations(edited), declarations(twin));
        assert_eq!(sem_diag_count(&p2, INDEX_FILE), sem_diag_count(&p2, TWIN_FILE));
    }
}

child_test! {
    // A thread seeded before the release reads its freeable version (its
    // columns and its GoFile) until it ends; the version dies after that.
    fn seeded_thread_reads_a_released_version_until_it_ends() {
        let session = open_p1();
        body_edit(&session, 2, "2");
        let p2 = program(&session, INDEX_URI);
        let second = root(&p2, INDEX_FILE);
        let probe = file_version_probe(second).expect("freeable");
        let expected = tree(second).into_iter().map(node_facts).collect::<Vec<_>>();
        let (start, started) = mpsc::channel::<()>();
        let reader = {
            let _program = ls_program::enter(&p2);
            program::spawn_seeded_thread(move || {
                started.recv().expect("the test thread sends start");
                let facts: Vec<_> = tree(second).into_iter().map(node_facts).collect();
                (facts, source_file_info(second).file_name.clone())
            })
        };
        drop(p2);

        body_edit(&session, 3, "3");
        assert!(!probe.is_freed(), "the seeded thread keeps the file version");
        start.send(()).expect("the seeded thread waits");
        let (facts, file_name) = reader.join().expect("the seeded thread reads the released version");
        assert_eq!(facts, expected);
        assert_eq!(file_name, INDEX_FILE);
        assert!(probe.is_freed(), "the file version outlives the seeded thread");
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
        assert_eq!((file_versions_made(), dead_file_versions()), (0, 0));
        assert!(
            program
                .source_files()
                .all(|file| file_version_probe(file.root).is_none())
        );
    }
}

/// `GOPORT_FREE_FILE_VERSIONS=0` in a session: every file version is
/// static, as before M3a, so a version of a released program still reads.
#[test]
fn flag_off_keeps_every_file_version_static() {
    let path = concat!(module_path!(), "::flag_off_keeps_every_file_version_static");
    let test = path.split_once("::").map_or(path, |(_, rest)| rest);
    crate::support::child::run_test_in_child_with_env(
        test,
        &[("GOPORT_FREE_FILE_VERSIONS", "0")],
        || {
            crate::project_lsp::projecttestutil::install_fs_override();
            let session = open_p1();
            assert!(!free_file_versions(), "the flag turns freeing off");
            body_edit(&session, 2, "2");
            let second = root(&program(&session, INDEX_URI), INDEX_FILE);
            assert!(
                file_version_probe(second).is_none(),
                "the edited version is static"
            );
            body_edit(&session, 3, "3");
            import_edit(&session, 4);
            assert_eq!((file_versions_made(), dead_file_versions()), (0, 0));
            assert_eq!(source_file_info(second).file_name, INDEX_FILE);
            assert!(!tree(second).is_empty());
        },
    );
}
