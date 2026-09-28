//! PORT: no Go counterpart. Go's GC frees a `*compiler.Program` when no
//! snapshot, request or other holder has it. Here the language server holds
//! each `NewProgram` in an `Rc` (the project, its checker pool, the
//! `ls_program` registry, a language service), so a released program is
//! freed with its last holder (lsshells M2b). A clone shares the processed
//! files of the load it came from, as Go `UpdateProgram` does. The publish
//! of a file keeps that file's parse, because its `GoFile` borrows it.

use std::rc::{Rc, Weak};

use ts_goport::ast::source_file_info;
use ts_goport::frontend::compiler::NewProgram;
use ts_goport::lsp::lsproto;
use ts_goport::program::ls_program;
use ts_goport::project::Session;

use super::projecttestutil::{FileMap, files};
use super::util::*;

const INDEX_URI: &str = "file:///home/projects/TS/p1/index.ts";
const INDEX_TEXT: &str = "import { a } from './a';\nexport const x = a + 1;";

fn p1_files() -> FileMap {
    files(&[
        ("/home/projects/TS/p1/tsconfig.json", "{}"),
        ("/home/projects/TS/p1/index.ts", INDEX_TEXT),
        ("/home/projects/TS/p1/a.ts", "export const a = 1;"),
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
/// program) and loads the program. The snapshot change releases the
/// program before, once the background tasks that hold the old snapshot
/// ran.
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

/// A weak handle of the current program of index.ts.
fn current_program(session: &Rc<Session>) -> Weak<NewProgram> {
    Rc::downgrade(&program(session, INDEX_URI))
}

child_test! {
    // A released load and a released clone are freed after the release and
    // the snapshot drop, so no reference cycle keeps them. A holder that
    // keeps the `Rc` keeps a released program, as a Go pointer does, until
    // it drops it.
    fn released_programs_are_freed() {
        let session = open_p1();
        let load = current_program(&session);

        body_edit(&session, 2, "2");
        let clone = program(&session, INDEX_URI);
        assert!(load.upgrade().is_none(), "the released load is not freed");

        import_edit(&session, 3);
        let live = current_program(&session);
        let released_clone = Rc::downgrade(&clone);
        assert!(released_clone.upgrade().is_some(), "a holder keeps the program");
        assert!(has_file(&clone, "/home/projects/TS/p1/a.ts"));
        drop(clone);
        assert!(released_clone.upgrade().is_none(), "the released clone is not freed");
        assert!(live.upgrade().is_some(), "the live program is freed");
        assert_eq!(sem_diag_count(&program(&session, INDEX_URI), "/home/projects/TS/p1/index.ts"), 0);
    }
}

child_test! {
    // The processed files of the first load (here its module resolutions)
    // live while a clone of it lives, and go with the last clone.
    fn first_load_processed_files_live_until_last_clone_goes() {
        let session = open_p1();
        let (load, resolutions) = {
            let p = program(&session, INDEX_URI);
            (Rc::downgrade(&p), Rc::downgrade(&p.resolved_modules))
        };

        body_edit(&session, 2, "2");
        let first_clone = current_program(&session);
        assert!(load.upgrade().is_none(), "the released load is not freed");
        assert!(
            Rc::ptr_eq(
                &resolutions.upgrade().expect("the clone keeps the load's resolutions"),
                &program(&session, INDEX_URI).resolved_modules,
            ),
            "the clone does not share the load's resolutions"
        );

        body_edit(&session, 3, "3");
        assert!(first_clone.upgrade().is_none(), "the released clone is not freed");
        assert!(resolutions.upgrade().is_some(), "the last clone keeps the load's resolutions");

        import_edit(&session, 4);
        assert!(resolutions.upgrade().is_none(), "the load's resolutions outlive its last clone");
    }
}

const JS_URI: &str = "file:///home/projects/TS/p2/index.js";
const JS_FILE: &str = "/home/projects/TS/p2/index.js";
const JS_TEXT: &str = "/** @type {number} */\nexport const x = 1;\nconst y = ;\n";

child_test! {
    // A file version whose program is freed keeps what its `GoFile` borrows
    // from the parse: the parse diagnostics and the JSDoc cache of a JS
    // file. The edit makes a new version of index.js, so the old one is in
    // the freed program only.
    fn go_file_of_freed_program_reads_diagnostics_and_js_doc() {
        let session = bare_session(files(&[
            (
                "/home/projects/TS/p2/tsconfig.json",
                r#"{"compilerOptions": {"allowJs": true, "checkJs": true}}"#,
            ),
            (JS_FILE, JS_TEXT),
        ]));
        open_kind(&session, JS_URI, JS_TEXT, lsproto::LanguageKind::JAVA_SCRIPT);
        let (freed, root, statement) = {
            let p = program(&session, JS_URI);
            let root = p.get_source_file(JS_FILE).expect("index.js is in the program").root;
            (Rc::downgrade(&p), root, root.statements().get(0))
        };
        let diagnostics = |root: ts_goport::core::Node| -> Vec<(i32, i32, i32)> {
            source_file_info(root)
                .diagnostics
                .iter()
                .map(|d| (d.code, d.pos, d.end))
                .collect()
        };
        let before = diagnostics(root);
        assert!(!before.is_empty(), "index.js has a parse error");
        assert_eq!(statement.js_doc(root).len(), 1);

        edit(&session, JS_URI, 2, (1, 17), (1, 18), "2");
        let live = program(&session, JS_URI);
        session.wait_for_background_tasks();
        assert!(freed.upgrade().is_none(), "the released program is not freed");
        assert_ne!(
            live.get_source_file(JS_FILE).expect("index.js is in the program").root,
            root,
            "the edit makes a new version of index.js"
        );

        let _program = ls_program::enter(&live);
        assert_eq!(diagnostics(root), before);
        assert_eq!(statement.js_doc(root).len(), 1);
    }
}

child_test! {
    // Files that import each other make the parse tasks of a load an `Rc`
    // cycle: a task holds its sub tasks, and a sub task of a file that is
    // already queued holds the task that loaded it. The loader takes these
    // links out when it is done, so a freed load keeps no parse task. The
    // probe is the include reasons, which the tasks and the program share.
    fn parse_tasks_of_a_freed_load_are_freed() {
        let session = bare_session(files(&[
            ("/home/projects/TS/p1/tsconfig.json", "{}"),
            ("/home/projects/TS/p1/index.ts", INDEX_TEXT),
            (
                "/home/projects/TS/p1/a.ts",
                "import { b } from './b';\nexport const a = 1;\nexport const c = b;",
            ),
            ("/home/projects/TS/p1/b.ts", "import { a } from './a';\nexport const b = a;"),
        ]));
        open(&session, INDEX_URI, INDEX_TEXT);
        let (load, reasons) = {
            let p = program(&session, INDEX_URI);
            let reasons: Vec<_> =
                p.get_include_reasons().values().flatten().map(Rc::downgrade).collect();
            (Rc::downgrade(&p), reasons)
        };
        assert!(reasons.len() >= 3, "index.ts, a.ts and b.ts have include reasons");

        import_edit(&session, 2);
        assert!(load.upgrade().is_none(), "the released load is not freed");
        let kept = reasons.iter().filter(|reason| reason.upgrade().is_some()).count();
        assert_eq!(kept, 0, "the freed load keeps {kept} of {} include reasons", reasons.len());
    }
}
