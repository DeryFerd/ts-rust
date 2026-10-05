//! Port-only tests of a symbol of project A used in a request on project B
//! (editfuzz4 triage G1, apisym1). Go hands the `*ast.Symbol` to B's checker
//! (api/session.go:2439 handleGetTypeOfSymbol), which reads the bound
//! declarations of any file. A port checker reads only the binder lineage
//! ids of its copy. B's API checker copies the lineage when it is made
//! (`ls_program::new_api_checker`), so it gets Go's answer for a file version
//! bound before that. When B's API checker is older than the version, the
//! port answers an `unported` panic (`api::checker_symbol`), not a wrong type,
//! and B's next answers do not change.
//!
//! PORT: the tests call the session handlers directly and catch the panic
//! that the server turns into the `panic: <text>` answer, as
//! `api_session_misuse_test` does.

use std::panic::AssertUnwindSafe;
use std::rc::Rc;

use ts_goport::api::requestfilesystem::{Kind, RequestFileSystem};
use ts_goport::api::{
    self, CreateSnapshotParams, EnsurePrograms, GetSymbolAtPositionParams, GetTypeOfSymbolParams,
    SnapshotID, SnapshotRequestChangesParams, SymbolID, TypeToTypeNodeParams, UpdateSnapshotParams,
};
use ts_goport::gostd::Context;
use ts_goport::project;

use super::api_util::{doc, nil_error, project_program, snapshot_of};
use super::projecttestutil::{self, files};
use super::requestfilesystem_test::files as request_files;
use super::util::{bg, text};

const A_CONFIG: &str = "/home/projects/p/tsconfig.a.json";
const B_CONFIG: &str = "/home/projects/p/tsconfig.b.json";
const X_TS: &str = "/home/projects/p/x.ts";
const B_TS: &str = "/home/projects/p/b.ts";
const X_TEXT: &str = "export const f = <T,>(x: T, y: string) => x;\n";
/// The edit that `layer` gives x.ts. `f` keeps its type.
const X_EDITED: &str = "// edited\nexport const f = <T,>(x: T, y: string) => x;\n";
const B_TEXT: &str = "export const g = (n: number) => n;\n";
const F_TYPE: &str = "<T>(x: T, y: string) => T";
const G_TYPE: &str = "(n: number) => number";

/// An API session with A (x.ts) and B (b.ts) open: two projects that share
/// no file. B never reads x.ts, so an edit of x.ts keeps B's program and its
/// API checker.
struct Api {
    project_session: Rc<project::Session>,
    session: Rc<api::Session>,
    ctx: Context,
    snapshot: SnapshotID,
    a: project::ID,
    b: project::ID,
}

impl Api {
    fn new() -> Self {
        let options = r#"{ "compilerOptions": { "noLib": true }, "files": "#;
        let (project_session, _) = projecttestutil::setup(files(&[
            (A_CONFIG, &format!(r#"{options}["x.ts"] }}"#)),
            (B_CONFIG, &format!(r#"{options}["b.ts"] }}"#)),
            (X_TS, X_TEXT),
            (B_TS, B_TEXT),
        ]));
        let session = api::new_lsp_session(project_session.clone(), None);
        let ctx = bg();
        let created = nil_error(session.handle_create_snapshot(
            &ctx,
            &CreateSnapshotParams {
                snapshot_request_changes_params: SnapshotRequestChangesParams {
                    open_projects: vec![doc(A_CONFIG), doc(B_CONFIG)],
                    ..Default::default()
                },
                ..Default::default()
            },
        ));
        let id = |config: &str| {
            created
                .projects
                .iter()
                .find(|p| p.config_file_name == config)
                .unwrap_or_else(|| panic!("no project {config}"))
                .id
                .clone()
        };
        let (a, b) = (id(A_CONFIG), id(B_CONFIG));
        Self {
            project_session,
            session,
            ctx,
            snapshot: created.snapshot,
            a,
            b,
        }
    }

    /// Go `updateSnapshot` with a layer that gives x.ts the text `X_EDITED`
    /// and `ensurePrograms.all`. A gets a new program with a new x.ts
    /// version; B keeps its program.
    fn edit_x(&mut self) {
        let b_before = project_program(&snapshot_of(&self.session, self.snapshot), &self.b.0);
        self.snapshot = nil_error(self.session.handle_update_snapshot(
            &self.ctx,
            &UpdateSnapshotParams {
                snapshot: self.snapshot,
                changes: Some(CreateSnapshotParams {
                    snapshot_request_changes_params: SnapshotRequestChangesParams {
                        ensure_programs: Some(EnsurePrograms {
                            all: true,
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                    file_system: Some(RequestFileSystem {
                        kind: Kind::LAYER,
                        files: request_files(&[(X_TS, X_EDITED)]),
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
            },
        ))
        .snapshot;
        let snapshot = snapshot_of(&self.session, self.snapshot);
        assert_eq!(text(&project_program(&snapshot, &self.a.0), X_TS), X_EDITED);
        assert!(Rc::ptr_eq(
            &project_program(&snapshot, &self.b.0),
            &b_before
        ));
    }

    /// The symbol at the first `name` in `file`, on `project`.
    fn symbol(&self, project: &project::ID, file: &str, text: &str, name: &str) -> SymbolID {
        nil_error(self.session.handle_get_symbol_at_position(
            &self.ctx,
            &GetSymbolAtPositionParams {
                snapshot: self.snapshot,
                project: project.clone(),
                file: doc(file),
                position: text.find(name).expect("the name") as u32,
            },
        ))
        .expect("a symbol")
        .id
    }

    /// Go `typeToString(getTypeOfSymbol(symbol))` on `project`.
    fn type_text(&self, project: &project::ID, symbol: SymbolID) -> String {
        let t = nil_error(self.session.handle_get_type_of_symbol(
            &self.ctx,
            &GetTypeOfSymbolParams {
                snapshot: self.snapshot,
                project: project.clone(),
                symbol,
            },
        ))
        .expect("a type");
        let text = nil_error(self.session.handle_type_to_string(
            &self.ctx,
            &TypeToTypeNodeParams {
                snapshot: self.snapshot,
                project: project.clone(),
                type_: t.id,
                location: Default::default(),
                flags: 0,
            },
        ))
        .expect("a text");
        text.downcast_ref::<String>().expect("a string").clone()
    }

    fn close(self) {
        self.session.close();
        self.project_session.close();
    }
}

/// The text of the Go panic of `f`.
fn go_panic_text<R>(f: impl FnOnce() -> R) -> String {
    match std::panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(_) => panic!("no panic"),
        Err(payload) => ts_goport::ipc::conn::recovered_value(payload.as_ref()),
    }
}

child_test! {
    // r-xc-min, g1-b-order: B's program bound before the x.ts version that A
    // reads, and B's API checker is made after it. The port read the
    // declarations of `f` past B's copy of the lineage and panicked
    // (index out of bounds), then answered `any`. Go answers the type.
    fn symbol_of_later_file_version_on_new_api_checker() {
        let mut api = Api::new();
        api.edit_x();
        let f = api.symbol(&api.a, X_TS, X_EDITED, "f =");
        assert_eq!(api.type_text(&api.b, f), F_TYPE);
        assert_eq!(api.type_text(&api.b, f), F_TYPE);
        assert_eq!(api.type_text(&api.a, f), F_TYPE);
        api.close();
    }
}

child_test! {
    // g1-b-alias, g1-z-alias3: B's API checker exists before the edit, so
    // its copy of the lineage lacks the new x.ts version. Go answers the
    // type (part B, on hold). The port answers an `unported` panic each
    // time, and B and A answer as before.
    fn symbol_of_later_file_version_on_older_api_checker() {
        let mut api = Api::new();
        let g = api.symbol(&api.b, B_TS, B_TEXT, "g =");
        assert_eq!(api.type_text(&api.b, g), G_TYPE);
        api.edit_x();
        let f = api.symbol(&api.a, X_TS, X_EDITED, "f =");
        for _ in 0..2 {
            assert_eq!(
                go_panic_text(|| api.type_text(&api.b, f)),
                "unported Go code: api: symbol of a file bound after the checker was made"
            );
        }
        let g = api.symbol(&api.b, B_TS, B_TEXT, "g =");
        assert_eq!(api.type_text(&api.b, g), G_TYPE);
        assert_eq!(api.type_text(&api.a, f), F_TYPE);
        api.close();
    }
}
