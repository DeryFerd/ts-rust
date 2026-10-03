//! Port-only tests of API requests on input that Go does not expect
//! (optapifuzz1). Go panics, and the API answers the panic text; the port
//! must panic at the same request with the same text.
//!
//! PORT: the tests call the session handlers directly, as the Go session
//! tests do, and catch the panic that the server would turn into the
//! `panic: <text>` answer (`handle_batch_request`, `ipc::conn`).

use std::panic::AssertUnwindSafe;
use std::rc::Rc;

use ts_goport::api::{
    self, CheckerNodeParams, CheckerSymbolParams, CheckerTypeParams, CreateSnapshotParams,
    GetCompletionsAtPositionParams, GetContextualTypeForArgumentParams, GetContextualTypeParams,
    GetDefaultProjectForFileParams, GetSymbolAtPositionParams, GetTypeAtPositionParams,
    GetTypeFromTypeNodeParams, GetTypePropertyParams, NodeHandle,
    SignatureToSignatureDeclarationParams, SnapshotID, SnapshotRequestChangesParams,
    TypeToTypeNodeParams,
};
use ts_goport::astdata::SyntaxKind;
use ts_goport::flags::ScriptKind;
use ts_goport::frontend::parser::{self, SourceFileParseOptions};
use ts_goport::frontend::tspath::Path;
use ts_goport::gostd::context::Context;
use ts_goport::{program, project};

use super::api_util::{doc, nil_error};
use super::projecttestutil::{self, files};
use super::util::bg;

/// Go's runtime text for a nil pointer dereference.
const NIL_DEREFERENCE: &str = "runtime error: invalid memory address or nil pointer dereference";

/// An API session with a snapshot that has `file` open, and its project.
struct Api {
    project_session: Rc<project::Session>,
    session: Rc<api::Session>,
    ctx: Context,
    snapshot: SnapshotID,
    project: project::ID,
}

impl Api {
    fn new(entries: &[(&str, &str)], file: &str) -> Self {
        let (project_session, _) = projecttestutil::setup(files(entries));
        let session = api::new_lsp_session(project_session.clone(), None);
        let ctx = bg();
        let snapshot = nil_error(session.handle_create_snapshot(
            &ctx,
            &CreateSnapshotParams {
                snapshot_request_changes_params: SnapshotRequestChangesParams {
                    open_files: Some(vec![doc(file)]),
                    ..Default::default()
                },
                ..Default::default()
            },
        ))
        .snapshot;
        let project = nil_error(session.handle_get_default_project_for_file(
            &ctx,
            &GetDefaultProjectForFileParams {
                snapshot,
                file: doc(file),
            },
        ))
        .expect("a default project")
        .id;
        Self {
            project_session,
            session,
            ctx,
            snapshot,
            project,
        }
    }

    /// The handle of the SourceFile node of `file`: index 1 of its node
    /// index table.
    fn source_file_handle(file: &str) -> NodeHandle {
        NodeHandle(format!("1.0.{file}"))
    }

    fn node_params(&self, location: NodeHandle) -> CheckerNodeParams {
        CheckerNodeParams {
            snapshot: self.snapshot,
            project: self.project.clone(),
            location,
        }
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

const A_TS: &str = "/home/projects/p/a.ts";
const A_TEXT: &str = "export const a = 1;\nexport function f(x: number) { return x; }\nf(1);\n";

fn api_a() -> Api {
    Api::new(
        &[("/home/projects/p/tsconfig.json", "{}"), (A_TS, A_TEXT)],
        A_TS,
    )
}

/// The id of the signature of `f` in `A_TEXT`, after `before` ran.
fn signature_id_of_f(before: impl FnOnce(&Api)) -> String {
    let api = api_a();
    before(&api);
    let f = nil_error(api.session.handle_get_symbol_at_position(
        &api.ctx,
        &GetSymbolAtPositionParams {
            snapshot: api.snapshot,
            project: api.project.clone(),
            file: doc(A_TS),
            position: A_TEXT.find("f(").expect("f") as u32,
        },
    ))
    .expect("the symbol f");
    let declaration = f.declarations[0].clone();
    let signature = nil_error(
        api.session
            .handle_get_signature_from_declaration(&api.ctx, &api.node_params(declaration)),
    )
    .expect("the signature of f");
    api.close();
    format!("{:?}", signature.id)
}

child_test! {
    // optapifuzz1 E1 (d030): Go `declaration.Parameters()` dereferences nil
    // on a node that is not function-like (checker.go:20192). The port read
    // the nil list as empty and made and registered a signature, so the
    // next signature had another id.
    fn get_signature_from_declaration_of_a_node_that_is_not_function_like() {
        let fresh = signature_id_of_f(|_| {});
        let after_panic = signature_id_of_f(|api| {
            let text = go_panic_text(|| {
                api.session.handle_get_signature_from_declaration(
                    &api.ctx,
                    &api.node_params(Api::source_file_handle(A_TS)),
                )
            });
            assert_eq!(text, NIL_DEREFERENCE);
        });
        assert_eq!(after_panic, fresh);
    }
}

child_test! {
    // optapifuzz1 E2 (d026): from the SourceFile, Go's walk in
    // getConditionalFlowTypeOfType reads the nil parent of the SourceFile
    // (checker.go:25424). The port's shortcut for a store with no
    // conditional or mapped type skipped the walk and answered a type.
    fn get_type_from_type_node_of_the_source_file() {
        let api = api_a();
        let text = go_panic_text(|| {
            api.session.handle_get_type_from_type_node(
                &api.ctx,
                &GetTypeFromTypeNodeParams {
                    snapshot: api.snapshot,
                    project: api.project.clone(),
                    location: Api::source_file_handle(A_TS),
                },
            )
        });
        assert_eq!(text, NIL_DEREFERENCE);
        api.close();
    }
}

child_test! {
    // optapifuzz1 E3 (d035): typeToTypeNode with no location builds an
    // import type into node_modules under nodenext, and Go reads the file
    // name of the nil context file (nodebuilderimpl.go:686,
    // compiler/program.go:1744). The port read nil as a file and answered
    // null.
    fn type_to_type_node_of_a_node_modules_type_with_no_location() {
        const DTS: &str = "/home/projects/p/node_modules/pkg/index.d.cts";
        let api = Api::new(
            &[
                (
                    "/home/projects/p/tsconfig.json",
                    r#"{"compilerOptions": {"module": "nodenext", "noEmit": true, "strict": true}, "files": ["node_modules/pkg/index.d.cts", "node_modules/pkg/lib/index.d.ts", "index.ts"]}"#,
                ),
                (
                    "/home/projects/p/node_modules/pkg/package.json",
                    r#"{"name": "pkg", "version": "1.0.0", "main": "index.cjs"}"#,
                ),
                (
                    DTS,
                    "declare const pkg: typeof import(\"./lib/index.js\");\nexport = pkg;\n",
                ),
                (
                    "/home/projects/p/node_modules/pkg/lib/index.d.ts",
                    "declare const configs: { a: number };\nexport { configs };\n",
                ),
                ("/home/projects/p/index.ts", "import * as pkg from 'pkg';\npkg;\n"),
            ],
            "/home/projects/p/index.ts",
        );
        let t = nil_error(api.session.handle_get_type_at_position(
            &api.ctx,
            &GetTypeAtPositionParams {
                snapshot: api.snapshot,
                project: api.project.clone(),
                file: doc(DTS),
                position: 15,
            },
        ))
        .expect("the type of pkg");
        let text = go_panic_text(|| {
            api.session.handle_type_to_type_node(
                &api.ctx,
                &TypeToTypeNodeParams {
                    snapshot: api.snapshot,
                    project: api.project.clone(),
                    type_: t.id,
                    location: NodeHandle(String::new()),
                    flags: 0,
                },
            )
        });
        assert_eq!(text, NIL_DEREFERENCE);
        api.close();
    }
}

/// The handle of the first node of `kind` in `A_TEXT`: its index in the
/// node index table, which depends only on the tree.
fn a_handle_of(kind: SyntaxKind) -> NodeHandle {
    let file = Rc::new(parser::parse_source_file(
        &SourceFileParseOptions {
            file_name: "/index-table/a.ts".to_string(),
            path: Path("/index-table/a.ts".to_string()),
            ..Default::default()
        },
        A_TEXT,
        ScriptKind::TS,
    ));
    program::note_parsed_source_file(&file);
    let table = api::encoder::build_node_index_table(file.root);
    let index = table
        .nodes
        .iter()
        .position(|node| node.is_some() && node.kind() == kind)
        .unwrap_or_else(|| panic!("no {kind:?} in A_TEXT"));
    NodeHandle(format!("{index}.0.{A_TS}"))
}

impl Api {
    fn type_at(&self, position: u32) -> api::TypeID {
        nil_error(self.session.handle_get_type_at_position(
            &self.ctx,
            &GetTypeAtPositionParams {
                snapshot: self.snapshot,
                project: self.project.clone(),
                file: doc(A_TS),
                position,
            },
        ))
        .expect("a type")
        .id
    }

    fn symbol_at(&self, position: u32) -> api::SymbolResponse {
        nil_error(self.session.handle_get_symbol_at_position(
            &self.ctx,
            &GetSymbolAtPositionParams {
                snapshot: self.snapshot,
                project: self.project.clone(),
                file: doc(A_TS),
                position,
            },
        ))
        .expect("a symbol")
    }
}

child_test! {
    // optapifuzz1 D: a type getter on the wrong type kind. A cast to a
    // concrete struct (`t.data.(*ConditionalType)`, types.go:709-727) panics
    // with Go's runtime text. A cast to an embedded struct returns nil, and
    // the caller dereferences it (checker.go:22285 for getTypeArguments).
    // The port panicked with its own text for both.
    fn type_getters_on_the_wrong_type_kind() {
        let api = api_a();
        // The literal type `1` of `a`.
        let t = api.type_at(13);
        let text = go_panic_text(|| {
            api.session.handle_get_check_type_of_type(
                &api.ctx,
                &GetTypePropertyParams {
                    snapshot: api.snapshot,
                    project: api.project.clone(),
                    type_: t,
                },
            )
        });
        assert_eq!(
            text,
            "interface conversion: checker.TypeData is *checker.LiteralType, not *checker.ConditionalType"
        );
        let text = go_panic_text(|| {
            api.session.handle_get_type_arguments(
                &api.ctx,
                &CheckerTypeParams {
                    snapshot: api.snapshot,
                    project: api.project.clone(),
                    type_: t,
                },
            )
        });
        assert_eq!(text, NIL_DEREFERENCE);
        api.close();
    }
}

child_test! {
    // optapifuzz1 F: other requests where Go panics, each with Go's text.
    // F1: getContextualType reads the nil parent of the SourceFile
    // (checker.go:29839). F2: getImmediateAliasedSymbol asserts an alias
    // (checker.go:2197); the port's assert was off in release. F3: argument
    // index -1 (relater.go:1801). F4: a position of 2^31, which Go keeps as
    // an int, past the text in the JSDoc snippet slice (jsdoc_snippet.go:77);
    // the port wrapped it to a negative i32. F5: a kind that is no syntax
    // kind (nodebuilderimpl.go:1972).
    fn misuse_panics_with_go_texts() {
        let api = api_a();
        let text = go_panic_text(|| {
            api.session.handle_get_contextual_type(
                &api.ctx,
                &GetContextualTypeParams {
                    snapshot: api.snapshot,
                    project: api.project.clone(),
                    location: Api::source_file_handle(A_TS),
                },
            )
        });
        assert_eq!(text, NIL_DEREFERENCE, "F1");

        let a = api.symbol_at(13);
        let text = go_panic_text(|| {
            api.session.handle_get_immediate_aliased_symbol(
                &api.ctx,
                &CheckerSymbolParams {
                    snapshot: api.snapshot,
                    project: api.project.clone(),
                    symbol: a.id,
                },
            )
        });
        assert_eq!(text, "Debug failure. False expression: Should only get Alias here.", "F2");

        let text = go_panic_text(|| {
            api.session.handle_get_contextual_type_for_argument(
                &api.ctx,
                &GetContextualTypeForArgumentParams {
                    snapshot: api.snapshot,
                    project: api.project.clone(),
                    location: a_handle_of(SyntaxKind::CallExpression),
                    index: -1,
                },
            )
        });
        assert_eq!(text, "runtime error: index out of range [-1]", "F3");

        let text = go_panic_text(|| {
            api.session.handle_get_completions_at_position(
                &api.ctx,
                &GetCompletionsAtPositionParams {
                    snapshot: api.snapshot,
                    project: api.project.clone(),
                    file: doc(A_TS),
                    position: 1 << 31,
                    ..Default::default()
                },
            )
        });
        assert_eq!(
            text,
            format!(
                "runtime error: slice bounds out of range [:2147483648] with length {}",
                A_TEXT.len()
            ),
            "F4"
        );

        let f = api.symbol_at(A_TEXT.find("f(").expect("f") as u32);
        let signature = nil_error(api.session.handle_get_signature_from_declaration(
            &api.ctx,
            &api.node_params(f.declarations[0].clone()),
        ))
        .expect("the signature of f");
        let text = go_panic_text(|| {
            api.session.handle_signature_to_signature_declaration(
                &api.ctx,
                &SignatureToSignatureDeclarationParams {
                    snapshot: api.snapshot,
                    project: api.project.clone(),
                    signature: signature.id,
                    kind: 99999,
                    location: NodeHandle(String::new()),
                    flags: 0,
                },
            )
        });
        assert_eq!(text, "Unhandled kind in signatureToSignatureDeclarationHelper", "F5");
        api.close();
    }
}

// optapifuzz1 B: a JSON error names Go's type with its package
// (project/project.go:44 `project.SyntheticProjectID`, as in "json: cannot
// unmarshal into Go project.SyntheticProjectID within ..."). The port named
// it without the package.
#[test]
fn project_types_have_go_package_names() {
    use ts_goport::frontend::json_ext::go_type_name;
    assert_eq!(
        go_type_name::<project::SyntheticProjectID>(),
        "project.SyntheticProjectID"
    );
    assert_eq!(go_type_name::<project::ID>(), "project.ID");
}
