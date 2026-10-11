//! Port-only tests of the Effect refactor provider (`effect::ls::refactors`,
//! Effect-TS/tsgo patch 011; lane effectE9a): the refactors that need no
//! Effect types, in Go order, with and without the plugin.
//!
//! The refactors that read Effect types run through
//! `scripts/effect/ls-cases.mjs` on the Go baseline cases with the real
//! package.

use std::rc::Rc;

use ts_goport::ls::LanguageService;
use ts_goport::lsp::lsproto;
use ts_goport::project::Session;

use super::projecttestutil::{self, files};
use super::util::*;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const MAIN: &str = "/home/projects/p/main.ts";
const MAIN_URI: &str = "file:///home/projects/p/main.ts";

// `test1` is at 0:6-0:11, `f` at 1:9-1:10.
const MAIN_TEXT: &str = r#"const test1 = 1
function f(a: number) {
  return a + 1
}
"#;

const PLUGIN: &str = r#"{"name":"@effect/language-service"}"#;

/// A session on the project with `plugin` as the plugins list (`""`: no
/// plugin) and main.ts open, and its language service for main.ts.
fn service(plugin: &str) -> (Rc<Session>, LanguageService) {
    let config = format!(
        r#"{{"compilerOptions":{{"strict":true,"target":"ESNext","module":"ESNext","plugins":[{plugin}]}}}}"#
    );
    let (session, _) = projecttestutil::setup(files(&[(CONFIG, &config), (MAIN, MAIN_TEXT)]));
    open(&session, MAIN_URI, MAIN_TEXT);
    let service = session
        .get_language_service(&projecttestutil::with_request_id(&bg()), &uri(MAIN_URI))
        .unwrap_or_else(|err| panic!("{}", err.error()));
    (session, service)
}

fn pos(line: u32, character: u32) -> lsproto::Position {
    lsproto::Position { line, character }
}

fn range(line: u32, start: u32, end: u32) -> lsproto::Range {
    lsproto::Range {
        start: pos(line, start),
        end: pos(line, end),
    }
}

type Action = (String, String, Vec<(lsproto::Range, String)>);

/// The code actions at `range` with the `only` filter `only` (None: no
/// filter, as the lightbulb asks), as `(title, kind, edits of main.ts)`.
fn code_actions(
    service: &LanguageService,
    range: lsproto::Range,
    only: Option<&[&'static str]>,
) -> Vec<Action> {
    let only = only.map(|kinds| {
        kinds
            .iter()
            .map(|&kind| lsproto::CodeActionKind(kind.into()))
            .collect()
    });
    let response = service
        .provide_code_actions(
            &projecttestutil::with_request_id(&bg()),
            &lsproto::CodeActionParams {
                text_document: lsproto::TextDocumentIdentifier { uri: uri(MAIN_URI) },
                range,
                context: Some(lsproto::CodeActionContext {
                    only,
                    ..Default::default()
                }),
                ..Default::default()
            },
        )
        .unwrap_or_else(|err| panic!("{}", err.error()));
    response
        .command_or_code_action_array
        .unwrap_or_default()
        .into_iter()
        .map(|action| {
            let action = action.code_action.expect("a code action");
            let mut changes = action
                .edit
                .and_then(|edit| edit.changes)
                .unwrap_or_default();
            assert!(changes.len() <= 1, "edits of one file: {changes:?}");
            let edits = changes
                .shift_remove(&uri(MAIN_URI))
                .unwrap_or_default()
                .into_iter()
                .map(|edit| {
                    let edit = edit.expect("an edit");
                    (edit.range, edit.new_text)
                })
                .collect();
            let kind = action
                .kind
                .map(|kind| kind.0.into_owned())
                .unwrap_or_default();
            (action.title, kind, edits)
        })
        .collect()
}

fn action(title: &str, name: &str, edits: &[(lsproto::Range, &str)]) -> Action {
    (
        title.to_string(),
        format!("refactor.rewrite.effect.{name}"),
        edits
            .iter()
            .map(|(range, text)| (*range, text.to_string()))
            .collect(),
    )
}

child_test! {
    // A selection of a const name gives wrapWithPipe, toggleTypeAnnotation
    // and toggleLazyConst, in Go's `refactors.All` order. A cursor on a
    // function name gives toggleReturnTypeAnnotation and functionToArrow.
    // The edits are the Go edits: text inserts, and for functionToArrow the
    // printed `const` statement in place of the declaration.
    fn refactors_follow_go_order_with_the_plugin() {
        let (_session, service) = service(PLUGIN);
        let on_name = vec![
            action(
                "Wrap with pipe",
                "wrapWithPipe",
                &[(range(0, 6, 6), "pipe("), (range(0, 11, 11), ")")],
            ),
            action(
                "Toggle type annotation",
                "toggleTypeAnnotation",
                &[(range(0, 11, 11), ": 1")],
            ),
            action("Toggle lazy const", "toggleLazyConst", &[(range(0, 13, 13), " () =>")]),
        ];
        assert_eq!(code_actions(&service, range(0, 6, 11), None), on_name);
        assert_eq!(code_actions(&service, range(0, 6, 11), Some(&["refactor"])), on_name);

        let on_function = vec![
            action(
                "Toggle return type annotation",
                "toggleReturnTypeAnnotation",
                &[(range(1, 21, 21), ": number")],
            ),
            action(
                "Convert to arrow",
                "functionToArrow",
                &[(
                    lsproto::Range { start: pos(1, 0), end: pos(3, 1) },
                    "const f = (a: number) => a + 1;",
                )],
            ),
        ];
        assert_eq!(code_actions(&service, range(1, 9, 9), Some(&["refactor"])), on_function);

        // A quick fix filter runs no refactor.
        assert_eq!(code_actions(&service, range(0, 6, 11), Some(&["quickfix"])), vec![]);
    }
}

child_test! {
    // Without the plugin, or with the plugin option `refactors: false`, the
    // provider gives no refactor.
    fn no_refactors_without_the_plugin_or_when_off() {
        for plugin in ["", r#"{"name":"@effect/language-service","refactors":false}"#] {
            let (_session, service) = service(plugin);
            assert_eq!(code_actions(&service, range(0, 6, 11), None), vec![], "{plugin}");
            assert_eq!(code_actions(&service, range(1, 9, 9), None), vec![], "{plugin}");
        }
    }
}
