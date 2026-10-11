//! Port-only tests of the 4 async/await refactors of the Effect refactor
//! provider (`effect::ls::refactors`, Effect-TS/tsgo patch 011; lane
//! effectE9b). They need no Effect types: the module names come from the
//! imports, so the project has no Effect package.
//!
//! effectGenToFn reads Effect types; it runs through
//! `scripts/effect/ls-cases.mjs` on the Go baseline cases with the real
//! package, as the other type-based refactors.

use std::rc::Rc;

use ts_goport::ls::LanguageService;
use ts_goport::lsp::lsproto;
use ts_goport::project::Session;

use super::projecttestutil::{self, files};
use super::util::*;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const MAIN: &str = "/home/projects/p/main.ts";
const MAIN_URI: &str = "file:///home/projects/p/main.ts";

// `load` is at 2:22-2:26, `Promise` at 5:39, `plain` at 6:9.
const MAIN_TEXT: &str = r#"import * as Eff from "effect/Effect"
import { Data as D } from "effect"
export async function load(id: string) {
  return await fetch(id)
}
const run = async (n: number) => await Promise.resolve(n)
function plain() { return 1 }
"#;

const CONFIG_TEXT: &str = r#"{"compilerOptions":{"strict":true,"target":"ESNext","module":"ESNext","plugins":[{"name":"@effect/language-service"}]}}"#;

/// A session on the project with the plugin and main.ts open, and its
/// language service for main.ts.
fn service() -> (Rc<Session>, LanguageService) {
    let (session, _) = projecttestutil::setup(files(&[(CONFIG, CONFIG_TEXT), (MAIN, MAIN_TEXT)]));
    open(&session, MAIN_URI, MAIN_TEXT);
    let service = session
        .get_language_service(&projecttestutil::with_request_id(&bg()), &uri(MAIN_URI))
        .unwrap_or_else(|err| panic!("{}", err.error()));
    (session, service)
}

fn pos(line: u32, character: u32) -> lsproto::Position {
    lsproto::Position { line, character }
}

type Action = (String, String, Vec<(lsproto::Range, String)>);

/// The async/await refactor actions at the cursor `at` (no `only` filter, as
/// the lightbulb asks), in answer order, as `(title, kind, edits of main.ts)`.
fn async_await_actions(service: &LanguageService, at: lsproto::Position) -> Vec<Action> {
    let response = service
        .provide_code_actions(
            &projecttestutil::with_request_id(&bg()),
            &lsproto::CodeActionParams {
                text_document: lsproto::TextDocumentIdentifier { uri: uri(MAIN_URI) },
                range: lsproto::Range { start: at, end: at },
                context: Some(lsproto::CodeActionContext::default()),
                ..Default::default()
            },
        )
        .unwrap_or_else(|err| panic!("{}", err.error()));
    response
        .command_or_code_action_array
        .unwrap_or_default()
        .into_iter()
        .filter_map(|action| {
            let action = action.code_action.expect("a code action");
            let kind = action
                .kind
                .map(|kind| kind.0.into_owned())
                .unwrap_or_default();
            if !kind.starts_with("refactor.rewrite.effect.asyncAwaitTo") {
                return None;
            }
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
            Some((action.title, kind, edits))
        })
        .collect()
}

/// The 4 actions in Go's `refactors.All` order, each one edit of `range`
/// with the text of `texts` (gen, gen with failures, fn, fn with failures).
fn expected(range: lsproto::Range, texts: [&str; 4]) -> Vec<Action> {
    [
        ("Rewrite to Effect.gen", "asyncAwaitToGen"),
        (
            "Rewrite to Effect.gen with failures",
            "asyncAwaitToGenTryPromise",
        ),
        ("Rewrite to Effect.fn", "asyncAwaitToFn"),
        (
            "Rewrite to Effect.fn with failures",
            "asyncAwaitToFnTryPromise",
        ),
    ]
    .into_iter()
    .zip(texts)
    .map(|((title, name), text)| {
        (
            title.to_string(),
            format!("refactor.rewrite.effect.{name}"),
            vec![(range, text.to_string())],
        )
    })
    .collect()
}

child_test! {
    // A cursor in an async function declaration replaces the declaration; in
    // an async arrow, the variable statement around it (Go
    // replaceExpressionViaStatement). The failure variants put one exported
    // (as the function) error class per await before the top-level
    // statement, with the `Data` import alias, and the module names come
    // from the imports. A plain function gives none of the 4.
    fn async_await_refactors_follow_go() {
        let (_session, service) = service();

        let error1 = "class Error1 extends D.TaggedError(\"Error1\")<{\n    cause: unknown;\n}> {}\n\n";
        let load = lsproto::Range { start: pos(2, 0), end: pos(4, 1) };
        let gen_body = "export function load(id: string) {\n    return Eff.gen(function* () {\n        return yield* Eff.promise(() => fetch(id));\n    });\n}";
        let gen_try_body = "export function load(id: string) {\n    return Eff.gen(function* () {\n        return yield* Eff.tryPromise({ try: () => fetch(id), catch: cause => new Error1({ cause }) });\n    });\n}";
        let fn_body = "export const load = Eff.fn(\"load\")(function* (id: string) {\n    return yield* Eff.promise(() => fetch(id));\n});";
        let fn_try_body = "export const load = Eff.fn(\"load\")(function* (id: string) {\n    return yield* Eff.tryPromise({ try: () => fetch(id), catch: cause => new Error1({ cause }) });\n});";
        assert_eq!(
            async_await_actions(&service, pos(2, 22)),
            expected(
                load,
                [
                    gen_body,
                    &format!("export {error1}{gen_try_body}"),
                    fn_body,
                    &format!("export {error1}{fn_try_body}"),
                ],
            )
        );

        let run = lsproto::Range { start: pos(5, 0), end: pos(5, 57) };
        let gen_body = "const run = (n: number) => Eff.gen(function* () {\n    return yield* Eff.promise(() => Promise.resolve(n));\n});";
        let gen_try_body = "const run = (n: number) => Eff.gen(function* () {\n    return yield* Eff.tryPromise({ try: () => Promise.resolve(n), catch: cause => new Error1({ cause }) });\n});";
        let fn_body = "const run = Eff.fn(\"run\")(function* (n: number) {\n    return yield* Eff.promise(() => Promise.resolve(n));\n});";
        let fn_try_body = "const run = Eff.fn(\"run\")(function* (n: number) {\n    return yield* Eff.tryPromise({ try: () => Promise.resolve(n), catch: cause => new Error1({ cause }) });\n});";
        assert_eq!(
            async_await_actions(&service, pos(5, 39)),
            expected(
                run,
                [
                    gen_body,
                    &format!("{error1}{gen_try_body}"),
                    fn_body,
                    &format!("{error1}{fn_try_body}"),
                ],
            )
        );

        assert_eq!(async_await_actions(&service, pos(6, 9)), vec![]);
    }
}
