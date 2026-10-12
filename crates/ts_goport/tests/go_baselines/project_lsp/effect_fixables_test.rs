//! Port-only tests of the Effect quick fix provider (`effect::ls::fixables`,
//! Effect-TS/tsgo patch 011; lane effectE4): the disable actions on a
//! stand-in Effect diagnostic, with and without the plugin, and in a
//! standalone API process.
//!
//! Go writes "skipped by default" for the disable actions in its quick fix
//! baselines, so their edits are tested here. The 12 rule fixes run through
//! `scripts/effect/ls-cases.mjs` on the Go cases with the real package.

use std::rc::Rc;

use ts_goport::effect::rulerunner;
use ts_goport::ls::LanguageService;
use ts_goport::lsp::lsproto;
use ts_goport::project::Session;

use super::projecttestutil::{self, files};
use super::util::*;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const MAIN: &str = "/home/projects/p/main.ts";
const MAIN_URI: &str = "file:///home/projects/p/main.ts";

// Line 4 is `    return myEffect` (4 spaces), `myEffect` at characters 11-19.
const MAIN_TEXT: &str = r#"import { Effect } from "effect"
export declare const myEffect: Effect.Effect<string, Error, never>
export function f() {
  if (myEffect) {
    return myEffect
  }
}
"#;

const EFFECT_PACKAGE_JSON: &str = r#"{"name":"effect","version":"3.0.0","types":"./index.d.ts"}"#;
const EFFECT_INDEX: &str = "export * as Effect from \"./Effect.js\"\n";
const EFFECT_MODULE: &str = r#"export declare const EffectTypeId: unique symbol
export interface Variance<A, E, R> {
  readonly _A: (_: never) => A
  readonly _E: (_: never) => E
  readonly _R: (_: never) => R
}
export interface Effect<A, E = never, R = never> {
  readonly [EffectTypeId]: Variance<A, E, R>
}
"#;

const PLUGIN: &str = r#"{"name":"@effect/language-service"}"#;

/// TS377100, the code of the `flatMapToMap` rule.
const FLAT_MAP_TO_MAP: i32 = 377100;

/// A session on the project with `plugin` as the plugins list (`""`: no
/// plugin) and main.ts open, and its language service for main.ts.
fn service(plugin: &str) -> (Rc<Session>, LanguageService) {
    let config = format!(
        r#"{{"compilerOptions":{{"strict":true,"target":"ESNext","module":"ESNext","moduleResolution":"bundler","plugins":[{plugin}]}}}}"#
    );
    let (session, _) = projecttestutil::setup(files(&[
        (CONFIG, &config),
        (MAIN, MAIN_TEXT),
        (
            "/home/projects/p/node_modules/effect/package.json",
            EFFECT_PACKAGE_JSON,
        ),
        (
            "/home/projects/p/node_modules/effect/index.d.ts",
            EFFECT_INDEX,
        ),
        (
            "/home/projects/p/node_modules/effect/Effect.d.ts",
            EFFECT_MODULE,
        ),
    ]));
    open(&session, MAIN_URI, MAIN_TEXT);
    let service = session
        .get_language_service(&projecttestutil::with_request_id(&bg()), &uri(MAIN_URI))
        .unwrap_or_else(|err| panic!("{}", err.error()));
    (session, service)
}

fn range(line: u32, start: u32, end: u32) -> lsproto::Range {
    lsproto::Range {
        start: lsproto::Position {
            line,
            character: start,
        },
        end: lsproto::Position {
            line,
            character: end,
        },
    }
}

/// A stand-in for an Effect diagnostic with `code` at `range`.
fn diagnostic(code: i32, range: lsproto::Range) -> lsproto::Diagnostic {
    lsproto::Diagnostic {
        range,
        code: Some(lsproto::IntegerOrString {
            integer: Some(code),
            string: None,
        }),
        message: lsproto::StringOrMarkupContent {
            string: Some("stand-in".to_string()),
            markup_content: None,
        },
        ..Default::default()
    }
}

/// The quick fixes for `diagnostics` (request range: the first one), as
/// `(title, kind, edits of main.ts)`.
fn quick_fixes(
    service: &LanguageService,
    diagnostics: &[lsproto::Diagnostic],
) -> Vec<(String, String, Vec<(lsproto::Range, String)>)> {
    let response = service
        .provide_code_actions(
            &projecttestutil::with_request_id(&bg()),
            &lsproto::CodeActionParams {
                text_document: lsproto::TextDocumentIdentifier { uri: uri(MAIN_URI) },
                range: diagnostics[0].range,
                context: Some(lsproto::CodeActionContext {
                    diagnostics: diagnostics.iter().cloned().map(Some).collect(),
                    only: Some(vec![lsproto::CodeActionKind::QUICK_FIX]),
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

child_test! {
    // The disable actions on an indented line: the line action inserts the
    // indented `@effect-diagnostics-next-line` comment at the start of the
    // line, the file action the `@effect-diagnostics` comment at 0:0. Two
    // diagnostics of one rule on one line give each action once.
    fn disable_actions_insert_the_directive_comments() {
        let (_session, service) = service(PLUGIN);
        let expected = vec![
            (
                "Disable flatMapToMap for this line".to_string(),
                "quickfix".to_string(),
                vec![(
                    range(4, 0, 0),
                    "    // @effect-diagnostics-next-line flatMapToMap:off\n".to_string(),
                )],
            ),
            (
                "Disable flatMapToMap for entire file".to_string(),
                "quickfix".to_string(),
                vec![(
                    range(0, 0, 0),
                    "/** @effect-diagnostics flatMapToMap:off */\n".to_string(),
                )],
            ),
        ];
        let one = diagnostic(FLAT_MAP_TO_MAP, range(4, 11, 19));
        assert_eq!(quick_fixes(&service, std::slice::from_ref(&one)), expected);
        let two = [one, diagnostic(FLAT_MAP_TO_MAP, range(4, 4, 10))];
        assert_eq!(quick_fixes(&service, &two), expected);

        // A code that no Effect rule has gets no Effect action.
        assert_eq!(quick_fixes(&service, &[diagnostic(377999, range(4, 11, 19))]), vec![]);
    }
}

child_test! {
    // Without the plugin the provider gives no action for an Effect code.
    fn no_effect_actions_without_the_plugin() {
        let (_session, service) = service("");
        assert_eq!(
            quick_fixes(&service, &[diagnostic(FLAT_MAP_TO_MAP, range(4, 11, 19))]),
            vec![]
        );
    }
}

child_test! {
    env &[("TSGO_EFFECT_API", "0")];
    // A standalone API process without TSGO_EFFECT_API=1 has the Effect
    // actions off, as it has the rules off (`rulerunner::enabled_options`).
    fn no_effect_actions_in_a_standalone_api_process() {
        rulerunner::set_api_process();
        let (_session, service) = service(PLUGIN);
        assert_eq!(
            quick_fixes(&service, &[diagnostic(FLAT_MAP_TO_MAP, range(4, 11, 19))]),
            vec![]
        );
    }
}
