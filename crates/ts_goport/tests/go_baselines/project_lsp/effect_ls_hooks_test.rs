//! Port-only tests of the Effect language service hooks (`effect::ls`,
//! Effect-TS/tsgo patches 011, 012, 015 and 024; lane effectE2). Each hook
//! runs with the Effect plugin on and off. Without the plugin every hook
//! gives back its input. A standalone API process has the hooks off unless
//! `TSGO_EFFECT_API=1`. With completions on, the completion hook (patch 022)
//! adds Effect items, so its on and off checks are in
//! `effect_ls_completions_test.rs`.
//!
//! The project has a small stand-in for the `effect` package: an `Effect`
//! interface with the v3 variance struct, `succeed` and `gen`. That is enough
//! for the type parser to find Effect types and `Effect.gen` calls. The Go
//! cases with the real package (`internal/effecttest/hover_test.go`, the
//! inlay hint baselines) run through `scripts/effect/ls-cases.mjs`.

use std::rc::Rc;

use ts_goport::effect::rulerunner;
use ts_goport::ls::{LanguageService, lsutil};
use ts_goport::lsp::lsproto;
use ts_goport::options::Tristate;
use ts_goport::project::Session;

use super::projecttestutil::{self, files};
use super::util::*;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const MAIN: &str = "/home/projects/p/main.ts";
const MAIN_URI: &str = "file:///home/projects/p/main.ts";

// Line 1 declares `myEffect`, line 3 starts `program` (`Effect.gen`), line 4
// has `yield*` at character 12.
const MAIN_TEXT: &str = r#"import { Effect } from "effect"
export declare const myEffect: Effect.Effect<string, Error, never>
export declare const plain: string
export const program = Effect.gen(function* () {
  const a = yield* Effect.succeed(1)
  return a
})
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
  [Symbol.iterator](): Generator<Effect<A, E, R>, A, any>
}
export declare function succeed<A>(value: A): Effect<A>
export declare function gen<Eff extends Effect<any, any, any>, AEff>(f: () => Generator<Eff, AEff, never>): Effect<AEff>
"#;

/// The tsconfig text with `plugin` as the plugins list (`""`: no plugin).
fn config(plugin: &str) -> String {
    format!(
        r#"{{"compilerOptions":{{"strict":true,"target":"ESNext","module":"ESNext","moduleResolution":"bundler","plugins":[{plugin}]}}}}"#
    )
}

const PLUGIN: &str = r#"{"name":"@effect/language-service"}"#;

/// A session on the project with `plugin`, the preferences `preferences` and
/// main.ts open, and its language service for main.ts.
fn service(
    plugin: &str,
    preferences: Option<lsutil::UserPreferences>,
) -> (Rc<Session>, LanguageService) {
    let config = config(plugin);
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
    if let Some(preferences) = preferences {
        session.configure(preferences);
    }
    open(&session, MAIN_URI, MAIN_TEXT);
    let service = session
        .get_language_service(&projecttestutil::with_request_id(&bg()), &uri(MAIN_URI))
        .unwrap_or_else(|err| panic!("{}", err.error()));
    (session, service)
}

fn position(line: u32, character: u32) -> lsproto::Position {
    lsproto::Position { line, character }
}

/// The plain text hover at `pos` and its range, or None.
fn hover(service: &LanguageService, pos: lsproto::Position) -> Option<(String, lsproto::Range)> {
    let response = service
        .provide_hover(
            &projecttestutil::with_request_id(&bg()),
            &lsproto::HoverParams {
                text_document: lsproto::TextDocumentIdentifier { uri: uri(MAIN_URI) },
                position: pos,
                ..Default::default()
            },
        )
        .unwrap_or_else(|err| panic!("{}", err.error()));
    let hover = response.hover?;
    let content = hover.contents.markup_content.expect("markup content");
    Some((content.value, hover.range.expect("a hover range")))
}

/// The return type hints that the language service gives for main.ts.
fn return_type_hints(service: &LanguageService) -> Vec<lsproto::InlayHint> {
    let response = service
        .provide_inlay_hint(
            &projecttestutil::with_request_id(&bg()),
            &lsproto::InlayHintParams {
                text_document: lsproto::TextDocumentIdentifier { uri: uri(MAIN_URI) },
                range: lsproto::Range {
                    start: position(0, 0),
                    end: position(8, 0),
                },
                ..Default::default()
            },
        )
        .unwrap_or_else(|err| panic!("{}", err.error()));
    response.inlay_hints.unwrap_or_default()
}

fn inlay_preferences() -> lsutil::UserPreferences {
    let mut preferences = lsutil::new_default_user_preferences();
    preferences
        .inlay_hints
        .include_inlay_function_like_return_type_hints = Tristate::True;
    preferences
}

const TYPE_PARAMETERS: &str =
    "Effect Type Parameters:\n  Success = string\n  Failure = Error\n  Requirements = never\n";

child_test! {
    // Patch 012: hover on an Effect-typed name adds the Effect type
    // parameters (plain text client); a name of another type and a project
    // without the plugin keep the plain hover.
    fn hover_adds_effect_type_parameters() {
        let (_session, on) = service(PLUGIN, None);
        let (text, _) = hover(&on, position(1, 22)).expect("a hover on myEffect");
        assert_eq!(
            text,
            format!("const myEffect: Effect.Effect<string, Error, never>{TYPE_PARAMETERS}")
        );
        let (text, _) = hover(&on, position(2, 22)).expect("a hover on plain");
        assert_eq!(text, "const plain: string");

        let (_session, off) = service("", None);
        let (text, _) = hover(&off, position(1, 22)).expect("a hover on myEffect");
        assert_eq!(text, "const myEffect: Effect.Effect<string, Error, never>");
    }
}

child_test! {
    // Patch 012 with `quickinfo: false`: the plain hover.
    fn hover_with_quickinfo_off_is_plain() {
        let (_session, service) =
            service(r#"{"name":"@effect/language-service","quickinfo":false}"#, None);
        let (text, _) = hover(&service, position(1, 22)).expect("a hover on myEffect");
        assert_eq!(text, "const myEffect: Effect.Effect<string, Error, never>");
    }
}

child_test! {
    // Patch 012 on `yield*` in Effect.gen: the yielded type and its Effect
    // type parameters, with the yield expression as the range. Without the
    // plugin the keyword has no hover.
    fn hover_on_yield_star() {
        let (_session, on) = service(PLUGIN, None);
        for character in [12, 17, 18] {
            let (text, range) = hover(&on, position(4, character)).expect("a hover on yield*");
            assert_eq!(
                text,
                "(yield*) Effect<number, never, never>Effect Type Parameters:\n  Success = number\n  Failure = never\n  Requirements = never\n"
            );
            assert_eq!(
                range,
                lsproto::Range {
                    start: position(4, 12),
                    end: position(4, 36),
                }
            );
        }

        let (_session, off) = service("", None);
        assert_eq!(hover(&off, position(4, 12)), None);
    }
}

child_test! {
    // Patch 015 with `inlays: true`: the return type hint of the Effect.gen
    // generator is removed. With `inlays` off (the default) and without the
    // plugin it stays.
    fn inlay_filter_removes_generator_return_type() {
        let generator_hint = |hints: &[lsproto::InlayHint]| {
            hints
                .iter()
                .filter(|hint| {
                    hint.kind == Some(lsproto::InlayHintKind::TYPE) && hint.position.line == 3
                })
                .count()
        };
        let (_session, filtered) = service(
            r#"{"name":"@effect/language-service","inlays":true}"#,
            Some(inlay_preferences()),
        );
        assert_eq!(generator_hint(&return_type_hints(&filtered)), 0);

        let (_session, inlays_off) = service(PLUGIN, Some(inlay_preferences()));
        assert_eq!(generator_hint(&return_type_hints(&inlays_off)), 1);

        let (_session, off) = service("", Some(inlay_preferences()));
        assert_eq!(generator_hint(&return_type_hints(&off)), 1);
    }
}

child_test! {
    // Patches 011 and 024: on this file the code action and document symbol
    // answers with the plugin are the answers without it, except for the
    // Effect refactors, which come after the other code actions. On
    // `program` 3 of the 21 refactors apply, in Go order (their edits are in
    // `effect_refactors_test.rs`). The range has no Effect diagnostic, so the
    // fixables (E4, E5) add no action. The file has no Layer, service, error
    // or schema, and flows need the `debug` option, so the document symbols
    // (E8) add no `Effect` symbol. The completion answer is not the same: at
    // `Effect.` the plugin appends `gen` and `fn` items
    // (`effect_ls_completions_test.rs`).
    fn code_actions_and_symbols_are_unchanged() {
        let answers = |service: &LanguageService| {
            let ctx = projecttestutil::with_request_id(&bg());
            let mut actions = service
                .provide_code_actions(
                    &ctx,
                    &lsproto::CodeActionParams {
                        text_document: lsproto::TextDocumentIdentifier { uri: uri(MAIN_URI) },
                        range: lsproto::Range {
                            start: position(3, 13),
                            end: position(3, 20),
                        },
                        context: Some(lsproto::CodeActionContext::default()),
                        ..Default::default()
                    },
                )
                .unwrap_or_else(|err| panic!("{}", err.error()))
                .command_or_code_action_array
                .unwrap_or_default();
            let kind = |action: &lsproto::CommandOrCodeAction| {
                action
                    .code_action
                    .as_ref()
                    .and_then(|action| action.kind.as_ref())
                    .map(|kind| kind.0.to_string())
                    .unwrap_or_default()
            };
            let first_refactor = actions
                .iter()
                .position(|action| kind(action).starts_with("refactor.rewrite.effect."))
                .unwrap_or(actions.len());
            let refactors: Vec<String> =
                actions.split_off(first_refactor).iter().map(kind).collect();
            let symbols = service
                .provide_document_symbols(&ctx, &uri(MAIN_URI))
                .unwrap_or_else(|err| panic!("{}", err.error()));
            (format!("{actions:?}\n{symbols:?}"), refactors)
        };
        let (_session, on) = service(PLUGIN, None);
        let (_session, off) = service("", None);
        let (on, on_refactors) = answers(&on);
        let (off, off_refactors) = answers(&off);
        assert_eq!(on, off);
        assert_eq!(off_refactors, Vec::<String>::new());
        assert_eq!(
            on_refactors,
            [
                "refactor.rewrite.effect.wrapWithPipe",
                "refactor.rewrite.effect.toggleTypeAnnotation",
                "refactor.rewrite.effect.toggleLazyConst",
            ]
        );
    }
}

child_test! {
    env &[("TSGO_EFFECT_API", "0")];
    // A standalone API process without TSGO_EFFECT_API=1 has the hooks off,
    // as it has the rules off (`rulerunner::enabled_options`).
    fn hooks_are_off_in_a_standalone_api_process() {
        rulerunner::set_api_process();
        let (_session, service) = service(PLUGIN, None);
        let (text, _) = hover(&service, position(1, 22)).expect("a hover on myEffect");
        assert_eq!(text, "const myEffect: Effect.Effect<string, Error, never>");
        assert_eq!(hover(&service, position(4, 12)), None);
    }
}
