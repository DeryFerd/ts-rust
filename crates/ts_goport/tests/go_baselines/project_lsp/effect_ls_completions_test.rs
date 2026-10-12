//! Port-only tests of the Effect completions (`effect::ls::completions`,
//! Effect-TS/tsgo patch 022 and `internal/completions`; lane effectE6). The
//! Effect items come after the plain items, in the order of
//! `completions.All`, and get the item data as the plain items do. Without
//! the plugin, with `completions: false` and in a standalone API process
//! without `TSGO_EFFECT_API=1` the answer is the plain answer.
//!
//! The project has the small stand-in for the `effect` package of
//! `effect_ls_hooks_test.rs`. The Go tests with the real package
//! (`internal/effecttest/completion_test.go` and the unit tests of
//! `internal/completions`) run through `scripts/effect/ls-cases.mjs --kinds
//! completion`.

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

// Line 2 has `Effect.` (the dot ends at character 26), line 6 a Duration
// string (`"1 "` from character 27 to 31), line 7 a `// @` comment, and
// line 8 an extends clause `Data.` (from character 18 to 23).
const MAIN_TEXT: &str = r#"import { Effect } from "effect"
export const program = Effect.gen(function* () {
  const a = yield* Effect.succeed(1)
  return a
})
type Duration = `${number} nanos` | `${number} millis`
export const d: Duration = "1 "
// @
class Foo extends Data.
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

/// A session on the project with `plugin` and main.ts open, and its
/// language service for main.ts.
fn service(plugin: &str) -> (Rc<Session>, LanguageService) {
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
    open(&session, MAIN_URI, MAIN_TEXT);
    let service = session
        .get_language_service(&projecttestutil::with_request_id(&bg()), &uri(MAIN_URI))
        .unwrap_or_else(|err| panic!("{}", err.error()));
    (session, service)
}

fn position(line: u32, character: u32) -> lsproto::Position {
    lsproto::Position { line, character }
}

fn range(start: lsproto::Position, end: lsproto::Position) -> lsproto::Range {
    lsproto::Range { start, end }
}

/// The completion items at `pos` (an empty list when the answer is null).
fn completion_items(
    service: &LanguageService,
    pos: lsproto::Position,
) -> Vec<lsproto::CompletionItem> {
    let response = service
        .provide_completion(
            &projecttestutil::with_request_id(&bg()),
            &uri(MAIN_URI),
            pos,
            None,
        )
        .unwrap_or_else(|err| panic!("{}", err.error()));
    assert!(response.items.is_none(), "the answer is a list or null");
    response.list.map(|list| list.items).unwrap_or_default()
}

/// The items of `on` after the plain items `off`: `on` must start with `off`.
fn effect_items(
    on: Vec<lsproto::CompletionItem>,
    off: &[lsproto::CompletionItem],
) -> Vec<lsproto::CompletionItem> {
    assert!(on.len() >= off.len(), "the Effect items are appended");
    assert_eq!(
        &on[..off.len()],
        off,
        "the plain items come first, unchanged"
    );
    on[off.len()..].to_vec()
}

fn labels(items: &[lsproto::CompletionItem]) -> Vec<&str> {
    items.iter().map(|item| item.label.as_str()).collect()
}

/// The text edit of `item` (Effect items always have one).
fn text_edit(item: &lsproto::CompletionItem) -> &lsproto::TextEdit {
    item.text_edit
        .as_ref()
        .and_then(|edit| edit.text_edit.as_ref())
        .expect("a text edit")
}

child_test! {
    // After `Effect.` the plugin appends `gen(function*(){})` (the
    // namespace has a callable `gen`) and the three fn items, the first one
    // named after the enclosing variable. Each is a snippet with sort text
    // "11", an empty edit at the cursor and the item data of the request.
    fn effect_items_follow_the_plain_items() {
        let pos = position(2, 26);
        let (_session, off) = service("");
        let off = completion_items(&off, pos);
        assert!(labels(&off).contains(&"succeed"), "the plain list has succeed");
        let (_session, on) = service(PLUGIN);
        let items = effect_items(completion_items(&on, pos), &off);
        assert_eq!(
            labels(&items),
            [
                "gen(function*(){})",
                r#"fn("a")"#,
                "fn(function*(){})",
                "fnUntraced(function*(){})",
            ]
        );
        let new_texts: Vec<&str> = items.iter().map(|item| text_edit(item).new_text.as_str()).collect();
        assert_eq!(
            new_texts,
            [
                "gen(function*(){${0}})",
                r#"fn("a")(function*(${1}){${0}})"#,
                "fn(function*(${1}){${0}})",
                "fnUntraced(function*(${1}){${0}})",
            ]
        );
        for item in &items {
            assert_eq!(item.kind, Some(lsproto::CompletionItemKind::VARIABLE));
            assert_eq!(item.insert_text_format, Some(lsproto::InsertTextFormat::SNIPPET));
            assert_eq!(item.sort_text.as_deref(), Some("11"));
            assert_eq!(item.filter_text, None);
            assert_eq!(text_edit(item).range, range(pos, pos));
            let data = item.data.as_ref().expect("item data");
            assert_eq!(data.file_name, MAIN);
            assert_eq!(data.name, item.label);
        }
    }
}

child_test! {
    // With `completions: false` the answer is the plain answer.
    fn completions_off_gives_the_plain_answer() {
        let (_session, off) = service("");
        let (_session, disabled) =
            service(r#"{"name":"@effect/language-service","completions":false}"#);
        for pos in [position(2, 26), position(6, 30), position(7, 4), position(8, 23)] {
            assert_eq!(completion_items(&disabled, pos), completion_items(&off, pos), "at {pos:?}");
        }
    }
}

child_test! {
    // In a Duration string (a union of template literals whose second text
    // is "nanos") the 8 units replace the string content.
    fn duration_units_in_a_duration_string() {
        let pos = position(6, 30);
        let (_session, off) = service("");
        let off = completion_items(&off, pos);
        let (_session, on) = service(PLUGIN);
        let items = effect_items(completion_items(&on, pos), &off);
        assert_eq!(
            labels(&items),
            ["nanos", "micros", "millis", "seconds", "minutes", "hours", "days", "weeks"]
        );
        for item in &items {
            assert_eq!(item.kind, Some(lsproto::CompletionItemKind::CONSTANT));
            let edit = text_edit(item);
            assert_eq!(edit.new_text, format!("${{0}} {}", item.label));
            assert_eq!(edit.range, range(position(6, 28), position(6, 30)));
        }
    }
}

child_test! {
    // After `// @` the diagnostics, codegens and JSDoc directives, from the
    // `@`. The plain answer there is null, so the list holds only them.
    fn directives_in_a_comment() {
        let pos = position(7, 4);
        let (_session, off) = service("");
        assert_eq!(completion_items(&off, pos), []);
        let (_session, on) = service(PLUGIN);
        let items = completion_items(&on, pos);
        assert_eq!(
            labels(&items),
            [
                "@effect-diagnostics",
                "@effect-diagnostics-next-line",
                "@effect-codegens",
                "@effect-identifier",
            ]
        );
        let mut rule_names: Vec<&str> =
            ts_goport::effect::rules::ALL.iter().map(|rule| rule.name).collect();
        rule_names.sort_unstable();
        assert_eq!(
            text_edit(&items[0]).new_text,
            format!(
                "@effect-diagnostics ${{1|{}|}}:${{2|off,warning,error,message,suggestion|}}$0",
                rule_names.join(",")
            )
        );
        assert_eq!(
            text_edit(&items[2]).new_text,
            "@effect-codegens ${1|accessors,annotate,typeToSchema|} $0"
        );
        assert_eq!(text_edit(&items[3]).new_text, "@effect-identifier");
        for item in &items {
            assert_eq!(item.kind, Some(lsproto::CompletionItemKind::CONSTANT));
            assert_eq!(text_edit(item).range, range(position(7, 3), pos));
        }
    }
}

child_test! {
    // In `class Foo extends Data.` (Data not imported, so its module name is
    // the fallback "Data"): Data.TaggedError and Data.TaggedClass over the
    // whole `Data.` expression, filtered by `Data.<label>`.
    fn data_classes_in_an_extends_clause() {
        let pos = position(8, 23);
        let (_session, off) = service("");
        let off = completion_items(&off, pos);
        let (_session, on) = service(PLUGIN);
        let items = effect_items(completion_items(&on, pos), &off);
        assert_eq!(labels(&items), [r#"TaggedError("Foo")"#, r#"TaggedClass("Foo")"#]);
        assert_eq!(text_edit(&items[0]).new_text, r#"Data.TaggedError("Foo")<{${0}}>{}"#);
        assert_eq!(text_edit(&items[1]).new_text, r#"Data.TaggedClass("Foo")<{${0}}>{}"#);
        for item in &items {
            assert_eq!(item.filter_text, Some(format!("Data.{}", item.label)));
            assert_eq!(text_edit(item).range, range(position(8, 18), pos));
        }
    }
}

child_test! {
    env &[("TSGO_EFFECT_API", "0")];
    // A standalone API process without TSGO_EFFECT_API=1 has the hook off,
    // as it has the rules off (`rulerunner::enabled_options`).
    fn no_effect_items_in_a_standalone_api_process() {
        rulerunner::set_api_process();
        let (_session, service) = service(PLUGIN);
        let items = completion_items(&service, position(2, 26));
        assert!(labels(&items).contains(&"succeed"));
        assert!(!labels(&items).contains(&"gen(function*(){})"));
        assert_eq!(completion_items(&service, position(7, 4)), []);
    }
}
