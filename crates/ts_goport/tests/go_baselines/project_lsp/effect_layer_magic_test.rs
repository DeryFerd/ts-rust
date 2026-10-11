//! Port-only tests of the layerMagic refactor
//! (`effect::ls::refactors::layer_magic` and `effect::layergraph` magic.go,
//! Effect-TS/tsgo patch 011; lane effectE9d): "prepare" on a Layer
//! composition, "build" on the `[...] as any as Layer.Layer<T>` form (with
//! and without missing outputs), and nothing without the plugin.
//!
//! The project has a small stand-in for the `effect` package (v3: a `Layer`
//! interface with the variance struct and a data-first `provide`). The
//! expected edits are E0's answers (effect-tsgo 0.51.1 at the Go pin) on
//! the same project (`effectE9d/tools/refactor_probe.py`). The Go cases with
//! the real package (`layerMagic_*.refactors.txt`) and writeTagClassAccessors
//! run through `scripts/effect/ls-cases.mjs`.

use std::rc::Rc;

use ts_goport::ls::LanguageService;
use ts_goport::lsp::lsproto;
use ts_goport::project::Session;

use super::projecttestutil::{self, files};
use super::util::*;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const MAIN: &str = "/home/projects/p/main.ts";
const MAIN_URI: &str = "file:///home/projects/p/main.ts";

// Line 4 declares `dbLive`, line 6 `app` (a Layer.provide call of two
// layers), line 7 `built` and line 8 `missing` (the prepared form; `missing`
// asks for a service that no layer provides).
const MAIN_TEXT: &str = r#"import { Layer } from "effect"
interface Cache { readonly cache: true }
interface Database { readonly db: true }
interface Missing { readonly missing: true }
export declare const dbLive: Layer.Layer<Database>
export declare const cacheLive: Layer.Layer<Cache, never, Database>
export const app = Layer.provide(cacheLive, dbLive)
export const built = [cacheLive, dbLive] as any as Layer.Layer<Cache>
export const missing = [cacheLive, dbLive] as any as Layer.Layer<Cache | Missing>
"#;

const EFFECT_PACKAGE_JSON: &str = r#"{"name":"effect","version":"3.0.0","types":"./index.d.ts"}"#;
const EFFECT_INDEX: &str = "export * as Layer from \"./Layer.js\"\n";
const LAYER_MODULE: &str = r#"export declare const LayerTypeId: unique symbol
export interface Layer<ROut, E = never, RIn = never> {
  readonly [LayerTypeId]: {
    readonly _ROut: (_: ROut) => void
    readonly _E: (_: never) => E
    readonly _RIn: (_: never) => RIn
  }
}
export declare function provide<ROut, E, RIn, ROut2, E2, RIn2>(
  self: Layer<ROut, E, RIn>,
  that: Layer<ROut2, E2, RIn2>
): Layer<ROut, E | E2, RIn2 | Exclude<RIn, ROut2>>
"#;

const PLUGIN: &str = r#"{"name":"@effect/language-service"}"#;

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
            "/home/projects/p/node_modules/effect/Layer.d.ts",
            LAYER_MODULE,
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

type Action = (String, String, Vec<(lsproto::Range, String)>);

/// The layerMagic actions of the refactor answer at `range` (`only:
/// ["refactor"]`, as the Go refactor baselines ask), as `(title, kind,
/// edits of main.ts)`. The other refactors are E9a to E9c.
fn layer_magic_actions(service: &LanguageService, range: lsproto::Range) -> Vec<Action> {
    let response = service
        .provide_code_actions(
            &projecttestutil::with_request_id(&bg()),
            &lsproto::CodeActionParams {
                text_document: lsproto::TextDocumentIdentifier { uri: uri(MAIN_URI) },
                range,
                context: Some(lsproto::CodeActionContext {
                    only: Some(vec![lsproto::CodeActionKind("refactor".into())]),
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
        .map(|action| action.code_action.expect("a code action"))
        .filter(|action| {
            action
                .kind
                .as_ref()
                .is_some_and(|kind| kind.0.starts_with("refactor.rewrite.effect.layerMagic"))
        })
        .map(|action| {
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

/// One action that replaces line `line` (columns 0 to `end`) with `text`.
fn whole_line(title: &str, name: &str, line: u32, end: u32, text: &str) -> Vec<Action> {
    vec![(
        title.to_string(),
        format!("refactor.rewrite.effect.{name}"),
        vec![(range(line, 0, end), text.to_string())],
    )]
}

child_test! {
    // Prepare: on the name of `app` and on a layer inside its call, the
    // leaves become an array cast to the Layer of the new services, with the
    // services that `app` already provides in a comment. Build: on `built`,
    // the layer that provides the target merges and the other is provided;
    // on `missing`, the service no layer provides is named in a comment. No
    // action on a declaration without an initializer. The whole variable
    // statement is printed again (Go's replaceExpressionViaStatement).
    fn layer_magic_prepares_and_builds() {
        let (_session, service) = service(PLUGIN);
        let prepare = whole_line(
            "Prepare layers for automatic composition",
            "layerMagicPrepare",
            6,
            51,
            "export const app = [cacheLive, dbLive] as any as Layer.Layer<Database /* Cache */>;",
        );
        assert_eq!(layer_magic_actions(&service, range(6, 13, 16)), prepare);
        assert_eq!(layer_magic_actions(&service, range(6, 35, 35)), prepare);
        assert_eq!(
            layer_magic_actions(&service, range(7, 13, 18)),
            whole_line(
                "Compose layers automatically with target output services",
                "layerMagicBuild",
                7,
                69,
                "export const built = cacheLive.pipe(Layer.provide(dbLive));",
            )
        );
        assert_eq!(
            layer_magic_actions(&service, range(8, 13, 20)),
            whole_line(
                "Compose layers automatically with target output services",
                "layerMagicBuild",
                8,
                81,
                "export const missing = cacheLive.pipe(Layer.provide(dbLive)) /* Unable to find Missing in the provided layers. */;",
            )
        );
        assert_eq!(layer_magic_actions(&service, range(4, 21, 27)), vec![]);
    }
}

child_test! {
    // Without the plugin the provider gives no refactor.
    fn no_layer_magic_without_the_plugin() {
        let (_session, service) = service("");
        for r in [range(6, 13, 16), range(7, 13, 18), range(8, 13, 20)] {
            assert_eq!(layer_magic_actions(&service, r), vec![]);
        }
    }
}
