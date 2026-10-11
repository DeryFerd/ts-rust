//! Port-only tests of the Effect document symbol hook
//! (`effect::ls::document_symbols`, Effect-TS/tsgo patch 024; lane
//! effectE8). With the plugin, a Layer declaration gives the synthetic
//! `Effect` > `Layers` tree before the plain symbols. Without the plugin, and
//! in a standalone API process without `TSGO_EFFECT_API=1`, the symbols are
//! the plain ones.
//!
//! The project has a small stand-in for the `effect` package (v3): a `Layer`
//! interface with the v3 variance struct. The Go cases with the real package
//! (the 2 `*.symbols.txt` baselines) run through `scripts/effect/ls-cases.mjs`.

use std::rc::Rc;
use std::sync::Arc;

use ts_goport::effect::rulerunner;
use ts_goport::ls::LanguageService;
use ts_goport::lsp::lsproto;
use ts_goport::project::Session;

use super::projecttestutil::{self, files};
use super::util::*;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const MAIN: &str = "/home/projects/p/main.ts";
const MAIN_URI: &str = "file:///home/projects/p/main.ts";

// Line 1 declares the Layer `live` (characters 21 to 61).
const MAIN_TEXT: &str = r#"import { Layer } from "effect"
export declare const live: Layer.Layer<string, Error, number>
export declare const plain: string
"#;

const EFFECT_PACKAGE_JSON: &str = r#"{"name":"effect","version":"3.0.0","types":"./index.d.ts"}"#;
const EFFECT_INDEX: &str = "export * as Layer from \"./Layer.js\"\n";
const EFFECT_LAYER: &str = r#"export declare const LayerTypeId: unique symbol
export interface Variance<ROut, E, RIn> {
  readonly _ROut: (_: ROut) => void
  readonly _E: (_: never) => E
  readonly _RIn: (_: never) => RIn
}
export interface Layer<ROut, E = never, RIn = never> {
  readonly [LayerTypeId]: Variance<ROut, E, RIn>
}
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
            EFFECT_LAYER,
        ),
    ]));
    open(&session, MAIN_URI, MAIN_TEXT);
    let service = session
        .get_language_service(&projecttestutil::with_request_id(&bg()), &uri(MAIN_URI))
        .unwrap_or_else(|err| panic!("{}", err.error()));
    (session, service)
}

/// The hierarchical document symbols of main.ts.
fn symbols(service: &LanguageService) -> Vec<lsproto::DocumentSymbol> {
    let mut caps = lsproto::ResolvedClientCapabilities::default();
    caps.text_document
        .document_symbol
        .hierarchical_document_symbol_support = true;
    let ctx =
        lsproto::with_client_capabilities(&projecttestutil::with_request_id(&bg()), Arc::new(caps));
    service
        .provide_document_symbols(&ctx, &uri(MAIN_URI))
        .unwrap_or_else(|err| panic!("{}", err.error()))
        .document_symbols
        .expect("hierarchical document symbols")
}

fn range(start: (u32, u32), end: (u32, u32)) -> lsproto::Range {
    lsproto::Range {
        start: lsproto::Position {
            line: start.0,
            character: start.1,
        },
        end: lsproto::Position {
            line: end.0,
            character: end.1,
        },
    }
}

fn symbol(
    name: &str,
    kind: lsproto::SymbolKind,
    detail: Option<&str>,
    rng: lsproto::Range,
    children: Vec<lsproto::DocumentSymbol>,
) -> lsproto::DocumentSymbol {
    lsproto::DocumentSymbol {
        name: name.to_string(),
        detail: detail.map(str::to_string),
        kind,
        range: rng,
        selection_range: rng,
        children: Some(children),
        ..Default::default()
    }
}

child_test! {
    // Go document_symbols.go:20 afterDocumentSymbols: the Layer `live` goes
    // under Effect > Layers with its `<ROut, E, RIn>` detail and the range of
    // its declaration. The synthetic symbols have zero ranges. The plain
    // symbols follow unchanged; `plain` is no Effect declaration.
    fn layer_goes_under_the_effect_symbol() {
        let (_session, on) = service(PLUGIN);
        let (_session, off) = service("");
        let on = symbols(&on);
        let off = symbols(&off);
        let zero = range((0, 0), (0, 0));
        let live = symbol(
            "live",
            lsproto::SymbolKind::VARIABLE,
            Some("<string, Error, number>"),
            range((1, 21), (1, 61)),
            Vec::new(),
        );
        let layers = symbol("Layers", lsproto::SymbolKind::PACKAGE, None, zero, vec![live]);
        let effect = symbol("Effect", lsproto::SymbolKind::PACKAGE, None, zero, vec![layers]);
        assert_eq!(on.first(), Some(&effect));
        assert_eq!(on[1..], off[..]);
        assert!(off.iter().all(|symbol| symbol.name != "Effect"), "{off:?}");
    }
}

child_test! {
    env &[("TSGO_EFFECT_API", "0")];
    // A standalone API process without TSGO_EFFECT_API=1 has the hook off,
    // as it has the rules off (`rulerunner::enabled_options`).
    fn no_effect_symbol_in_a_standalone_api_process() {
        rulerunner::set_api_process();
        let (_session, on) = service(PLUGIN);
        let (_session, off) = service("");
        assert_eq!(symbols(&on), symbols(&off));
    }
}
