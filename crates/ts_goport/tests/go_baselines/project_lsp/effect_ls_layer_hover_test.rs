//! Port-only tests of the Layer hover (`effect::ls::hover`
//! `format_layer_hover`, Effect-TS/tsgo patch 012; lane effectE7): the
//! provides/requires summary and the Mermaid links on a Layer declaration
//! name, with the plugin options `noExternal` and `mermaidProvider`.
//!
//! The project has a small stand-in for the `effect` package (v3: a `Layer`
//! interface with the variance struct). The expected texts are E0's answers
//! (effect-tsgo 0.51.1 at the Go pin) on the same project, with the `pako:`
//! payload of each Mermaid URL inflated: root decision D3 keeps the port's
//! deflate bytes, which differ from Go's. The Go cases with the real
//! package (`internal/effecttest/hover_test.go`) run through
//! `scripts/effect/ls-cases.mjs`.

use std::io::Read as _;
use std::rc::Rc;

use ts_goport::ls::LanguageService;
use ts_goport::lsp::lsproto;
use ts_goport::project::Session;

use super::projecttestutil::{self, files};
use super::util::*;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const MAIN: &str = "/home/projects/p/main.ts";
const MAIN_URI: &str = "file:///home/projects/p/main.ts";

// Line 4 declares `dbLive` (no initializer), line 8 `app` (a call of two
// Layers) and line 9 `app2` (a reference to `app`).
const MAIN_TEXT: &str = r#"import { Layer } from "effect"
interface Cache { readonly cache: true }
interface Database { readonly db: true }
/** The database. */
export declare const dbLive: Layer.Layer<Database>
export declare const cacheLive: Layer.Layer<Cache, never, Database>
declare function provide(self: Layer.Layer<Cache, never, Database>, that: Layer.Layer<Database>): Layer.Layer<Cache>
/** The app. */
export const app = provide(cacheLive, dbLive)
export const app2 = app
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
"#;

const APP: &str = "const app: Layer.Layer<Cache, never, never>";
const SUMMARY: &str = "/**\n * - Cache provided at ln 9 col 27 by `cacheLive`\n */\n";
// The inflated payloads of E0's "Show full graph" and "Show outline" links.
const NESTED: &str = r#"{"code":"flowchart TB\n  subgraph 0 [\"`dbLive\u003cbr/\u003e\u003csmall\u003e_ln 9 col 38_\u003c/small\u003e`\"]\n    subgraph 0_wrap[\" \"]\n      subgraph 0_provides [Provides]\n        0_provides_0[\"Database\"]\n      end\n      style 0_provides stroke:none\n    end\n    style 0_wrap fill:transparent\n    style 0_wrap stroke:none\n  end\n  style 0 fill:transparent\n  subgraph 1 [\"`cacheLive\u003cbr/\u003e\u003csmall\u003e_ln 9 col 27_\u003c/small\u003e`\"]\n    subgraph 1_wrap[\" \"]\n      subgraph 1_requires [Requires]\n        1_requires_0[\"Database\"]\n      end\n      style 1_requires stroke:none\n      subgraph 1_provides [Provides]\n        1_provides_0[\"Cache\"]\n      end\n      style 1_provides stroke:none\n    end\n    style 1_wrap fill:transparent\n    style 1_wrap stroke:none\n  end\n  style 1 fill:transparent\n  subgraph 2 [\"`app\u003cbr/\u003e\u003csmall\u003e_ln 9 col 13_\u003c/small\u003e`\"]\n    subgraph 2_wrap[\" \"]\n      subgraph 2_provides [Provides]\n        2_provides_0[\"Cache\"]\n      end\n      style 2_provides stroke:none\n    end\n    style 2_wrap fill:transparent\n    style 2_wrap stroke:none\n  end\n  style 2 fill:transparent\n  2_provides_0 -.-\u003e 1_provides_0\n  2 -.-x 0"}"#;
const OUTLINE: &str =
    r#"{"code":"flowchart TD\n  0[\"dbLive\"]\n  1[\"cacheLive\"]\n  1 --\u003e 0"}"#;

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

/// The base64url (no padding) bytes of `s`.
fn base64_raw_url_decode(s: &str) -> Vec<u8> {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    let mut out = Vec::new();
    let (mut acc, mut bits) = (0u32, 0u32);
    for ch in s.bytes() {
        let v = ALPHABET.iter().position(|&e| e == ch).expect("base64url");
        acc = (acc << 6) | v as u32;
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
            acc &= (1 << bits) - 1;
        }
    }
    out
}

/// `text` with each `pako:<base64url>` replaced by `pako:<payload>`, the
/// zlib-inflated payload.
fn inflate_mermaid_urls(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(at) = rest.find("pako:") {
        out.push_str(&rest[..at + "pako:".len()]);
        rest = &rest[at + "pako:".len()..];
        let end = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '-' || c == '_'))
            .unwrap_or(rest.len());
        let mut payload = String::new();
        flate2::read::ZlibDecoder::new(base64_raw_url_decode(&rest[..end]).as_slice())
            .read_to_string(&mut payload)
            .expect("zlib inflate");
        out.push('<');
        out.push_str(&payload);
        out.push('>');
        rest = &rest[end..];
    }
    out.push_str(rest);
    out
}

/// The plain text hover at `line`:`character` with its Mermaid URLs
/// inflated.
fn hover(service: &LanguageService, line: u32, character: u32) -> String {
    let response = service
        .provide_hover(
            &projecttestutil::with_request_id(&bg()),
            &lsproto::HoverParams {
                text_document: lsproto::TextDocumentIdentifier { uri: uri(MAIN_URI) },
                position: lsproto::Position { line, character },
                ..Default::default()
            },
        )
        .unwrap_or_else(|err| panic!("{}", err.error()));
    let hover = response.hover.expect("a hover");
    let content = hover.contents.markup_content.expect("markup content");
    inflate_mermaid_urls(&content.value)
}

/// E0's plain text links with the base URL `base`.
fn links(base: &str) -> String {
    format!(
        "{{@link {base}pako:<{NESTED}> Show full graph}}\n\n{{@link {base}pako:<{OUTLINE}> Show outline}}\n\n"
    )
}

child_test! {
    // A hover on a Layer declaration name puts the summary and the two
    // Mermaid links before the documentation. A reference to the Layer, and
    // the name without the plugin, keep the plain hover.
    fn layer_hover_adds_summary_and_graph_links() {
        let (_session, on) = service(PLUGIN);
        assert_eq!(
            hover(&on, 8, 13),
            format!("{APP}{SUMMARY}{}\nThe app.", links("https://mermaid.live/edit#"))
        );
        assert_eq!(hover(&on, 9, 20), format!("{APP}The app."));

        let (_session, off) = service("");
        assert_eq!(hover(&off, 8, 13), format!("{APP}The app."));
    }
}

child_test! {
    // `noExternal: true` drops the links; `mermaidProvider: "mermaid.com"`
    // changes their base URL.
    fn layer_hover_follows_link_options() {
        let (_session, no_external) =
            service(r#"{"name":"@effect/language-service","noExternal":true}"#);
        assert_eq!(hover(&no_external, 8, 13), format!("{APP}{SUMMARY}\nThe app."));

        let (_session, mermaid_com) =
            service(r#"{"name":"@effect/language-service","mermaidProvider":"mermaid.com"}"#);
        assert_eq!(
            hover(&mermaid_com, 8, 13),
            format!(
                "{APP}{SUMMARY}{}\nThe app.",
                links("https://www.mermaidchart.com/play#")
            )
        );
    }
}

child_test! {
    // A Layer declaration with no initializer has no graph: Go writes only
    // "\n" before the documentation.
    fn layer_hover_without_initializer() {
        let (_session, on) = service(PLUGIN);
        assert_eq!(
            hover(&on, 4, 21),
            "const dbLive: Layer.Layer<Database, never, never>\nThe database."
        );

        let (_session, off) = service("");
        assert_eq!(
            hover(&off, 4, 21),
            "const dbLive: Layer.Layer<Database, never, never>The database."
        );
    }
}
