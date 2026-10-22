//! Tests of the Effect auto-import style (`effect::ls::autoimportstyle`,
//! Effect-TS/tsgo patches 018 and 027; lane effectE3). The cases follow
//! `internal/effecttest/autoimport_style_consistency_test.go` (effect-tsgo
//! 0.51.1) on a small stand-in for the `effect` package. Each case sends the
//! requests of the Go fourslash verbs through the language server:
//! `textDocument/diagnostic`, then `textDocument/codeAction` with those
//! diagnostics (the quick fixes), and `textDocument/completion` plus
//! `completionItem/resolve` (the completion's import edits).
//!
//! The stand-in package has the v4 layout: the index reexports each module
//! as a namespace (`export * as Effect from "./Effect.js"`), a nested group
//! (`effect/testing`) has its own barrel, and `effect/internal/core` is an
//! internal module.

use ts_goport::effect::rulerunner;
use ts_goport::ls::lsconv;
use ts_goport::lsp::lsproto;

use super::lsp_server_completion_test::init_completion_client;
use super::lsptestutil::LspClient;

const ROOT: &str = "/home/projects/p";
const MAIN: &str = "/home/projects/p/main.ts";

const EFFECT_PACKAGE_JSON: &str = r#"{
  "name": "effect",
  "version": "4.0.0",
  "exports": {
    ".": { "types": "./index.d.ts" },
    "./Effect": { "types": "./Effect.d.ts" },
    "./testing": { "types": "./testing/index.d.ts" },
    "./testing/TestClock": { "types": "./testing/TestClock.d.ts" },
    "./internal/core": { "types": "./internal/core.d.ts" }
  }
}"#;
const EFFECT_INDEX: &str = "export * as Effect from \"./Effect.js\"\n";
const EFFECT_MODULE: &str = r#"export interface Effect<A> {
  readonly _A: A
}
export declare function succeed<A>(value: A): Effect<A>
export declare function runPromiseExit<A>(effect?: Effect<A>): Promise<A>
"#;
const TESTING_INDEX: &str = "export * as TestClock from \"./TestClock.js\"\n";
const TEST_CLOCK: &str = r#"export declare function adjust(millis: number): void
export declare function testClockWith(f: () => unknown): void
"#;
const INTERNAL_CORE: &str = "export declare const internalOnly: number\n";

const PLUGIN: &str = r#"{"name":"@effect/language-service"}"#;
const NAMESPACE: &str =
    r#"{"name":"@effect/language-service","namespaceImportPackages":["effect"]}"#;

/// A language server on the project with the plugin list `plugins` (`""`:
/// no plugin) and `main.ts` open with `text`.
fn server(plugins: &str, text: &str) -> LspClient {
    let config = format!(
        r#"{{"compilerOptions":{{"strict":true,"target":"ESNext","module":"ESNext","moduleResolution":"bundler","plugins":[{plugins}]}}}}"#
    );
    let pkg = |name: &str| format!("{ROOT}/node_modules/effect/{name}");
    let files = [
        (format!("{ROOT}/tsconfig.json"), config),
        (MAIN.to_string(), text.to_string()),
        (pkg("package.json"), EFFECT_PACKAGE_JSON.to_string()),
        (pkg("index.d.ts"), EFFECT_INDEX.to_string()),
        (pkg("Effect.d.ts"), EFFECT_MODULE.to_string()),
        (pkg("testing/index.d.ts"), TESTING_INDEX.to_string()),
        (pkg("testing/TestClock.d.ts"), TEST_CLOCK.to_string()),
        (pkg("internal/core.d.ts"), INTERNAL_CORE.to_string()),
    ];
    let entries: Vec<(&str, &str)> = files
        .iter()
        .map(|(p, t)| (p.as_str(), t.as_str()))
        .collect();
    let client = init_completion_client(ROOT, &entries);
    client.send_notification(
        &lsproto::TEXT_DOCUMENT_DID_OPEN_INFO,
        lsproto::DidOpenTextDocumentParams {
            text_document: Some(lsproto::TextDocumentItem {
                uri: main_uri(),
                language_id: lsproto::LanguageKind::TYPE_SCRIPT,
                text: text.to_string(),
                ..Default::default()
            }),
        },
    );
    client
}

fn main_uri() -> lsproto::DocumentUri {
    lsconv::file_name_to_document_uri(MAIN)
}

fn document() -> lsproto::TextDocumentIdentifier {
    lsproto::TextDocumentIdentifier { uri: main_uri() }
}

/// The byte offset of `pos` in `text` (ASCII text: UTF-16 units are bytes).
fn offset(text: &str, pos: lsproto::Position) -> usize {
    let line_start: usize = text
        .split_inclusive('\n')
        .take(pos.line as usize)
        .map(str::len)
        .sum();
    line_start + pos.character as usize
}

/// `text` with `edits` applied. Edits at one position apply in list order,
/// as LSP clients and the Go fourslash `applyTextEdits` do.
fn apply(text: &str, edits: &[lsproto::TextEdit]) -> String {
    let mut ranged: Vec<(usize, usize, usize, &str)> = edits
        .iter()
        .enumerate()
        .map(|(i, edit)| {
            (
                offset(text, edit.range.start),
                i,
                offset(text, edit.range.end),
                edit.new_text.as_str(),
            )
        })
        .collect();
    ranged.sort_by(|a, b| (b.0, b.1).cmp(&(a.0, a.1)));
    let mut out = text.to_string();
    for (start, _, end, new_text) in ranged {
        out.replace_range(start..end, new_text);
    }
    out
}

/// The import quick fixes for the "Cannot find name" error at `pos` (the
/// Go `VerifyImportFixAtPosition` requests): each action's title and the
/// text after its edits.
fn import_fixes(client: &LspClient, text: &str, pos: lsproto::Position) -> Vec<(String, String)> {
    let (msg, report) = client.send_request(
        &lsproto::TEXT_DOCUMENT_DIAGNOSTIC_INFO,
        lsproto::DocumentDiagnosticParams {
            text_document: document(),
            ..Default::default()
        },
    );
    assert!(msg.error.is_none(), "{:?}", msg.error);
    let diagnostics: Vec<Option<lsproto::Diagnostic>> = report
        .and_then(|report| report.full_document_diagnostic_report)
        .expect("a full diagnostic report")
        .items
        .into_iter()
        .map(Some)
        .collect();
    let (msg, actions) = client.send_request(
        &lsproto::TEXT_DOCUMENT_CODE_ACTION_INFO,
        lsproto::CodeActionParams {
            text_document: document(),
            range: lsproto::Range {
                start: pos,
                end: pos,
            },
            context: Some(lsproto::CodeActionContext {
                diagnostics,
                only: Some(vec![lsproto::CodeActionKind::QUICK_FIX]),
                ..Default::default()
            }),
            ..Default::default()
        },
    );
    assert!(msg.error.is_none(), "{:?}", msg.error);
    actions
        .and_then(|actions| actions.command_or_code_action_array)
        .unwrap_or_default()
        .into_iter()
        .filter_map(|action| action.code_action)
        .filter(|action| action.title.starts_with("Add import from"))
        .map(|action| {
            let changes = action
                .edit
                .and_then(|edit| edit.changes)
                .expect("the fix has changes");
            let edits: Vec<lsproto::TextEdit> = changes
                .get(&main_uri())
                .expect("edits of main.ts")
                .iter()
                .flatten()
                .cloned()
                .collect();
            (action.title, apply(text, &edits))
        })
        .collect()
}

/// The auto-import completion items labeled `label` at `pos`.
fn auto_import_items(
    client: &LspClient,
    pos: lsproto::Position,
    label: &str,
) -> Vec<lsproto::CompletionItem> {
    let (msg, completion) = client.send_request(
        &lsproto::TEXT_DOCUMENT_COMPLETION_INFO,
        lsproto::CompletionParams {
            text_document: document(),
            position: pos,
            context: Some(lsproto::CompletionContext::default()),
            ..Default::default()
        },
    );
    assert!(msg.error.is_none(), "{:?}", msg.error);
    let completion = completion.expect("a completion answer");
    let items = match completion.list {
        Some(list) => list.items,
        None => completion.items.unwrap_or_default(),
    };
    items
        .into_iter()
        .filter(|item| {
            item.label == label
                && item
                    .data
                    .as_ref()
                    .is_some_and(|data| data.auto_import.is_some())
        })
        .collect()
}

fn auto_import_fix(item: &lsproto::CompletionItem) -> &lsproto::AutoImportFix {
    item.data
        .as_ref()
        .and_then(|data| data.auto_import.as_ref())
        .expect("auto-import data")
}

/// The detail of the resolved `item` and the text after its additional
/// edits (the Go `VerifyApplyCodeActionFromCompletion` requests).
fn resolve(client: &LspClient, text: &str, item: lsproto::CompletionItem) -> (String, String) {
    let (msg, resolved) = client.send_request(&lsproto::COMPLETION_ITEM_RESOLVE_INFO, item);
    assert!(msg.error.is_none(), "{:?}", msg.error);
    let resolved = resolved.flatten().expect("a resolved item");
    let edits: Vec<lsproto::TextEdit> = resolved
        .additional_text_edits
        .unwrap_or_default()
        .into_iter()
        .flatten()
        .collect();
    (resolved.detail.unwrap_or_default(), apply(text, &edits))
}

fn position(line: u32, character: u32) -> lsproto::Position {
    lsproto::Position { line, character }
}

const RUN_PROMISE_EXIT: &str = "runPromiseExit();\n";
const RUN_PROMISE_EXIT_NAMESPACE: &str =
    "import * as Effect from \"effect/Effect\";\n\nEffect.runPromiseExit();\n";

child_test! {
    // Go: TestAutoImportEffectStyleConsistency_namespace (with "EFFECT" in
    // upper case). The quick fix and the completion both import the module as
    // a namespace and qualify the name. The completion data holds the
    // namespace import kind, the prefix and the usage position.
    fn namespace_rewrite() {
        let plugin = r#"{"name":"@effect/language-service","namespaceImportPackages":["EFFECT"]}"#;
        let client = server(plugin, RUN_PROMISE_EXIT);
        assert_eq!(
            import_fixes(&client, RUN_PROMISE_EXIT, position(0, 0)),
            [(
                "Add import from \"effect/Effect\"".to_string(),
                RUN_PROMISE_EXIT_NAMESPACE.to_string()
            )]
        );

        let items = auto_import_items(&client, position(0, 14), "runPromiseExit");
        assert_eq!(items.len(), 1, "{items:?}");
        let fix = auto_import_fix(&items[0]);
        assert_eq!(fix.kind, lsproto::AutoImportFixKind::ADD_NEW);
        assert_eq!(fix.import_kind, lsproto::ImportKind::NAMESPACE);
        assert_eq!(fix.module_specifier, "effect/Effect");
        assert_eq!(fix.namespace_prefix, "Effect");
        assert_eq!(fix.usage_position, Some(position(0, 0)));
        assert_eq!(
            resolve(&client, RUN_PROMISE_EXIT, items[0].clone()),
            (
                "Add import from \"effect/Effect\"".to_string(),
                RUN_PROMISE_EXIT_NAMESPACE.to_string()
            )
        );
    }
}

child_test! {
    // Go: TestAutoImportEffectStyleConsistency_namespaceReexport. The
    // namespace reexport `Effect` of the package index becomes a namespace
    // import of its module, with no qualifier.
    fn namespace_reexport_imports_its_module() {
        let text = "const x = Effect;\n";
        let client = server(NAMESPACE, text);
        let import_only = "import * as Effect from \"effect/Effect\";\n\nconst x = Effect;\n";
        let fixes = import_fixes(&client, text, position(0, 10));
        assert!(
            fixes.iter().all(|(title, _)| title == "Add import from \"effect/Effect\""),
            "{fixes:?}"
        );
        assert!(fixes.iter().any(|(_, after)| after == import_only), "{fixes:?}");

        let items = auto_import_items(&client, position(0, 16), "Effect");
        let item = items
            .iter()
            .find(|item| auto_import_fix(item).namespace_prefix.is_empty())
            .unwrap_or_else(|| panic!("an item with no prefix: {items:?}"))
            .clone();
        let fix = auto_import_fix(&item);
        assert_eq!(fix.import_kind, lsproto::ImportKind::NAMESPACE);
        assert_eq!(fix.module_specifier, "effect/Effect");
        assert_eq!(
            resolve(&client, text, item),
            ("Add import from \"effect/Effect\"".to_string(), import_only.to_string())
        );
    }
}

child_test! {
    // Go: TestApplySuppressesEffectInternalImport, through the server. The
    // `effect/internal/...` fixes are removed. Without the plugin they stay.
    fn effect_internal_fixes_are_removed() {
        let text = "internalOnly;\n";
        let client_on = server(NAMESPACE, text);
        assert_eq!(import_fixes(&client_on, text, position(0, 0)), []);
        assert_eq!(auto_import_items(&client_on, position(0, 12), "internalOnly").len(), 0);

        let client_off = server("", text);
        assert_eq!(
            import_fixes(&client_off, text, position(0, 0)),
            [(
                "Add import from \"effect/internal/core\"".to_string(),
                "import { internalOnly } from \"effect/internal/core\";\n\ninternalOnly;\n"
                    .to_string()
            )]
        );
    }
}

child_test! {
    // Go: TestAutoImportEffectStyleConsistency_barrel. The fix imports the
    // module from the package barrel, or from the group barrel for a nested
    // module (`effectNestedBarrel`), and qualifies the name.
    fn barrel_rewrite() {
        let plugin = r#"{"name":"@effect/language-service","barrelImportPackages":["EFFECT"]}"#;
        let client = server(plugin, RUN_PROMISE_EXIT);
        assert_eq!(
            import_fixes(&client, RUN_PROMISE_EXIT, position(0, 0)),
            [(
                "Add import from \"effect\"".to_string(),
                "import { Effect } from \"effect\";\n\nEffect.runPromiseExit();\n".to_string()
            )]
        );

        let text = "testClockWith(() => 1);\n";
        let client = server(plugin, text);
        assert_eq!(
            import_fixes(&client, text, position(0, 0)),
            [(
                "Add import from \"effect/testing\"".to_string(),
                "import { TestClock } from \"effect/testing\";\n\nTestClock.testClockWith(() => 1);\n"
                    .to_string()
            )]
        );
    }
}

child_test! {
    // Go: TestAutoImportEffectStyleConsistency_testClockWithNamespace.
    fn nested_module_namespace_rewrite() {
        let text = "testClockWith(() => 1);\n";
        let after =
            "import * as TestClock from \"effect/testing/TestClock\";\n\nTestClock.testClockWith(() => 1);\n";
        let client = server(NAMESPACE, text);
        assert_eq!(
            import_fixes(&client, text, position(0, 0)),
            [(
                "Add import from \"effect/testing/TestClock\"".to_string(),
                after.to_string()
            )]
        );
        let items = auto_import_items(&client, position(0, 13), "testClockWith");
        assert_eq!(items.len(), 1, "{items:?}");
        assert_eq!(
            resolve(&client, text, items[0].clone()),
            (
                "Add import from \"effect/testing/TestClock\"".to_string(),
                after.to_string()
            )
        );
    }
}

child_test! {
    // Go: TestAutoImportEffectStyleConsistency_testClockWithNamespaceAlongsideNamedImport.
    // The add-to-existing fix becomes a new namespace import line.
    fn add_to_existing_becomes_a_namespace_import() {
        let text = "import { adjust } from \"effect/testing/TestClock\"\n\nvoid adjust\ntestClockWith(() => 1);\n";
        let client = server(NAMESPACE, text);
        assert_eq!(
            import_fixes(&client, text, position(3, 0)),
            [(
                "Add import from \"effect/testing/TestClock\"".to_string(),
                "import * as TestClock from \"effect/testing/TestClock\";\nimport { adjust } from \"effect/testing/TestClock\"\n\nvoid adjust\nTestClock.testClockWith(() => 1);\n"
                    .to_string()
            )]
        );
    }
}

child_test! {
    // Go: TestAutoImportEffectStyleConsistency_testClockWithUsesExistingNamespaceImport
    // and TestNewFixTransformerPrefersExistingNamespaceUse. The existing
    // namespace import wins: the only fix adds the qualifier.
    fn existing_namespace_import_wins() {
        let text = "import * as TestClock from \"effect/testing/TestClock\";\n\nvoid TestClock.adjust\ntestClockWith(() => 1);\n";
        let client = server(NAMESPACE, text);
        let (msg, report) = client.send_request(
            &lsproto::TEXT_DOCUMENT_DIAGNOSTIC_INFO,
            lsproto::DocumentDiagnosticParams {
                text_document: document(),
                ..Default::default()
            },
        );
        assert!(msg.error.is_none(), "{:?}", msg.error);
        let diagnostics: Vec<Option<lsproto::Diagnostic>> = report
            .and_then(|report| report.full_document_diagnostic_report)
            .expect("a full diagnostic report")
            .items
            .into_iter()
            .map(Some)
            .collect();
        let (msg, actions) = client.send_request(
            &lsproto::TEXT_DOCUMENT_CODE_ACTION_INFO,
            lsproto::CodeActionParams {
                text_document: document(),
                range: lsproto::Range {
                    start: position(3, 0),
                    end: position(3, 0),
                },
                context: Some(lsproto::CodeActionContext {
                    diagnostics,
                    only: Some(vec![lsproto::CodeActionKind::QUICK_FIX]),
                    ..Default::default()
                }),
                ..Default::default()
            },
        );
        assert!(msg.error.is_none(), "{:?}", msg.error);
        let actions: Vec<(String, String)> = actions
            .and_then(|actions| actions.command_or_code_action_array)
            .unwrap_or_default()
            .into_iter()
            .filter_map(|action| action.code_action)
            .map(|action| {
                let edits: Vec<lsproto::TextEdit> = action
                    .edit
                    .and_then(|edit| edit.changes)
                    .and_then(|changes| changes.get(&main_uri()).cloned())
                    .unwrap_or_default()
                    .into_iter()
                    .flatten()
                    .collect();
                (action.title, apply(text, &edits))
            })
            .collect();
        assert_eq!(
            actions,
            [(
                "Change 'testClockWith' to 'TestClock.testClockWith'".to_string(),
                "import * as TestClock from \"effect/testing/TestClock\";\n\nvoid TestClock.adjust\nTestClock.testClockWith(() => 1);\n"
                    .to_string()
            )]
        );
    }
}

child_test! {
    // PORT: patch 018 sets the usage position on every AddNew and
    // AddToExisting fix. The port sets it only with the plugin on, so a
    // project without the plugin answers as plain tsgo. With the plugin and
    // no style option, the completion data holds the usage position and the
    // fix is the plain named import, as in effect-tsgo.
    fn usage_position_only_with_the_plugin() {
        let plain_fix = [(
            "Add import from \"effect/Effect\"".to_string(),
            "import { runPromiseExit } from \"effect/Effect\";\n\nrunPromiseExit();\n".to_string(),
        )];
        for (plugins, usage_position) in [("", None), (PLUGIN, Some(position(0, 0)))] {
            let client = server(plugins, RUN_PROMISE_EXIT);
            assert_eq!(import_fixes(&client, RUN_PROMISE_EXIT, position(0, 0)), plain_fix);
            let items = auto_import_items(&client, position(0, 14), "runPromiseExit");
            assert_eq!(items.len(), 1, "{items:?}");
            let fix = auto_import_fix(&items[0]);
            assert_eq!(fix.import_kind, lsproto::ImportKind::NAMED);
            assert_eq!(fix.namespace_prefix, "");
            assert_eq!(fix.usage_position, usage_position, "plugins {plugins:?}");
        }
    }
}

child_test! {
    env &[("TSGO_EFFECT_API", "0")];
    // A standalone API process without TSGO_EFFECT_API=1 has the Effect
    // hooks off, so the auto-import style does not apply.
    fn style_is_off_in_a_standalone_api_process() {
        rulerunner::set_api_process();
        let client = server(NAMESPACE, RUN_PROMISE_EXIT);
        assert_eq!(
            import_fixes(&client, RUN_PROMISE_EXIT, position(0, 0)),
            [(
                "Add import from \"effect/Effect\"".to_string(),
                "import { runPromiseExit } from \"effect/Effect\";\n\nrunPromiseExit();\n"
                    .to_string()
            )]
        );
        let items = auto_import_items(&client, position(0, 14), "runPromiseExit");
        assert_eq!(items.len(), 1, "{items:?}");
        assert_eq!(auto_import_fix(&items[0]).usage_position, None);
    }
}
