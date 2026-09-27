//! Port of Go `internal/lsp/server_completion_test.go`.
//!
//! PORT: Go answers `workspace/configuration` with `[]any{prefs}` and sends
//! `Settings: map[string]any{"typescript": prefs}` where `prefs` is a
//! `*lsutil.UserPreferences`. `lsutil.ParseUserPreferences` matches only a
//! `map[string]any` or a `UserPreferences` value, so Go ignores these
//! pointers and the server keeps its default preferences. The port sends
//! `null` in their place, which the Rust parser also ignores.

use std::sync::Arc;

use ts_goport::frontend::json_ext::LspAny;
use ts_goport::ls::lsconv;
use ts_goport::lsp::lsproto;

use super::lsptestutil::{self, LspClient, result_response};
use super::projecttestutil::files;

// Go: server_completion_test.go:19 initCompletionClient
pub(super) fn init_completion_client(cwd: &str, entries: &[(&str, &str)]) -> LspClient {
    let on_server_request: lsptestutil::ServerRequestHandler = Arc::new(|req| {
        if req.method == lsproto::Method::WORKSPACE_CONFIGURATION {
            return Some(result_response(req, Box::new(vec![LspAny::Null])));
        }
        if req.method == lsproto::Method::CLIENT_REGISTER_CAPABILITY
            || req.method == lsproto::Method::CLIENT_UNREGISTER_CAPABILITY
        {
            return Some(result_response(req, Box::new(lsproto::Null)));
        }
        None
    });

    let client = lsptestutil::new_lsp_client(
        lsptestutil::server_setup(cwd, files(entries)),
        Some(on_server_request),
        None,
    );

    let (init_msg, _) = client.send_request(
        &lsproto::INITIALIZE_INFO,
        lsproto::InitializeParams {
            capabilities: Some(lsproto::ClientCapabilities::default()),
            ..Default::default()
        },
    );
    assert!(init_msg.error.is_none(), "Initialize failed");
    client.send_notification(
        &lsproto::INITIALIZED_INFO,
        lsproto::InitializedParams::default(),
    );

    let mut settings = indexmap::IndexMap::new();
    settings.insert("typescript".to_string(), LspAny::Null);
    client.send_notification(
        &lsproto::WORKSPACE_DID_CHANGE_CONFIGURATION_INFO,
        lsproto::DidChangeConfigurationParams {
            settings: LspAny::Object(settings),
        },
    );

    client
}

// Go: server_completion_test.go:65 completionItems
fn completion_items(resp: Option<lsproto::CompletionResponse>) -> Vec<lsproto::CompletionItem> {
    let Some(resp) = resp else {
        return Vec::new();
    };
    if let Some(list) = resp.list {
        return list.items;
    }
    resp.items.unwrap_or_default()
}

// Go: server_completion_test.go:75 findCompletionItem
fn find_completion_item<'a>(
    items: &'a [lsproto::CompletionItem],
    label: &str,
) -> Option<&'a lsproto::CompletionItem> {
    items.iter().find(|item| item.label == label)
}

fn open(client: &LspClient, u: &lsproto::DocumentUri, text: &str) {
    client.send_notification(
        &lsproto::TEXT_DOCUMENT_DID_OPEN_INFO,
        lsproto::DidOpenTextDocumentParams {
            text_document: Some(lsproto::TextDocumentItem {
                uri: u.clone(),
                language_id: lsproto::LanguageKind::TYPE_SCRIPT,
                text: text.to_string(),
                ..Default::default()
            }),
        },
    );
}

fn close(client: &LspClient, u: &lsproto::DocumentUri) {
    client.send_notification(
        &lsproto::TEXT_DOCUMENT_DID_CLOSE_INFO,
        lsproto::DidCloseTextDocumentParams {
            text_document: lsproto::TextDocumentIdentifier { uri: u.clone() },
        },
    );
}

fn completion_params(
    u: &lsproto::DocumentUri,
    line: u32,
    character: u32,
) -> lsproto::CompletionParams {
    lsproto::CompletionParams {
        text_document: lsproto::TextDocumentIdentifier { uri: u.clone() },
        position: lsproto::Position { line, character },
        context: Some(lsproto::CompletionContext::default()),
        ..Default::default()
    }
}

/// The checks of the auto-import completion subtests: `someVar` with an
/// auto-import fix from "./a".
fn assert_some_var_auto_import(
    msg: &lsproto::ResponseMessage,
    resp: Option<lsproto::CompletionResponse>,
    message: &str,
) {
    assert!(msg.error.is_none(), "{:?}", msg.error);
    let items = completion_items(resp);
    let item = find_completion_item(&items, "someVar").unwrap_or_else(|| panic!("{message}"));
    let auto_import = item
        .data
        .as_ref()
        .and_then(|data| data.auto_import.as_ref())
        .expect("item.Data.AutoImport");
    assert_eq!(auto_import.module_specifier, "./a");
}

const TSCONFIG: &str = r#"{"compilerOptions": {"module": "esnext", "target": "esnext"}}"#;

child_test! {
    // Go: server_completion_test.go:86 TestCompletionAfterFileClose
    fn completion_after_file_close() {
        let client = init_completion_client(
            "/home/projects",
            &[
                ("/home/projects/tsconfig.json", TSCONFIG),
                ("/home/projects/a.ts", "export const someVar = 10;"),
                ("/home/projects/b.ts", "s"),
            ],
        );

        let a_uri = lsconv::file_name_to_document_uri("/home/projects/a.ts");
        let b_uri = lsconv::file_name_to_document_uri("/home/projects/b.ts");
        open(&client, &a_uri, "export const someVar = 10;");
        open(&client, &b_uri, "s");

        close(&client, &b_uri);

        let (msg, resp) = client.send_request(&lsproto::TEXT_DOCUMENT_COMPLETION_INFO, completion_params(&b_uri, 0, 1));
        assert_some_var_auto_import(&msg, resp, "someVar");
    }
}

child_test! {
    // Go: server_completion_test.go:131 TestCompletionWithConcurrentFileClose
    fn completion_with_concurrent_file_close() {
        let client = init_completion_client(
            "/home/projects",
            &[
                ("/home/projects/tsconfig.json", TSCONFIG),
                ("/home/projects/a.ts", "export const someVar = 10;"),
                ("/home/projects/b.ts", "s"),
            ],
        );

        let a_uri = lsconv::file_name_to_document_uri("/home/projects/a.ts");
        let b_uri = lsconv::file_name_to_document_uri("/home/projects/b.ts");
        open(&client, &a_uri, "export const someVar = 10;");
        open(&client, &b_uri, "s");

        let wait_for_completion =
            client.send_request_async(&lsproto::TEXT_DOCUMENT_COMPLETION_INFO, completion_params(&b_uri, 0, 1));

        close(&client, &b_uri);

        let (msg, resp) = wait_for_completion();
        assert_some_var_auto_import(&msg, resp, "someVar");
    }
}

child_test! {
    // Go: server_completion_test.go:176 TestCompletionForUnopenedFile
    fn completion_for_unopened_file() {
        let client = init_completion_client(
            "/home/projects",
            &[
                ("/home/projects/tsconfig.json", TSCONFIG),
                ("/home/projects/c.ts", "let xyz = 1;\nxy"),
            ],
        );

        let c_uri = lsconv::file_name_to_document_uri("/home/projects/c.ts");
        let (msg, resp) = client.send_request(&lsproto::TEXT_DOCUMENT_COMPLETION_INFO, completion_params(&c_uri, 1, 2));
        assert!(msg.error.is_none(), "{:?}", msg.error);
        assert!(find_completion_item(&completion_items(resp), "xyz").is_some());
    }
}

child_test! {
    // Go: server_completion_test.go:200 TestAutoImportCompletionForUnopenedFile
    fn auto_import_completion_for_unopened_file() {
        let client = init_completion_client(
            "/home/projects",
            &[
                ("/home/projects/tsconfig.json", TSCONFIG),
                ("/home/projects/a.ts", "export const someVar = 10;"),
                ("/home/projects/c.ts", "s"),
            ],
        );

        let c_uri = lsconv::file_name_to_document_uri("/home/projects/c.ts");
        let (msg, resp) = client.send_request(&lsproto::TEXT_DOCUMENT_COMPLETION_INFO, completion_params(&c_uri, 0, 1));
        assert_some_var_auto_import(&msg, resp, "someVar");
    }
}

child_test! {
    // Go: server_completion_test.go:235 TestCompletionSnapshotFreezing
    fn completion_snapshot_freezing() {
        let client = init_completion_client(
            "/home/projects",
            &[
                ("/home/projects/tsconfig.json", TSCONFIG),
                ("/home/projects/a.ts", "export const someVar = 10;"),
                ("/home/projects/b.ts", "someV"),
            ],
        );

        let a_uri = lsconv::file_name_to_document_uri("/home/projects/a.ts");
        let b_uri = lsconv::file_name_to_document_uri("/home/projects/b.ts");
        open(&client, &a_uri, "export const someVar = 10;");
        open(&client, &b_uri, "someV");

        let wait_for_completion =
            client.send_request_async(&lsproto::TEXT_DOCUMENT_COMPLETION_INFO, completion_params(&b_uri, 0, 5));

        client.send_notification(
            &lsproto::TEXT_DOCUMENT_DID_CHANGE_INFO,
            lsproto::DidChangeTextDocumentParams {
                text_document: lsproto::VersionedTextDocumentIdentifier {
                    uri: b_uri.clone(),
                    version: 2,
                },
                content_changes: vec![lsproto::TextDocumentContentChangePartialOrWholeDocument {
                    partial: None,
                    whole_document: Some(lsproto::TextDocumentContentChangeWholeDocument {
                        text: "notMatching".to_string(),
                    }),
                }],
            },
        );

        let (msg, resp) = wait_for_completion();
        assert_some_var_auto_import(
            &msg,
            resp,
            "expected someVar in completions (snapshot freezing should preserve original content)",
        );
    }
}
