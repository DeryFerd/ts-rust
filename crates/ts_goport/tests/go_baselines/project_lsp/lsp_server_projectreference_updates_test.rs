//! Port of Go `internal/lsp/server_projectreference_updates_test.go`.

use ts_goport::ls::lsconv;
use ts_goport::lsp::lsproto;

use super::lsp_server_completion_test::init_completion_client;

child_test! {
    // Go: server_projectreference_updates_test.go:67 TestReferencesAfterAncestorProjectConfigDeletion1
    fn references_after_ancestor_project_config_deletion1() {
        // Go: initMutableLSPClient (server_projectreference_updates_test.go:19) is
        // initCompletionClient with Cwd "/root" and the map FS kept for edits.
        let client = init_completion_client(
            "/root",
            &[
                (
                    "/root/tsconfig.json",
                    r#"{
			"files": [],
			"references": [{ "path": "./project" }]
		}"#,
                ),
                (
                    "/root/project/tsconfig.json",
                    r#"{
			"compilerOptions": { "composite": true },
			"include": ["src/**/*.ts"]
		}"#,
                ),
                ("/root/project/src/main.ts", "export function helloWorld() {}\nhelloWorld()\n"),
            ],
        );
        let fs = super::projecttestutil::current_map_fs_for_test();

        let main_uri = lsconv::file_name_to_document_uri("/root/project/src/main.ts");
        client.send_notification(
            &lsproto::TEXT_DOCUMENT_DID_OPEN_INFO,
            lsproto::DidOpenTextDocumentParams {
                text_document: Some(lsproto::TextDocumentItem {
                    uri: main_uri.clone(),
                    language_id: lsproto::LanguageKind::TYPE_SCRIPT,
                    text: "export function helloWorld() {}\nhelloWorld()\n".to_string(),
                    ..Default::default()
                }),
            },
        );

        // Prime the child project so opening a file creates the ancestor configured-project placeholder.
        let (msg, _) = client.send_request(
            &lsproto::TEXT_DOCUMENT_DOCUMENT_SYMBOL_INFO,
            lsproto::DocumentSymbolParams {
                text_document: lsproto::TextDocumentIdentifier { uri: main_uri.clone() },
                ..Default::default()
            },
        );
        assert!(msg.error.is_none(), "{:?}", msg.error);

        fs.remove("root/tsconfig.json").unwrap();
        client.send_notification(
            &lsproto::WORKSPACE_DID_CHANGE_WATCHED_FILES_INFO,
            lsproto::DidChangeWatchedFilesParams {
                changes: vec![Some(lsproto::FileEvent {
                    uri: lsconv::file_name_to_document_uri("/root/tsconfig.json"),
                    type_: lsproto::FileChangeType::DELETED,
                })],
            },
        );

        let (msg, resp) = client.send_request(
            &lsproto::TEXT_DOCUMENT_REFERENCES_INFO,
            lsproto::ReferenceParams {
                text_document: lsproto::TextDocumentIdentifier { uri: main_uri.clone() },
                position: lsproto::Position { line: 1, character: 3 },
                context: Some(lsproto::ReferenceContext {
                    include_declaration: true,
                }),
                ..Default::default()
            },
        );
        assert!(msg.error.is_none(), "{:?}", msg.error);
        let locations = resp.expect("expected response").locations.expect("resp.Locations");
        assert_eq!(locations.len(), 2);
        let location = |sl, sc, el, ec| lsproto::Location {
            uri: main_uri.clone(),
            range: lsproto::Range {
                start: lsproto::Position { line: sl, character: sc },
                end: lsproto::Position { line: el, character: ec },
            },
        };
        assert_eq!(locations, vec![location(0, 16, 0, 26), location(1, 0, 1, 10)]);
    }
}
