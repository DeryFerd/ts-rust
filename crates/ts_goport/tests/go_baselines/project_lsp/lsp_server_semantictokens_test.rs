//! Port of Go `internal/lsp/server_semantictokens_test.go`.

use std::sync::Arc;

use ts_goport::lsp::lsproto;

use super::lsptestutil::{self, result_response};
use super::projecttestutil::files;
use super::util::uri;

child_test! {
    // Go: server_semantictokens_test.go:23 TestSemanticTokensCRLF
    fn semantic_tokens_crlf() {
        // Enough lines so the cumulative \r\n vs \n offset difference
        // causes an LF-based position to land on a \r in the CRLF text.
        let file_on_disk = "var x\nvar x\nvar x\nvar x\nvar x\nvar x\nconst a = 1\n";
        let file_from_editor = file_on_disk.replace('\n', "\r\n");

        let on_server_request: lsptestutil::ServerRequestHandler = Arc::new(|req| {
            if req.method == lsproto::Method::CLIENT_REGISTER_CAPABILITY
                || req.method == lsproto::Method::CLIENT_UNREGISTER_CAPABILITY
            {
                return Some(result_response(req, Box::new(lsproto::Null)));
            }
            None
        });

        let client = lsptestutil::new_lsp_client(
            lsptestutil::server_setup(
                "/home/projects",
                files(&[
                    ("/home/projects/tsconfig.json", "{}"),
                    ("/home/projects/test.ts", file_on_disk),
                    ("/home/projects/other.ts", "export {}"),
                ]),
            ),
            Some(on_server_request),
            None,
        );

        let strings = |items: &[&str]| items.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        let (init_msg, _) = client.send_request(
            &lsproto::INITIALIZE_INFO,
            lsproto::InitializeParams {
                capabilities: Some(lsproto::ClientCapabilities {
                    text_document: Some(lsproto::TextDocumentClientCapabilities {
                        semantic_tokens: Some(lsproto::SemanticTokensClientCapabilities {
                            token_types: strings(&[
                                "namespace", "type", "class", "enum", "interface", "struct", "typeParameter",
                                "parameter", "variable", "property", "enumMember", "event", "function", "method",
                                "macro", "keyword", "modifier", "comment", "string", "number", "regexp", "operator",
                                "decorator",
                            ]),
                            token_modifiers: strings(&[
                                "declaration", "definition", "readonly", "static", "deprecated", "abstract", "async",
                                "modification", "documentation", "defaultLibrary", "local",
                            ]),
                            ..Default::default()
                        }),
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
                ..Default::default()
            },
        );
        assert!(init_msg.error.is_none(), "Initialize failed");
        client.send_notification(&lsproto::INITIALIZED_INFO, lsproto::InitializedParams::default());

        let open = |u: &lsproto::DocumentUri, text: &str| {
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
        };

        // Open another project file to force the project to load test.ts from disk (LF).
        let other_uri = uri("file:///home/projects/other.ts");
        open(&other_uri, "export {}");
        let (msg1, _) = client.send_request(
            &lsproto::TEXT_DOCUMENT_SEMANTIC_TOKENS_FULL_INFO,
            lsproto::SemanticTokensParams {
                text_document: lsproto::TextDocumentIdentifier { uri: other_uri },
                ..Default::default()
            },
        );
        assert!(msg1.error.is_none(), "Initial request failed");

        // Open test.ts with CRLF content; the project already parsed it from disk (LF).
        let u = uri("file:///home/projects/test.ts");
        open(&u, &file_from_editor);

        let (msg, _) = client.send_request(
            &lsproto::TEXT_DOCUMENT_SEMANTIC_TOKENS_FULL_INFO,
            lsproto::SemanticTokensParams {
                text_document: lsproto::TextDocumentIdentifier { uri: u },
                ..Default::default()
            },
        );
        if let Some(err) = &msg.error {
            panic!("Semantic tokens request failed: {}", err.message);
        }
    }
}
