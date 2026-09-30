//! Port of Go `internal/lsp/server_contentmapper_test.go` (tsgo#4712).
//!
//! PORT: Go `<-client.Server.InitComplete()` has no port (see
//! `lsptestutil`). Go `<-unregisteredSignal` waits up to 120 s here, the
//! request timeout of `lsptestutil`.

use std::collections::BTreeMap;
use std::sync::mpsc::sync_channel;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use ts_goport::frontend::json_ext::LspAny;
use ts_goport::frontend::vfs::Fs;
use ts_goport::lsp::lsproto;

use super::lsptestutil::{self, result_response};
use super::projecttestutil::{self, files};
use super::util::uri;
use crate::support::contentmappertest;

// Go: server_contentmapper_test.go:26 component
const COMPONENT: &str = r#"<component name="ProfileCard">
<template><h1>{{ title }}</h1></template>
<script lang="ts">
export const title = "Profile";
</script>"#;

/// The `**/*.vue` pattern of the first document filter of a registration's
/// document selector.
fn first_selector_pattern(selector: &lsproto::DocumentSelectorOrNull) -> Option<&str> {
    let filters = selector.document_selector.as_ref()?;
    assert_eq!(filters.len(), 1);
    filters[0]
        .pattern
        .as_ref()
        .and_then(|pattern| pattern.pattern.pattern.as_deref())
}

/// Go `lsproto.TextDocumentIdentifier{Uri: uri}`.
fn document(u: &lsproto::DocumentUri) -> lsproto::TextDocumentIdentifier {
    lsproto::TextDocumentIdentifier { uri: u.clone() }
}

child_test! {
    // Go: server_contentmapper_test.go:19 TestSetContentMapperContributionsBeforeDidOpen
    // PORT: Go `bundled.Embedded` is always true in the port, so the skip is dropped.
    fn set_content_mapper_contributions_before_did_open() {
        let mapper = contentmappertest::package_json(contentmappertest::COMPONENT_MAPPER);
        let file_map = files(&[
            (
                "/home/project/tsconfig.json",
                r#"{
			"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler", "strict": true },
			"contentMappers": [ { "package": "mapper", "extensions": [".vue"] } ]
		}"#,
            ),
            ("/home/project/node_modules/mapper/package.json", mapper.as_str()),
            ("/home/project/ProfileCard.vue", COMPONENT),
        ]);

        let registrations: Arc<Mutex<Vec<lsproto::Registration>>> = Arc::default();
        let unregistrations: Arc<Mutex<Vec<lsproto::Unregistration>>> = Arc::default();
        let (unregistered_tx, unregistered_rx) = sync_channel::<()>(1);
        let on_server_request: lsptestutil::ServerRequestHandler = {
            let registrations = registrations.clone();
            let unregistrations = unregistrations.clone();
            Arc::new(move |req| {
                if req.method == lsproto::Method::WORKSPACE_CONFIGURATION {
                    return Some(result_response(
                        req,
                        Box::new(vec![LspAny::Null, LspAny::Null, LspAny::Null, LspAny::Null]),
                    ));
                }
                if req.method == lsproto::Method::CLIENT_REGISTER_CAPABILITY {
                    let params = lsproto::unmarshal_params::<lsproto::RegistrationParams>(req)
                        .unwrap_or_else(|err| panic!("RegistrationParams: {}", err.error()));
                    registrations
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .extend(params.registrations);
                    return Some(result_response(req, Box::new(lsproto::Null)));
                }
                if req.method == lsproto::Method::CLIENT_UNREGISTER_CAPABILITY {
                    let params = lsproto::unmarshal_params::<lsproto::UnregistrationParams>(req)
                        .unwrap_or_else(|err| panic!("UnregistrationParams: {}", err.error()));
                    unregistrations
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .extend(params.unregisterations);
                    let _ = unregistered_tx.try_send(());
                    return Some(result_response(req, Box::new(lsproto::Null)));
                }
                None
            })
        };

        let mut setup = lsptestutil::server_setup("/home/project", file_map);
        setup.spawner = Some(contentmappertest::new_spawner);
        let fs = projecttestutil::current_map_fs_for_test().fs();
        let client = lsptestutil::new_lsp_client(setup, Some(on_server_request), None);

        let caps = lsproto::ClientCapabilities {
            workspace: Some(lsproto::WorkspaceClientCapabilities {
                file_operations: Some(lsproto::FileOperationClientCapabilities {
                    dynamic_registration: Some(true),
                    will_rename: Some(true),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            text_document: Some(lsproto::TextDocumentClientCapabilities {
                synchronization: Some(lsproto::TextDocumentSyncClientCapabilities {
                    dynamic_registration: Some(true),
                    ..Default::default()
                }),
                document_symbol: Some(lsproto::DocumentSymbolClientCapabilities {
                    dynamic_registration: Some(true),
                    ..Default::default()
                }),
                folding_range: Some(lsproto::FoldingRangeClientCapabilities {
                    dynamic_registration: Some(true),
                    ..Default::default()
                }),
                selection_range: Some(lsproto::SelectionRangeClientCapabilities {
                    dynamic_registration: Some(true),
                }),
                inlay_hint: Some(lsproto::InlayHintClientCapabilities {
                    dynamic_registration: Some(true),
                    ..Default::default()
                }),
                code_lens: Some(lsproto::CodeLensClientCapabilities {
                    dynamic_registration: Some(true),
                    ..Default::default()
                }),
                code_action: Some(lsproto::CodeActionClientCapabilities {
                    dynamic_registration: Some(true),
                    ..Default::default()
                }),
                formatting: Some(lsproto::DocumentFormattingClientCapabilities {
                    dynamic_registration: Some(true),
                }),
                range_formatting: Some(lsproto::DocumentRangeFormattingClientCapabilities {
                    dynamic_registration: Some(true),
                    ..Default::default()
                }),
                on_type_formatting: Some(lsproto::DocumentOnTypeFormattingClientCapabilities {
                    dynamic_registration: Some(true),
                }),
                linked_editing_range: Some(lsproto::LinkedEditingRangeClientCapabilities {
                    dynamic_registration: Some(true),
                }),
                call_hierarchy: Some(lsproto::CallHierarchyClientCapabilities {
                    dynamic_registration: Some(true),
                }),
                semantic_tokens: Some(lsproto::SemanticTokensClientCapabilities {
                    dynamic_registration: Some(true),
                    requests: Some(lsproto::ClientSemanticTokensRequestOptions::default()),
                    token_types: Vec::new(),
                    token_modifiers: Vec::new(),
                    formats: vec![lsproto::TokenFormat::RELATIVE],
                    ..Default::default()
                }),
                ..Default::default()
            }),
            ..Default::default()
        };
        let (init_msg, init_result) = client.send_request(
            &lsproto::INITIALIZE_INFO,
            lsproto::InitializeParams {
                capabilities: Some(caps),
                initialization_options: Some(lsproto::InitializationOptionsOrNull {
                    initialization_options: Some(lsproto::InitializationOptions {
                        run_external_code: Some(true),
                        ..Default::default()
                    }),
                }),
                ..Default::default()
            },
        );
        assert!(
            init_result.is_some() && init_msg.error.is_none(),
            "initialize failed"
        );
        client.send_notification(&lsproto::INITIALIZED_INFO, lsproto::InitializedParams::default());

        let u = uri("file:///home/project/ProfileCard.vue");
        let (msg, result) = client.send_request(
            &lsproto::CUSTOM_SET_CONTENT_MAPPER_CONTRIBUTIONS_INFO,
            lsproto::SetContentMapperContributionsParams {
                open_documents: vec![document(&u)],
                contributions: vec![Some(lsproto::ContentMapperContribution {
                    contributor_id: "test".to_string(),
                    extensions: vec![".vue".to_string(), ".svelte".to_string()],
                    inferred_project_contribution: None,
                })],
            },
        );
        assert!(result.is_some() && msg.error.is_none());

        let registered = registrations
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        assert!(!registered.is_empty(), "expected dynamic registrations");
        let mut expected_mapper_registrations: BTreeMap<&str, bool> = [
            "content-mapper-did-open",
            "content-mapper-did-change",
            "content-mapper-did-close",
            "content-mapper-semantic-tokens",
            "content-mapper-document-symbol",
            "content-mapper-folding-range",
            "content-mapper-selection-range",
            "content-mapper-inlay-hint",
            "content-mapper-code-lens",
            "content-mapper-code-action",
            "content-mapper-formatting",
            "content-mapper-range-formatting",
            "content-mapper-on-type-formatting",
            "content-mapper-linked-editing",
            "content-mapper-call-hierarchy",
            "content-mapper-will-rename-files",
        ]
        .into_iter()
        .map(|id| (id, false))
        .collect();
        for registration in &registered {
            match expected_mapper_registrations.get_mut(registration.id.as_str()) {
                Some(found) => *found = true,
                None => assert!(
                    !registration.id.starts_with("content-mapper-"),
                    "unexpected unsupported content mapper registration {:?}",
                    registration.id
                ),
            }
            if registration.id == "content-mapper-did-open" {
                let options = registration
                    .register_options
                    .as_ref()
                    .and_then(|options| options.text_document_did_open.as_ref())
                    .expect("expected textDocument/didOpen register options");
                assert_eq!(
                    first_selector_pattern(&options.document_selector),
                    Some("**/*.vue")
                );
            }
            if registration.id == "content-mapper-semantic-tokens" {
                let options = registration
                    .register_options
                    .as_ref()
                    .and_then(|options| options.text_document_semantic_tokens.as_ref())
                    .expect("expected textDocument/semanticTokens register options");
                assert_eq!(
                    first_selector_pattern(&options.document_selector),
                    Some("**/*.vue")
                );
            }
        }
        for (id, found) in &expected_mapper_registrations {
            assert!(*found, "expected {id} registration for .vue");
        }

        client.send_notification(
            &lsproto::TEXT_DOCUMENT_DID_OPEN_INFO,
            lsproto::DidOpenTextDocumentParams {
                text_document: Some(lsproto::TextDocumentItem {
                    uri: u.clone(),
                    language_id: lsproto::LanguageKind("vue".into()),
                    version: 1,
                    text: COMPONENT.to_string(),
                }),
            },
        );
        let position = lsproto::Position {
            line: 3,
            character: 15,
        };
        let (hover_msg, hover) = client.send_request(
            &lsproto::TEXT_DOCUMENT_HOVER_INFO,
            lsproto::HoverParams {
                text_document: document(&u),
                position,
                ..Default::default()
            },
        );
        assert!(hover.is_some() && hover_msg.error.is_none());
        assert!(
            hover.is_some_and(|hover| hover.hover.is_some()),
            "expected hover after first foreign didOpen"
        );

        Fs::write_file(
            &*fs,
            "/home/project/tsconfig.json",
            r#"{
		"compilerOptions": { "target": "es2020", "module": "esnext", "moduleResolution": "bundler", "strict": true }
	}"#,
        )
        .unwrap_or_else(|err| panic!("WriteFile: {err:?}"));
        client.send_notification(
            &lsproto::WORKSPACE_DID_CHANGE_WATCHED_FILES_INFO,
            lsproto::DidChangeWatchedFilesParams {
                changes: vec![Some(lsproto::FileEvent {
                    uri: uri("file:///home/project/tsconfig.json"),
                    type_: lsproto::FileChangeType::CHANGED,
                })],
            },
        );
        let (hover_msg, hover) = client.send_request(
            &lsproto::TEXT_DOCUMENT_HOVER_INFO,
            lsproto::HoverParams {
                text_document: document(&u),
                position,
                ..Default::default()
            },
        );
        assert!(
            hover_msg.error.is_none(),
            "request before didClose should return a null result"
        );
        assert!(hover.is_none_or(|hover| hover.hover.is_none()));
        let (diagnostic_msg, diagnostics) = client.send_request(
            &lsproto::TEXT_DOCUMENT_DIAGNOSTIC_INFO,
            lsproto::DocumentDiagnosticParams {
                text_document: document(&u),
                ..Default::default()
            },
        );
        assert!(
            diagnostics.is_some() && diagnostic_msg.error.is_none(),
            "diagnostics before didClose should return an empty report"
        );
        let report = diagnostics
            .and_then(|diagnostics| diagnostics.full_document_diagnostic_report)
            .expect("expected a full document diagnostic report");
        assert!(report.items.is_empty());
        let (completion_msg, completion) = client.send_request(
            &lsproto::TEXT_DOCUMENT_COMPLETION_INFO,
            lsproto::CompletionParams {
                text_document: document(&u),
                position,
                ..Default::default()
            },
        );
        assert!(completion.is_some() && completion_msg.error.is_none());
        assert!(
            completion.is_some_and(|completion| completion.items.is_none() && completion.list.is_none())
        );
        let (references_msg, references) = client.send_request(
            &lsproto::TEXT_DOCUMENT_REFERENCES_INFO,
            lsproto::ReferenceParams {
                text_document: document(&u),
                position,
                context: Some(lsproto::ReferenceContext {
                    include_declaration: true,
                }),
                ..Default::default()
            },
        );
        assert!(references.is_some() && references_msg.error.is_none());
        assert!(references.is_some_and(|references| references.locations.is_none()));
        let (rename_msg, rename) = client.send_request(
            &lsproto::TEXT_DOCUMENT_RENAME_INFO,
            lsproto::RenameParams {
                text_document: document(&u),
                position,
                new_name: "renamed".to_string(),
                ..Default::default()
            },
        );
        assert!(rename.is_some() && rename_msg.error.is_none());
        assert!(rename.is_some_and(|rename| rename.workspace_edit.is_none()));
        unregistered_rx
            .recv_timeout(Duration::from_secs(120))
            .unwrap_or_else(|err| panic!("expected an unregistration: {err}"));
        let unregistered = unregistrations
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        assert!(!unregistered.is_empty(), "expected dynamic unregistration");
        let mut expected_unregistrations: BTreeMap<&str, bool> = expected_mapper_registrations
            .keys()
            .map(|id| (*id, false))
            .collect();
        for unregistration in &unregistered {
            match expected_unregistrations.get_mut(unregistration.id.as_str()) {
                Some(found) => *found = true,
                None => assert!(
                    !unregistration.id.starts_with("content-mapper-"),
                    "unexpected unsupported content mapper unregistration {:?}",
                    unregistration.id
                ),
            }
        }
        for (id, found) in &expected_unregistrations {
            assert!(*found, "expected {id} unregistration");
        }

        client.send_notification(
            &lsproto::TEXT_DOCUMENT_DID_CLOSE_INFO,
            lsproto::DidCloseTextDocumentParams {
                text_document: document(&u),
            },
        );
    }
}
