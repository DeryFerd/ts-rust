//! Port of Go `internal/lsp/server_progress_test.go`.

use std::sync::{Arc, Mutex, mpsc::sync_channel};
use std::time::Duration;

use ts_goport::lsp::lsproto;

use super::lsptestutil::{self, result_response};
use super::projecttestutil::files;
use super::util::uri;

// Go: server_progress_test.go:129 tokenString
fn token_string(t: &lsproto::IntegerOrString) -> String {
    t.string.clone().unwrap_or_default()
}

child_test! {
    // Go: server_progress_test.go:17 TestProgressNotificationsEndToEnd
    fn progress_notifications_end_to_end() {
        // Collect $/progress notifications. Signal when "end" arrives.
        let progress_notifications: Arc<Mutex<Vec<lsproto::ProgressParams>>> = Arc::default();
        let (end_tx, end_rx) = sync_channel::<()>(1);

        let on_server_request: lsptestutil::ServerRequestHandler = Arc::new(|req| {
            if req.method == lsproto::Method::CLIENT_REGISTER_CAPABILITY
                || req.method == lsproto::Method::CLIENT_UNREGISTER_CAPABILITY
                || req.method == lsproto::Method::WINDOW_WORK_DONE_PROGRESS_CREATE
            {
                return Some(result_response(req, Box::new(lsproto::Null)));
            }
            None
        });

        let collected = progress_notifications.clone();
        let on_server_notification: lsptestutil::ServerNotificationHandler = Arc::new(move |req| {
            if req.method == lsproto::Method::PROGRESS {
                if let Some(params) = req
                    .params
                    .as_deref()
                    .and_then(|p| (p as &dyn std::any::Any).downcast_ref::<lsproto::ProgressParams>())
                {
                    let is_end = params.value.end.is_some();
                    collected
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .push(params.clone());
                    if is_end {
                        // Signal once; later ends are dropped.
                        let _ = end_tx.try_send(());
                    }
                }
            }
        });

        let mut client = lsptestutil::new_lsp_client(
            lsptestutil::server_setup(
                "/home/projects",
                files(&[
                    ("/home/projects/tsconfig.json", "{}"),
                    ("/home/projects/index.ts", "export const x = 1;"),
                ]),
            ),
            Some(on_server_request),
            Some(on_server_notification),
        );

        let (init_msg, _) = client.send_request(
            &lsproto::INITIALIZE_INFO,
            lsproto::InitializeParams {
                capabilities: Some(lsproto::ClientCapabilities {
                    window: Some(lsproto::WindowClientCapabilities {
                        work_done_progress: Some(true),
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
                ..Default::default()
            },
        );
        assert!(init_msg.error.is_none(), "Initialize failed");
        client.send_notification(&lsproto::INITIALIZED_INFO, lsproto::InitializedParams::default());

        let u = uri("file:///home/projects/index.ts");
        client.send_notification(
            &lsproto::TEXT_DOCUMENT_DID_OPEN_INFO,
            lsproto::DidOpenTextDocumentParams {
                text_document: Some(lsproto::TextDocumentItem {
                    uri: u.clone(),
                    language_id: lsproto::LanguageKind::TYPE_SCRIPT,
                    text: "export const x = 1;".to_string(),
                    ..Default::default()
                }),
            },
        );

        // Send a request to ensure the server has processed the didOpen and loaded the project.
        let (msg, resp) = client.send_request(
            &lsproto::CUSTOM_PROJECT_INFO_INFO,
            lsproto::ProjectInfoParams {
                text_document: lsproto::TextDocumentIdentifier { uri: u },
            },
        );
        assert!(msg.error.is_none(), "{:?}", msg.error);
        let resp = resp.expect("expected a response").expect("project info");
        assert_eq!(resp.config_file_path, "/home/projects/tsconfig.json");

        // Wait for the "end" progress notification before reading.
        end_rx
            .recv_timeout(Duration::from_secs(60))
            .expect("timed out waiting for progress end notification");

        let notifications = progress_notifications
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();

        assert!(
            notifications.len() >= 2,
            "expected at least begin+end progress notifications, got {}",
            notifications.len()
        );

        // First notification should be a "begin".
        let begin = notifications[0]
            .value
            .begin
            .as_ref()
            .expect("expected first progress notification to be 'begin'");
        assert_eq!(begin.title, "Loading");

        // Last notification should be an "end".
        let last = notifications.last().unwrap();
        assert!(last.value.end.is_some(), "expected last progress notification to be 'end'");

        // All notifications should share the same token.
        let first_token = token_string(&notifications[0].token);
        assert!(!first_token.is_empty(), "expected non-empty progress token");
        for (i, n) in notifications.iter().enumerate() {
            assert_eq!(token_string(&n.token), first_token, "notification {i} has different token");
        }

        client.close().unwrap_or_else(|err| panic!("{}", err.error()));
    }
}
