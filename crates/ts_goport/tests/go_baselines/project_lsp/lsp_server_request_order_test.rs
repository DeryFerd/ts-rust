//! Port-only tests (no Go test file): where the background tasks that a
//! request queues land among the server's messages
//! (`project::background::race`). Only the orders that do not depend on a
//! Go race are tested.

use std::sync::mpsc::Receiver;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, Instant};

use ts_goport::jsonrpc;
use ts_goport::ls::lsconv;
use ts_goport::lsp::lsproto;

use super::lsptestutil::{self, LspClient, result_response};
use super::projecttestutil::files;

/// The messages that the client saw, in the order the router passed them
/// on: `register <globs>` for each watch registration, and `answer` for
/// the answer in `answer_rx`, each with the time it was logged.
#[derive(Default)]
struct Seen {
    log: Vec<String>,
    times: Vec<Instant>,
    /// The client stops replying to watch registrations: its reply has an
    /// ID that the server did not send, which the server drops.
    swallow_watches: bool,
    /// The channel of the answer to watch, set while the request is sent.
    answer_rx: Option<Receiver<lsproto::ResponseMessage>>,
    answer: Option<lsproto::ResponseMessage>,
}

impl Seen {
    /// Logs `answer` once the router has put the answer in its channel.
    fn take_answer(&mut self) -> bool {
        if self.answer.is_none()
            && let Some(resp) = self.answer_rx.as_ref().and_then(|rx| rx.try_recv().ok())
        {
            self.answer = Some(resp);
            self.push("answer".to_string());
        }
        self.answer.is_some()
    }

    fn push(&mut self, entry: String) {
        self.log.push(entry);
        self.times.push(Instant::now());
    }
}

fn lock(seen: &Mutex<Seen>) -> std::sync::MutexGuard<'_, Seen> {
    seen.lock().unwrap_or_else(PoisonError::into_inner)
}

fn glob_text(glob: &lsproto::PatternOrRelativePattern) -> String {
    match (&glob.pattern, &glob.relative_pattern) {
        (Some(pattern), _) => pattern.clone(),
        (None, Some(relative)) => format!("{:?} {}", relative.base_uri, relative.pattern),
        (None, None) => String::new(),
    }
}

/// A client with dynamic watch registration that logs each watch
/// registration in `seen`. Before it logs one, it logs the watched answer
/// if the router has passed it on, so the log has the router's order.
fn init_watching_client(entries: &[(&str, &str)], seen: &Arc<Mutex<Seen>>) -> LspClient {
    let on_server_request: lsptestutil::ServerRequestHandler = {
        let seen = seen.clone();
        Arc::new(move |req| {
            if req.method == lsproto::Method::CLIENT_REGISTER_CAPABILITY {
                let params = lsproto::unmarshal_params::<lsproto::RegistrationParams>(req)
                    .unwrap_or_else(|err| panic!("RegistrationParams: {}", err.error()));
                let mut seen = lock(&seen);
                seen.take_answer();
                for registration in params.registrations {
                    let Some(options) = registration
                        .register_options
                        .and_then(|options| options.workspace_did_change_watched_files)
                    else {
                        continue;
                    };
                    let globs: Vec<String> = options
                        .watchers
                        .iter()
                        .map(|w| glob_text(&w.glob_pattern))
                        .collect();
                    seen.push(format!("register {}", globs.join(" ")));
                }
                let mut resp = result_response(req, Box::new(lsproto::Null));
                if seen.swallow_watches {
                    resp.id = Some(jsonrpc::new_id_string("no-such-request"));
                }
                return Some(resp);
            }
            if req.method == lsproto::Method::CLIENT_UNREGISTER_CAPABILITY
                || req.method == lsproto::Method::WORKSPACE_CONFIGURATION
            {
                return Some(result_response(req, Box::new(lsproto::Null)));
            }
            None
        })
    };
    let client = lsptestutil::new_lsp_client(
        lsptestutil::server_setup("/home/user/work/app", files(entries)),
        Some(on_server_request),
        None,
    );
    let (init_msg, _) = client.send_request(
        &lsproto::INITIALIZE_INFO,
        lsproto::InitializeParams {
            capabilities: Some(lsproto::ClientCapabilities {
                workspace: Some(lsproto::WorkspaceClientCapabilities {
                    did_change_watched_files: Some(
                        lsproto::DidChangeWatchedFilesClientCapabilities {
                            dynamic_registration: Some(true),
                            relative_pattern_support: Some(true),
                        },
                    ),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            ..Default::default()
        },
    );
    assert!(init_msg.error.is_none(), "Initialize failed");
    client.send_notification(
        &lsproto::INITIALIZED_INFO,
        lsproto::InitializedParams::default(),
    );
    client
}

const INDEX: &str = "/home/user/work/app/index.ts";

/// Hovers `x` in index.ts and checks that the answer is not an error.
fn hover(client: &LspClient) {
    let (msg, _) = client.send_request(
        &lsproto::TEXT_DOCUMENT_HOVER_INFO,
        lsproto::HoverParams {
            text_document: lsproto::TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(INDEX),
            },
            position: lsproto::Position {
                line: 0,
                character: 13,
            },
            ..Default::default()
        },
    );
    assert!(msg.error.is_none(), "{:?}", msg.error);
}

/// Starts a watching client on a project with index.ts, opens index.ts,
/// and changes it to import a file outside the project directory, so the
/// snapshot that the next request builds watches that directory. Returns
/// the client and the length of the log before the change.
fn open_and_import_outside(seen: &Arc<Mutex<Seen>>) -> (LspClient, usize) {
    let client = init_watching_client(
        &[
            ("/home/user/work/app/tsconfig.json", "{}"),
            (INDEX, "export const x = 1;\n"),
            ("/home/user/work/app/other.ts", "export const y = 2;\n"),
            ("/home/user/shared/z.ts", "export const z = 3;\n"),
        ],
        seen,
    );
    let index = lsconv::file_name_to_document_uri(INDEX);
    client.send_notification(
        &lsproto::TEXT_DOCUMENT_DID_OPEN_INFO,
        lsproto::DidOpenTextDocumentParams {
            text_document: Some(lsproto::TextDocumentItem {
                uri: index.clone(),
                language_id: lsproto::LanguageKind::TYPE_SCRIPT,
                version: 1,
                text: "export const x = 1;\n".to_string(),
                ..Default::default()
            }),
        },
    );
    hover(&client);
    let before = lock(seen).log.len();

    // An import of a file outside the project directory: the next
    // snapshot watches its directory.
    client.send_notification(
        &lsproto::TEXT_DOCUMENT_DID_CHANGE_INFO,
        lsproto::DidChangeTextDocumentParams {
            text_document: lsproto::VersionedTextDocumentIdentifier {
                uri: index,
                version: 2,
            },
            content_changes: vec![lsproto::TextDocumentContentChangePartialOrWholeDocument {
                partial: None,
                whole_document: Some(lsproto::TextDocumentContentChangeWholeDocument {
                    text: "import { z } from \"../../shared/z\";\nexport const x = z;\n"
                        .to_string(),
                }),
            }],
        },
    );
    (client, before)
}

/// The params of a willRenameFiles of other.ts.
fn rename_other() -> lsproto::RenameFilesParams {
    lsproto::RenameFilesParams {
        files: vec![Some(lsproto::FileRename {
            old_uri: lsconv::file_name_to_document_uri("/home/user/work/app/other.ts"),
            new_uri: lsconv::file_name_to_document_uri("/home/user/work/app/other2.ts"),
        })],
    }
}

/// Sends `info` and waits for its answer, which `seen` logs in the
/// router's order.
fn send_watched<P: ts_goport::frontend::json_ext::AnyValue, R>(
    client: &LspClient,
    seen: &Mutex<Seen>,
    info: &lsproto::RequestInfo<P, R>,
    params: P,
) -> lsproto::ResponseMessage {
    {
        // The lock holds a registration that comes before the channel is set.
        let mut guard = lock(seen);
        let id = jsonrpc::new_id_int(client.next_id());
        let req = info.new_request_message(Some(id.clone()), params);
        guard.answer_rx = Some(client.send_request_message(req, id));
    }
    let deadline = Instant::now() + Duration::from_secs(120);
    loop {
        {
            let mut guard = lock(seen);
            if guard.take_answer() {
                guard.answer_rx = None;
                return guard.answer.take().expect("the answer");
            }
        }
        assert!(Instant::now() < deadline, "no answer to {}", info.method.0);
        std::thread::sleep(Duration::from_millis(1));
    }
}

child_test! {
    // PORT: no Go counterpart (editfuzz3 K2). A request with no async part
    // runs the background tasks of its snapshot update before its answer:
    // Go runs them on goroutines while the handler works, so the new watch
    // that a change needs is registered before the answer of the
    // willRenameFiles (or rename) that picks up the change. The port sent it
    // after the answer, at the end of the message.
    fn will_rename_files_registers_new_watches_before_its_answer() {
        let seen: Arc<Mutex<Seen>> = Arc::default();
        let (client, before) = open_and_import_outside(&seen);
        let msg = send_watched(
            &client,
            &seen,
            &lsproto::WORKSPACE_WILL_RENAME_FILES_INFO,
            rename_other(),
        );
        assert!(msg.error.is_none(), "{:?}", msg.error);
        // The tasks of the port's message boundary have run when the next
        // answer comes.
        hover(&client);

        let log = lock(&seen).log[before..].to_vec();
        let answer = log.iter().position(|m| m == "answer").expect("the answer is logged");
        assert!(
            log[..answer].iter().any(|m| m.starts_with("register ")),
            "no watch registration before the answer: {log:?}"
        );
        assert!(
            !log[answer..].iter().any(|m| m.starts_with("register ")),
            "a watch registration after the answer: {log:?}"
        );
    }
}

child_test! {
    // PORT: no Go counterpart (followups20 skeptic). A request that builds
    // no checker answers before the snapshot task that it starts: Go's
    // handler (here rename at the `export` keyword, which needs no
    // checker, ls/rename.go:89) ends before the task's goroutine reaches
    // its registerCapability.
    fn a_request_with_no_checker_build_answers_before_its_new_watches() {
        let seen: Arc<Mutex<Seen>> = Arc::default();
        let (client, before) = open_and_import_outside(&seen);
        let msg = send_watched(
            &client,
            &seen,
            &lsproto::TEXT_DOCUMENT_RENAME_INFO,
            lsproto::RenameParams {
                text_document: lsproto::TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(INDEX),
                },
                position: lsproto::Position { line: 1, character: 0 },
                new_name: "xx".to_string(),
                ..Default::default()
            },
        );
        assert!(msg.error.is_none(), "{:?}", msg.error);
        hover(&client);

        let log = lock(&seen).log[before..].to_vec();
        let answer = log.iter().position(|m| m == "answer").expect("the answer is logged");
        assert!(
            !log[..answer].iter().any(|m| m.starts_with("register ")),
            "a watch registration before the answer: {log:?}"
        );
        assert!(
            log[answer..].iter().any(|m| m.starts_with("register ")),
            "no watch registration after the answer: {log:?}"
        );
    }
}

child_test! {
    // PORT: no Go counterpart (followups20 skeptic). The same for a request
    // with an async part (foldingRange, which needs no checker): the task
    // runs before the async part but sends its registerCapability only
    // after the answer, as Go's goroutine reaches it after the handler.
    fn an_async_request_with_no_checker_build_answers_before_its_new_watches() {
        let seen: Arc<Mutex<Seen>> = Arc::default();
        let (client, before) = open_and_import_outside(&seen);
        let msg = send_watched(
            &client,
            &seen,
            &lsproto::TEXT_DOCUMENT_FOLDING_RANGE_INFO,
            lsproto::FoldingRangeParams {
                text_document: lsproto::TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(INDEX),
                },
                ..Default::default()
            },
        );
        assert!(msg.error.is_none(), "{:?}", msg.error);
        hover(&client);

        let log = lock(&seen).log[before..].to_vec();
        let answer = log.iter().position(|m| m == "answer").expect("the answer is logged");
        assert!(
            !log[..answer].iter().any(|m| m.starts_with("register ")),
            "a watch registration before the answer: {log:?}"
        );
        assert!(
            log[answer..].iter().any(|m| m.starts_with("register ")),
            "no watch registration after the answer: {log:?}"
        );
    }
}

child_test! {
    // PORT: no Go counterpart (followups20 skeptic). An answer does not
    // wait for the client's reply to a registerCapability of the snapshot
    // task: in Go the task waits on its own goroutine. Here the client
    // stops replying after the setup, so the task's call ends only at its
    // 1 s timeout (`WATCH_REQUEST_TIMEOUT`); the willRenameFiles answer
    // comes right after the registration, not after the timeout.
    fn an_answer_does_not_wait_for_the_reply_to_a_new_watch() {
        let seen: Arc<Mutex<Seen>> = Arc::default();
        let (client, before) = open_and_import_outside(&seen);
        lock(&seen).swallow_watches = true;
        let msg = send_watched(
            &client,
            &seen,
            &lsproto::WORKSPACE_WILL_RENAME_FILES_INFO,
            rename_other(),
        );
        assert!(msg.error.is_none(), "{:?}", msg.error);

        let (log, times) = {
            let seen = lock(&seen);
            (seen.log[before..].to_vec(), seen.times[before..].to_vec())
        };
        let answer = log.iter().position(|m| m == "answer").expect("the answer is logged");
        let register = log[..answer]
            .iter()
            .position(|m| m.starts_with("register "))
            .unwrap_or_else(|| panic!("no watch registration before the answer: {log:?}"));
        let wait = times[answer].duration_since(times[register]);
        assert!(
            wait < Duration::from_millis(500),
            "the answer came {wait:?} after the registration: {log:?}"
        );
    }
}
