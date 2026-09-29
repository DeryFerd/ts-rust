//! Port of Go `internal/lsp/server_shutdown_test.go`.

use std::rc::Rc;
use std::sync::atomic::Ordering;
use std::sync::mpsc::sync_channel;
use std::time::Duration;

use ts_goport::frontend::bundled;
use ts_goport::gostd::{GoError, context, errors};
use ts_goport::lsp::{self, lsproto};
use ts_goport::project::{self, logging};

use super::projecttestutil;

// Go: server_shutdown_test.go:15 shutdownTestReader
struct ShutdownTestReader;

impl lsp::Reader for ShutdownTestReader {
    fn read(&mut self) -> (Option<lsproto::Message>, Option<GoError>) {
        (None, Some(errors::EOF.clone()))
    }
}

// Go: server_shutdown_test.go:19 shutdownTestWriter
struct ShutdownTestWriter;

impl lsp::Writer for ShutdownTestWriter {
    fn write(&mut self, _msg: &lsproto::Message) -> Result<(), GoError> {
        Ok(())
    }
}

fn server_options(
    cwd: &str,
    fs: Rc<dyn ts_goport::frontend::vfs::Fs>,
    default_library_path: String,
) -> lsp::ServerOptions {
    lsp::ServerOptions {
        in_: Box::new(ShutdownTestReader),
        out: Box::new(ShutdownTestWriter),
        err: Box::new(std::io::sink()),
        cwd: cwd.to_string(),
        fs,
        default_library_path,
        typings_location: String::new(),
        parse_cache: None,
        npm_install: None,
        spawn: None,
        progress_delay: Duration::ZERO,
        set_parent_process_id: None,
    }
}

child_test! {
    // Go: server_shutdown_test.go:24 TestServerShutdownNoDeadlock
    // TestServerShutdownNoDeadlock verifies that operations after shutdown
    // don't block.
    fn server_shutdown_no_deadlock() {
        let (_, fs) = projecttestutil::wrapped_map_fs(
            projecttestutil::files(&[("/test/tsconfig.json", "{}"), ("/test/index.ts", "const x = 1;")]),
            false,
        );

        let server = lsp::new_server(server_options("/test", fs.clone(), bundled::lib_path()));

        let (ctx, cancel) = context::with_cancel(&context::background());
        let _ = server.shared.background_ctx.set(ctx.clone());

        // Start write loop to drain queue
        let (write_loop_done_tx, write_loop_done) = sync_channel::<()>(1);
        let shared = server.shared.clone();
        let write_ctx = ctx.clone();
        std::thread::spawn(move || {
            let _ = shared.write_loop(&write_ctx, &mut ShutdownTestWriter);
            let _ = write_loop_done_tx.send(());
        });

        // Create session with the server's lifecycle context
        server.shared.init_started.store(true, Ordering::SeqCst);
        let logger: Rc<dyn logging::Logger> = Rc::new(server.logger.clone());
        let session = project::new_session(&project::SessionInit {
            background_ctx: ctx.clone(),
            options: Rc::new(project::SessionOptions {
                current_directory: "/test".to_string(),
                typings_location: String::new(),
                watch_enabled: false,
                logging_enabled: true,
                ..projecttestutil::session_options("/test")
            }),
            fs,
            client: None,
            logger: Some(logger),
            npm_executor: None,
            spawner: None,
            content_mapper_logger: None,
            parse_cache: None,
            content_mapped_parse_cache: None,
        });
        *server.session.borrow_mut() = Some(session.clone());

        // Open a file to establish a project
        session.did_open_file(
            &ctx,
            &lsproto::DocumentUri("file:///test/index.ts".to_string()),
            1,
            "const x = 1;",
            &lsproto::LanguageKind::TYPE_SCRIPT,
        );
        session.wait_for_background_tasks();

        // Shutdown (cancel context and wait for write loop to exit)
        cancel();
        write_loop_done
            .recv_timeout(Duration::from_secs(60))
            .expect("write loop did not exit");

        // Trigger operations that would log (these should not block)
        session.did_change_file(
            &ctx,
            &lsproto::DocumentUri("file:///test/index.ts".to_string()),
            2,
            &[lsproto::TextDocumentContentChangePartialOrWholeDocument {
                partial: None,
                whole_document: Some(lsproto::TextDocumentContentChangeWholeDocument {
                    text: "const x = 2;".to_string(),
                }),
            }],
        );
        let _ = session.get_language_service(&ctx, &lsproto::DocumentUri("file:///test/index.ts".to_string()));
        session.wait_for_background_tasks();

        session.close();
    }
}

// Go: server_shutdown_test.go:92 TestServerOutgoingQueueDoesNotBlockWithoutWriter
// PORT: the server needs a file system; the Go test leaves FS nil (it is
// not read). An empty map file system stands in for it. No program is
// built, so this test runs in the test process.
#[test]
fn server_outgoing_queue_does_not_block_without_writer() {
    let fs = crate::support::vfstest::from_map(Vec::<(String, String)>::new(), false);
    let server = lsp::new_server(server_options("/test", fs, String::new()));
    let (ctx, _cancel) = context::with_cancel(&context::background());
    let _ = server.shared.background_ctx.set(ctx);

    let shared = server.shared.clone();
    let (done_tx, done) = sync_channel::<Result<(), GoError>>(1);
    std::thread::spawn(move || {
        for _ in 0..1000 {
            let msg = lsproto::WINDOW_LOG_MESSAGE_INFO
                .new_notification_message(lsproto::LogMessageParams {
                    type_: lsproto::MessageType::INFO,
                    message: "queued".to_string(),
                })
                .message();
            if let Err(err) = shared.send(msg) {
                let _ = done_tx.send(Err(err));
                return;
            }
        }
        let _ = done_tx.send(Ok(()));
    });

    match done.recv_timeout(Duration::from_secs(60)) {
        Ok(Ok(())) => {}
        Ok(Err(err)) => panic!("{}", err.error()),
        Err(_) => panic!("sending outgoing messages blocked without a writer"),
    }
}

// Go: server_test.go:133 TestWriteLoopRecoversFromUnserializableResponse
// PORT: Go renamed `server_shutdown_test.go` to `server_test.go` (#4896);
// this file keeps its name. The Go bad result is a selection range 20000
// levels deep, which the Go JSON encoder rejects (jsontext
// `maxNestingDepth`). The port's JSON encoder has no nesting limit, so the
// bad result here is a value whose marshal fails. The test checks the same
// write loop behavior.
#[derive(Debug)]
struct UnserializableResult;

impl ts_goport::frontend::json::MarshalerTo for UnserializableResult {
    fn marshal_json_to(
        &self,
        _enc: &mut String,
    ) -> Result<(), ts_goport::frontend::json::JsonError> {
        Err(ts_goport::frontend::json::JsonError {
            message: "exceeded max depth".to_string(),
        })
    }
}

// A response that exceeds the JSON encoder's nesting limit must fail only its
// request. The write loop must remain available to deliver subsequent responses.
#[test]
fn write_loop_recovers_from_unserializable_response() {
    let (pr, pw) = std::io::pipe().expect("pipe");
    let fs = crate::support::vfstest::from_map(Vec::<(String, String)>::new(), false);
    let server = lsp::new_server(lsp::ServerOptions {
        in_: Box::new(ShutdownTestReader),
        out: lsp::to_writer(Box::new(pw)),
        err: Box::new(std::io::sink()),
        ..server_options("/test", fs, String::new())
    });

    let (ctx, cancel) = context::with_cancel(&context::background());
    let _ = server.shared.background_ctx.set(ctx.clone());

    let (write_loop_err_tx, write_loop_err) = sync_channel::<Result<(), GoError>>(1);
    let mut w = server.w.borrow_mut().take().expect("writer");
    let shared = server.shared.clone();
    let write_ctx = ctx.clone();
    std::thread::spawn(move || {
        let _ = write_loop_err_tx.send(shared.write_loop(&write_ctx, &mut *w));
    });

    let bad_id = ts_goport::jsonrpc::new_id_string("bad");
    if let Err(err) = server.shared.send(
        lsproto::ResponseMessage {
            id: Some(bad_id.clone()),
            result: Some(Box::new(UnserializableResult)),
            ..Default::default()
        }
        .message(),
    ) {
        panic!("failed to enqueue bad response: {}", err.error());
    }

    // A subsequent well-formed response must still be delivered.
    let good_id = ts_goport::jsonrpc::new_id_string("good");
    if let Err(err) = server.shared.send(
        lsproto::ResponseMessage {
            id: Some(good_id.clone()),
            result: Some(Box::new(lsproto::SelectionRangesOrNull::default())),
            ..Default::default()
        }
        .message(),
    ) {
        panic!("failed to enqueue good response: {}", err.error());
    }

    // Go: readMessageWithTimeout (server_test.go:209).
    // PORT: the timeout is 60 s (Go: 2 s) for a loaded test machine.
    let (msg_tx, msg_rx) = sync_channel::<Result<lsproto::Message, String>>(2);
    std::thread::spawn(move || {
        let mut reader = lsp::to_reader(Box::new(std::io::BufReader::new(pr)));
        for _ in 0..2 {
            let result = match lsp::Reader::read(&mut *reader) {
                (Some(msg), None) => Ok(msg),
                (_, Some(err)) => Err(err.error()),
                (None, None) => Err("no message".to_string()),
            };
            if msg_tx.send(result).is_err() {
                return;
            }
        }
    });

    let mut saw_error = false;
    let mut saw_good = false;
    for _ in 0..2 {
        let msg = match msg_rx.recv_timeout(Duration::from_secs(60)) {
            Ok(Ok(msg)) => msg,
            Ok(Err(err)) => panic!("failed to read message: {err}"),
            Err(_) => panic!("timed out waiting for a message (write loop may have died)"),
        };
        let resp = msg.as_response();
        if resp.id.as_ref() == Some(&bad_id) {
            match &resp.error {
                None => panic!(
                    "expected an error response for the unserializable request, got a result"
                ),
                Some(err) => assert_eq!(
                    err.code,
                    lsproto::ErrorCode::INTERNAL_ERROR.0,
                    "error response code = {}, want {}",
                    err.code,
                    lsproto::ErrorCode::INTERNAL_ERROR.0
                ),
            }
            saw_error = true;
        } else if resp.id.as_ref() == Some(&good_id) {
            if let Some(err) = &resp.error {
                panic!("expected a successful response for the good request, got error: {err:?}");
            }
            saw_good = true;
        } else {
            panic!("unexpected response id: {:?}", resp.id);
        }
    }

    assert!(
        saw_error,
        "did not receive an error response for the unserializable request"
    );
    assert!(
        saw_good,
        "did not receive the subsequent well-formed response (write loop likely died)"
    );

    // The write loop must still be running.
    if let Ok(result) = write_loop_err.try_recv() {
        let err = result.err().map(|err| err.error()).unwrap_or_default();
        panic!("write loop exited unexpectedly: {err}");
    }
    // Go: defer cancel()
    cancel();
}
