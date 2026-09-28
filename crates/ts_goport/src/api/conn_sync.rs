//! Port of internal/api/conn_sync.go.

use crate::api::prelude::*;

use crate::api::conn::{Conn, Handler, recovered_value};
use crate::api::protocol::{Message, Protocol};
use crate::api::transport::ReadWriteCloser;
use crate::frontend::json_ext::{AnyValue, JsonValue};
use crate::gostd::{Context, GoError, errors, strconv};
use crate::jsonrpc;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::time::Instant;

// Go: conn_sync.go:17 SyncConn
// SyncConn manages bidirectional communication with synchronous request handling.
// Requests are handled one at a time inline, and outgoing calls are serialized.
pub struct SyncConn {
    rwc: Arc<dyn ReadWriteCloser>,
    // PORT: Go `mu` serializes all protocol operations across goroutines.
    // Every use here runs on the dispatch thread, so the `RefCell` borrow
    // stands in for the lock: it is held for the same spans as `mu`.
    protocol: RefCell<Box<dyn Protocol>>,
    handler: Rc<dyn Handler>,

    // timing, when non-nil, accumulates the wall-clock time spent handling each
    // request. Clients retrieve the collected data via a getServerTiming request.
    timing: RefCell<Option<TimingCollector>>,
}

// Go: conn_sync.go:29 NewSyncConn
// NewSyncConn creates a new sync connection with the given transport and handler.
pub fn new_sync_conn(
    rwc: Arc<dyn ReadWriteCloser>,
    protocol: Box<dyn Protocol>,
    handler: Rc<dyn Handler>,
) -> Rc<SyncConn> {
    Rc::new(SyncConn {
        rwc,
        protocol: RefCell::new(protocol),
        handler,
        timing: RefCell::new(None),
    })
}

// PORT: the Go methods are inherent methods; `impl Conn` below forwards to
// them, so callers need not import `Conn`.
impl SyncConn {
    // Go: conn_sync.go:45 SetCollectTiming
    // SetCollectTiming enables or disables per-request server processing-time
    // measurement. When enabled, the connection accumulates timing that clients can
    // retrieve via a getServerTiming request.
    pub fn set_collect_timing(&self, enabled: bool) {
        if enabled {
            *self.timing.borrow_mut() = Some(new_timing_collector());
        } else {
            *self.timing.borrow_mut() = None;
        }
    }

    // Go: conn_sync.go:39 Run
    // Run starts processing messages on the connection.
    // It blocks until the context is cancelled or an error occurs.
    pub fn run(&self, ctx: &Context) -> Result<(), GoError> {
        loop {
            if let Some(err) = ctx.err() {
                return Err(err);
            }

            let result = self.protocol.borrow_mut().read_message();

            let msg = match result {
                Ok(msg) => msg,
                Err(err) => {
                    if errors::is(&err, &errors::EOF) {
                        return Ok(());
                    }
                    return Err(err);
                }
            };

            if msg.is_request() {
                self.handle_request(ctx, msg);
            } else if msg.is_notification() {
                self.handle_notification(ctx, msg);
            } else {
                // Responses are not expected in the main loop - they are read inline by Call().
                return Err(errors::new(
                    "api: unexpected response message in sync connection",
                ));
            }
        }
    }

    // Go: conn_sync.go:68 handleRequest
    // handleRequest processes an incoming request.
    // PORT: Go recovers panics in a deferred function; `catch_unwind` covers
    // the same body (the handler call and the response write). Go
    // `debug.Stack()` is the backtrace at the recover point.
    fn handle_request(&self, ctx: &Context, msg: Message) {
        // Intercept the meta-requests for collected server timing before dispatching
        // to the handler, so they are answered directly and not themselves recorded.
        if msg.method == Method::GET_SERVER_TIMING.0 {
            let snapshot = server_timing_snapshot(self.timing.borrow().as_ref());
            let write_err = self
                .protocol
                .borrow_mut()
                .write_response(msg.id.as_ref(), Some(Box::new(snapshot)));
            if let Err(write_err) = write_err {
                panic!(
                    "api: failed to write server timing response: {}",
                    write_err.error()
                );
            }
            return;
        }
        if msg.method == Method::RESET_SERVER_TIMING.0 {
            if let Some(timing) = self.timing.borrow_mut().as_mut() {
                timing.reset();
            }
            let write_err = self
                .protocol
                .borrow_mut()
                .write_response(msg.id.as_ref(), None);
            if let Err(write_err) = write_err {
                panic!(
                    "api: failed to write reset server timing response: {}",
                    write_err.error()
                );
            }
            return;
        }

        let id = msg.id.clone();

        let start = Instant::now();

        // Recover from panics and convert to error response with stack trace
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let (result, err) = match self.handler.handle_request(ctx, &msg.method, msg.params) {
                Ok(result) => (result, None),
                Err(err) => (None, Some(err)),
            };

            if let Some(timing) = self.timing.borrow_mut().as_mut() {
                timing.record(&msg.method, start.elapsed());
            }

            let mut protocol = self.protocol.borrow_mut();

            let write_err = if let Some(err) = err {
                protocol.write_error(
                    id.as_ref(),
                    &jsonrpc::ResponseError {
                        code: jsonrpc::CODE_INTERNAL_ERROR,
                        message: err.error(),
                        data: None,
                    },
                )
            } else {
                protocol.write_response(id.as_ref(), result)
            };

            if let Err(write_err) = write_err {
                panic!("api: failed to write response: {}", write_err.error());
            }
        }));

        if let Err(r) = outcome {
            let r = recovered_value(r.as_ref());
            let stack = std::backtrace::Backtrace::force_capture().to_string();
            let err = errors::new(format!("panic: {r}\n{stack}"));

            let write_err = self.protocol.borrow_mut().write_error(
                id.as_ref(),
                &jsonrpc::ResponseError {
                    code: jsonrpc::CODE_INTERNAL_ERROR,
                    message: err.error(),
                    data: None,
                },
            );

            if let Err(write_err) = write_err {
                panic!(
                    "api: failed to write panic error response: {} (original panic: {r})",
                    write_err.error()
                );
            }
        }
    }

    // Go: conn_sync.go:112 handleNotification
    // handleNotification processes an incoming notification.
    fn handle_notification(&self, ctx: &Context, msg: Message) {
        let _ = self
            .handler
            .handle_notification(ctx, &msg.method, msg.params);
    }

    // Go: conn_sync.go:118 Call
    // Call sends a request to the client and waits for a response.
    // This method is safe to call from multiple goroutines - calls are serialized.
    pub fn call(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<JsonValue, GoError> {
        // Serialize all Call operations. This is critical because:
        // 1. The msgpack protocol uses method names as response IDs
        // 2. The handler code (project internals) may spawn goroutines that call
        //    filesystem callbacks concurrently
        // 3. We need to ensure write/read pairs are atomic
        let mut protocol = self.protocol.borrow_mut();

        let id = jsonrpc::new_id_string(method);

        protocol.write_request(Some(&id), method, params)?;

        if let Some(err) = ctx.err() {
            return Err(err);
        }

        // Read the response inline.
        let msg = protocol.read_message()?;

        if msg.is_response() && msg.id.as_ref().is_some_and(|id| id.string() == method) {
            if let Some(error) = &msg.error {
                return Err(errors::new(format!(
                    "api: remote error [{}]: {}",
                    error.code, error.message
                )));
            }
            return Ok(msg.result);
        }

        // Unexpected message while waiting for response
        Err(errors::new(format!(
            "api: unexpected message while waiting for {} response",
            strconv::quote(method)
        )))
    }

    // Go: conn_sync.go:155 Notify
    // Notify sends a notification to the client (no response expected).
    pub fn notify(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError> {
        let _ = ctx;
        self.protocol
            .borrow_mut()
            .write_notification(method, params)
    }
}

impl Conn for SyncConn {
    fn run(&self, ctx: &Context) -> Result<(), GoError> {
        SyncConn::run(self, ctx)
    }

    fn call(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<JsonValue, GoError> {
        SyncConn::call(self, ctx, method, params)
    }

    fn notify(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError> {
        SyncConn::notify(self, ctx, method, params)
    }
}
