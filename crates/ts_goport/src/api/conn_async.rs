//! Port of internal/api/conn_async.go.
//!
//! PORT: Go handles each incoming request in its own goroutine, and `Call`
//! waits on a response channel that the `Run` goroutine fills. The API
//! session and project state live on the dispatch thread, so here `Run`
//! handles each request and notification inline, and `Call` reads messages
//! itself until its response arrives. Responses delivered this way keep
//! their IDs; requests and notifications that `Call` reads while it waits
//! are queued and `Run` handles them next, in arrival order. So the
//! responses can come in a different order than in Go.

use crate::api::prelude::*;

use crate::api::conn::{Conn, Handler, recovered_value};
use crate::api::protocol::{Message, Protocol};
use crate::api::protocol_jsonrpc::new_jsonrpc_protocol;
use crate::api::transport::ReadWriteCloser;
use crate::frontend::json_ext::{AnyValue, JsonValue};
use crate::gostd::{Context, GoError, errors};
use crate::jsonrpc;
use std::cell::Cell;
use std::collections::VecDeque;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::time::Instant;

/// Go `chan *Message` with capacity 1 for one pending server-to-client call.
type ResponseChan = Rc<RefCell<Option<Message>>>;

// Go: conn_async.go:19 AsyncConn
// AsyncConn manages bidirectional JSON-RPC communication with async request handling.
// Each incoming request is handled in its own goroutine, allowing concurrent processing.
// This is the standard implementation for LSP-style JSON-RPC protocols.
pub struct AsyncConn {
    rwc: Arc<dyn ReadWriteCloser>,
    // PORT: Go `writeMu` guards writes across goroutines; on the dispatch
    // thread the `RefCell` borrow stands in for it (reads use it too).
    protocol: RefCell<Box<dyn Protocol>>,
    handler: Rc<dyn Handler>,

    // timing, when non-nil, accumulates the wall-clock time spent handling each
    // request. Clients retrieve the collected data via a getServerTiming request.
    timing: RefCell<Option<TimingCollector>>,

    // For server→client requests
    // PORT: Go `atomic.Int64` and the `pendingMu` lock are plain cells.
    seq: Cell<i64>,
    pending: RefCell<FxHashMap<jsonrpc::ID, ResponseChan>>,

    // PORT: requests and notifications that `call` read while it waited for
    // its response. `run` handles them before it reads more.
    deferred: RefCell<VecDeque<Message>>,
}

// Go: conn_async.go:33 NewAsyncConn
// NewAsyncConn creates a new async connection with the given transport and handler.
// It uses JSONRPCProtocol (LSP-style Content-Length framing) by default.
pub fn new_async_conn(rwc: Arc<dyn ReadWriteCloser>, handler: Rc<dyn Handler>) -> Rc<AsyncConn> {
    let protocol = new_jsonrpc_protocol(rwc.clone());
    new_async_conn_with_protocol(rwc, Box::new(protocol), handler)
}

// Go: conn_async.go:38 NewAsyncConnWithProtocol
// NewAsyncConnWithProtocol creates a new async connection with a custom protocol.
pub fn new_async_conn_with_protocol(
    rwc: Arc<dyn ReadWriteCloser>,
    protocol: Box<dyn Protocol>,
    handler: Rc<dyn Handler>,
) -> Rc<AsyncConn> {
    Rc::new(AsyncConn {
        rwc,
        protocol: RefCell::new(protocol),
        handler,
        timing: RefCell::new(None),
        seq: Cell::new(0),
        pending: RefCell::new(FxHashMap::default()),
        deferred: RefCell::new(VecDeque::new()),
    })
}

// PORT: the Go methods are inherent methods; `impl Conn` below forwards to
// them, so callers need not import `Conn`.
impl AsyncConn {
    // Go: conn_async.go:55 SetCollectTiming
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

    // Go: conn_async.go:49 Run
    // Run starts processing messages on the connection.
    // It blocks until the context is cancelled or an error occurs.
    pub fn run(&self, ctx: &Context) -> Result<(), GoError> {
        loop {
            if let Some(err) = ctx.err() {
                return Err(err);
            }

            // PORT: messages that `call` queued come first.
            let queued = self.deferred.borrow_mut().pop_front();
            let result = match queued {
                Some(msg) => Ok(msg),
                None => self.protocol.borrow_mut().read_message(),
            };
            let msg = match result {
                Ok(msg) => msg,
                Err(err) => {
                    if errors::is(&err, &errors::EOF) {
                        return Ok(());
                    }
                    return Err(err);
                }
            };

            if msg.is_response() {
                self.handle_response(msg);
            } else if msg.is_request() {
                // PORT: Go `go c.handleRequest(ctx, msg)`; handled inline.
                self.handle_request(ctx, msg);
            } else if msg.is_notification() {
                // PORT: Go `go c.handleNotification(ctx, msg)`; handled inline.
                self.handle_notification(ctx, msg);
            }
        }
    }

    // Go: conn_async.go:74 handleResponse
    // handleResponse matches a response to a pending request.
    fn handle_response(&self, msg: Message) {
        let Some(id) = msg.id.clone() else {
            // Go dereferences the nil ID and panics; responses always have one.
            panic!("runtime error: invalid memory address or nil pointer dereference");
        };
        let ch = self.pending.borrow_mut().remove(&id);

        if let Some(ch) = ch {
            *ch.borrow_mut() = Some(msg);
        }
    }

    // Go: conn_async.go:89 handleRequest
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

    // Go: conn_async.go:133 handleNotification
    // handleNotification processes an incoming notification.
    fn handle_notification(&self, ctx: &Context, msg: Message) {
        let _ = self
            .handler
            .handle_notification(ctx, &msg.method, msg.params);
    }

    // Go: conn_async.go:138 Call
    // Call sends a request to the client and waits for a response.
    pub fn call(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<JsonValue, GoError> {
        // Create unique request ID
        self.seq.set(self.seq.get() + 1);
        let id = jsonrpc::new_id_string(&format!("api{}", self.seq.get()));

        // Register response channel BEFORE sending request to avoid race
        let response_chan: ResponseChan = Rc::new(RefCell::new(None));
        self.pending
            .borrow_mut()
            .insert(id.clone(), response_chan.clone());

        // Go: defer that drops the pending entry on every return.
        let remove_pending = || {
            self.pending.borrow_mut().remove(&id);
        };

        // Send the request
        let err = self
            .protocol
            .borrow_mut()
            .write_request(Some(&id), method, params);

        if let Err(err) = err {
            remove_pending();
            return Err(err);
        }

        // PORT: Go selects on `ctx.Done()` and the response channel while the
        // Run goroutine reads. Here the loop reads messages until the
        // response is in the channel; `ctx` is checked before each read (a
        // blocked read is not interrupted). A read error ends the call; in
        // Go the Run goroutine would stop and Call would wait for `ctx`.
        loop {
            if let Some(err) = ctx.err() {
                remove_pending();
                return Err(err);
            }

            let resp = response_chan.borrow_mut().take();
            if let Some(resp) = resp {
                remove_pending();
                if let Some(error) = &resp.error {
                    return Err(errors::new(format!(
                        "api: remote error [{}]: {}",
                        error.code, error.message
                    )));
                }
                return Ok(resp.result);
            }

            let msg = match self.protocol.borrow_mut().read_message() {
                Ok(msg) => msg,
                Err(err) => {
                    remove_pending();
                    return Err(err);
                }
            };
            if msg.is_response() {
                self.handle_response(msg);
            } else {
                self.deferred.borrow_mut().push_back(msg);
            }
        }
    }

    // Go: conn_async.go:178 Notify
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

impl Conn for AsyncConn {
    fn run(&self, ctx: &Context) -> Result<(), GoError> {
        AsyncConn::run(self, ctx)
    }

    fn call(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<JsonValue, GoError> {
        AsyncConn::call(self, ctx, method, params)
    }

    fn notify(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError> {
        AsyncConn::notify(self, ctx, method, params)
    }
}
