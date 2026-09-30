//! Port of internal/ipc/conn_async.go (internal/api/conn_async.go before
//! tsgo#4712).
//!
//! PORT: Go handles each incoming request in its own goroutine, and `Call`
//! waits on a response channel that the `Run` goroutine fills. The API
//! session and project state live on the dispatch thread, so here `Run`
//! handles each request and notification inline, and `Call` reads messages
//! itself until its response arrives. Responses delivered this way keep
//! their IDs; requests and notifications that `Call` reads while it waits
//! are queued and `Run` handles them next, in arrival order. So the
//! responses can come in a different order than in Go.
//!
//! PORT: the reads in `Call` are Go's `Run` reads. When one fails, the read
//! loop ends there, as Go's `Run` would: `closePendingCalls` sets
//! `terminal` (tsgo#4712), the call returns it, and a later `run` handles
//! the queued messages and then returns what Go's `Run` returned.

use crate::ipc::prelude::*;

use crate::frontend::json_ext::{AnyValue, JsonValue};
use crate::gostd::{Context, GoError, errors};
use crate::ipc::conn::{Conn, ERR_CONN_CLOSED, Handler, recovered_value};
use crate::ipc::protocol::{Message, Protocol};
use crate::ipc::protocol_jsonrpc::new_jsonrpc_protocol;
use crate::ipc::transport::ReadWriteCloser;
use crate::jsonrpc;
use std::cell::Cell;
use std::collections::VecDeque;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::time::Instant;

/// Go `chan *Message` with capacity 1 for one pending server-to-client call.
type ResponseChan = Rc<RefCell<Option<Message>>>;

// Go: ipc/conn_async.go:20 AsyncConn
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
    terminal: RefCell<Option<GoError>>,
    // ts#64142
    has_cause: Cell<bool>,

    // PORT: requests and notifications that `call` read while it waited for
    // its response. `run` handles them before it reads more.
    deferred: RefCell<VecDeque<Message>>,
    // PORT: how the read loop ended when a read in `call` ended it: the
    // value Go's `Run` returned. `run` returns it and reads no more.
    read_loop_end: RefCell<Option<Result<(), GoError>>>,
}

// Go: ipc/conn_async.go:39 NewAsyncConn
// NewAsyncConn creates a new async connection with the given transport and handler.
// It uses JSONRPCProtocol (LSP-style Content-Length framing) by default.
pub fn new_async_conn(rwc: Arc<dyn ReadWriteCloser>, handler: Rc<dyn Handler>) -> Rc<AsyncConn> {
    let protocol = new_jsonrpc_protocol(rwc.clone());
    new_async_conn_with_protocol(rwc, Box::new(protocol), handler)
}

// Go: ipc/conn_async.go:44 NewAsyncConnWithProtocol
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
        terminal: RefCell::new(None),
        has_cause: Cell::new(false),
        deferred: RefCell::new(VecDeque::new()),
        read_loop_end: RefCell::new(None),
    })
}

// PORT: the Go methods are inherent methods; `impl Conn` below forwards to
// them, so callers need not import `Conn`.
impl AsyncConn {
    // Go: ipc/conn_async.go:56 SetCollectTiming
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

    // Go: ipc/conn_async.go:66 Run
    // Run starts processing messages on the connection.
    // It blocks until the context is cancelled or an error occurs.
    pub fn run(&self, ctx: &Context) -> Result<(), GoError> {
        // ts#64142: Go `requestErrors := make(chan error, 1)`.
        let request_errors: RefCell<Option<GoError>> = RefCell::new(None);
        // Go: defer func() { c.closePendingCalls(err); cancelHandlers(); c.handlers.Wait(); ... }()
        // PORT: the handlers run inline (file header), so when the loop ends
        // no handler is active: the Go `handlerCtx` cancel and the
        // `handlers.Wait()` (ts#64163) have nothing to do.
        let mut result = self.run_loop(ctx, &request_errors);
        self.close_pending_calls(result.as_ref().err());
        let request_err = request_errors.borrow_mut().take();
        if let Some(request_err) = request_err {
            result = Err(errors::join([result.err(), Some(request_err)])
                .expect("the request error is non-nil"));
        }
        result
    }

    /// The loop of Go `Run`, without its deferred function.
    fn run_loop(
        &self,
        ctx: &Context,
        request_errors: &RefCell<Option<GoError>>,
    ) -> Result<(), GoError> {
        loop {
            if let Some(err) = ctx.err() {
                return Err(err);
            }

            // PORT: messages that `call` queued come first. When a read in
            // `call` ended the read loop, there is nothing more to read.
            let queued = self.deferred.borrow_mut().pop_front();
            let result = match queued {
                Some(msg) => Ok(msg),
                None => {
                    if let Some(end) = self.read_loop_end.borrow().clone() {
                        return end;
                    }
                    self.protocol.borrow_mut().read_message()
                }
            };
            let msg = match result {
                Ok(msg) => msg,
                Err(err) => return read_loop_result(err),
            };

            if msg.is_response() {
                self.handle_response(msg);
            } else if msg.is_request() {
                // PORT: Go `c.handlers.Go(...)` (ts#64163); handled inline.
                if let Err(request_err) = self.handle_request(ctx, msg)
                    && self.record_request_error(request_err, request_errors)
                {
                    // PORT: Go checks `c.rwc != nil`; the Rust transport is
                    // always set.
                    let _ = self.rwc.close();
                }
            } else if msg.is_notification() {
                // PORT: Go `c.handlers.Go(...)` (ts#64163); handled inline.
                self.handle_notification(ctx, msg);
            }
        }
    }

    // Go: ipc/conn_async.go:92 closePendingCalls
    // closePendingCalls records that the read loop has exited and unblocks requests waiting for a response.
    // PORT: Go closes each pending response channel, and the `Call` that
    // waits on it returns `terminal`. Here the only call that can wait is the
    // one whose read ended the loop, and it returns `terminal` itself.
    fn close_pending_calls(&self, run_err: Option<&GoError>) {
        self.record_terminal_error_locked(run_err);
        self.close_pending_calls_locked();
    }

    // Go: ipc/conn_async.go recordRequestError (ts#64142)
    // PORT: Go sends to the `requestErrors` channel (capacity 1); here the
    // slot is an `Option`. Only the first cause returns true, so one error is
    // stored at most.
    fn record_request_error(
        &self,
        request_err: GoError,
        request_errors: &RefCell<Option<GoError>>,
    ) -> bool {
        if !self.record_terminal_error_locked(Some(&request_err)) {
            return false;
        }
        *request_errors.borrow_mut() = Some(request_err);
        self.close_pending_calls_locked();
        true
    }

    // Go: ipc/conn_async.go recordTerminalErrorLocked (ts#64142)
    fn record_terminal_error_locked(&self, terminal_err: Option<&GoError>) -> bool {
        let mut terminal = self.terminal.borrow_mut();
        if terminal.is_none() {
            let err = ERR_CONN_CLOSED.clone();
            if let Some(terminal_err) = terminal_err {
                *terminal = Some(
                    errors::join([err, terminal_err.clone()]).expect("both errors are non-nil"),
                );
                self.has_cause.set(true);
                return true;
            }
            *terminal = Some(err);
        } else if !self.has_cause.get()
            && let Some(terminal_err) = terminal_err
        {
            let current = terminal.take().expect("terminal is set");
            *terminal = Some(
                errors::join([current, terminal_err.clone()]).expect("both errors are non-nil"),
            );
            self.has_cause.set(true);
            return true;
        }
        false
    }

    // Go: ipc/conn_async.go closePendingCallsLocked (ts#64142)
    fn close_pending_calls_locked(&self) {
        self.pending.borrow_mut().clear();
    }

    // Go: ipc/conn_async.go:108 handleResponse
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

    // Go: ipc/conn_async.go:123 handleRequest
    // handleRequest processes an incoming request.
    // PORT: Go recovers panics in a deferred function; `catch_unwind` covers
    // the same body (the handler call and the response write). Go
    // `debug.Stack()` is the backtrace at the recover point.
    // ts#64142: write failures are returned, not panics.
    fn handle_request(&self, ctx: &Context, msg: Message) -> Result<(), GoError> {
        // Intercept the meta-requests for collected server timing before dispatching
        // to the handler, so they are answered directly and not themselves recorded.
        if msg.method == METHOD_GET_SERVER_TIMING {
            let snapshot = server_timing_snapshot(self.timing.borrow().as_ref());
            let write_err = self
                .protocol
                .borrow_mut()
                .write_response(msg.id.as_ref(), Some(Box::new(snapshot)));
            if let Err(write_err) = write_err {
                return Err(errors::errorf(
                    format!(
                        "ipc: failed to write server timing response: {}",
                        write_err.error()
                    ),
                    vec![write_err],
                ));
            }
            return Ok(());
        }
        if msg.method == METHOD_RESET_SERVER_TIMING {
            if let Some(timing) = self.timing.borrow_mut().as_mut() {
                timing.reset();
            }
            let write_err = self
                .protocol
                .borrow_mut()
                .write_response(msg.id.as_ref(), None);
            if let Err(write_err) = write_err {
                return Err(errors::errorf(
                    format!(
                        "ipc: failed to write reset server timing response: {}",
                        write_err.error()
                    ),
                    vec![write_err],
                ));
            }
            return Ok(());
        }

        let id = msg.id.clone();

        let start = Instant::now();

        // Recover from panics and convert to error response with stack trace
        let outcome = catch_unwind(AssertUnwindSafe(|| -> Result<(), GoError> {
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
                return Err(errors::errorf(
                    format!("ipc: failed to write response: {}", write_err.error()),
                    vec![write_err],
                ));
            }
            Ok(())
        }));

        let r = match outcome {
            Ok(result) => return result,
            Err(r) => r,
        };
        {
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
                return Err(errors::errorf(
                    format!(
                        "ipc: failed to write panic error response: {} (original panic: {r})",
                        write_err.error()
                    ),
                    vec![write_err],
                ));
            }
        }
        Ok(())
    }

    // Go: ipc/conn_async.go:200 handleNotification
    // handleNotification processes an incoming notification.
    fn handle_notification(&self, ctx: &Context, msg: Message) {
        let _ = self
            .handler
            .handle_notification(ctx, &msg.method, msg.params);
    }

    // Go: ipc/conn_async.go:205 Call
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
        let terminal = self.terminal.borrow().clone();
        if let Some(err) = terminal {
            return Err(err);
        }
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
        // blocked read is not interrupted). A read error ends the read loop,
        // as it ends Go's `Run`, and the call returns `terminal`, as Go's
        // `Call` does when `closePendingCalls` closes its channel.
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
                        "ipc: remote error [{}]: {}",
                        error.code, error.message
                    )));
                }
                return Ok(resp.result);
            }

            let read = self.protocol.borrow_mut().read_message();
            let msg = match read {
                Ok(msg) => msg,
                Err(err) => {
                    let end = read_loop_result(err);
                    self.close_pending_calls(end.as_ref().err());
                    *self.read_loop_end.borrow_mut() = Some(end);
                    remove_pending();
                    let terminal = self.terminal.borrow().clone();
                    return Err(terminal.expect("closePendingCalls sets terminal"));
                }
            };
            if msg.is_response() {
                self.handle_response(msg);
            } else {
                self.deferred.borrow_mut().push_back(msg);
            }
        }
    }

    // Go: ipc/conn_async.go:256 Notify
    // Notify sends a notification to the client (no response expected).
    pub fn notify(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError> {
        let _ = ctx;
        let terminal = self.terminal.borrow().clone();
        if let Some(err) = terminal {
            return Err(err);
        }
        self.protocol
            .borrow_mut()
            .write_notification(method, params)
    }
}

/// What Go `Run` returns when its read fails: nil for `io.EOF`, else the
/// error.
fn read_loop_result(err: GoError) -> Result<(), GoError> {
    if errors::is(&err, &errors::EOF) {
        return Ok(());
    }
    Err(err)
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

// Go: ipc/conn_async_test.go (tsgo#4712)
// PORT: Go `net.Pipe` is a `UnixStream` pair. Go runs `Run` and `Call` in
// goroutines. The port's `call` reads its own response (see the file
// header), so each test runs them in turn on one thread, and the peer runs
// on a thread when it must act while `call` blocks.
#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use crate::gostd::context;
    use std::io::{Read as _, Write as _};
    use std::os::unix::net::UnixStream;
    use std::time::Duration;

    // Go: ipc/conn_async_test.go:16 noOpHandler
    struct NoOpHandler;

    impl Handler for NoOpHandler {
        fn handle_request(
            &self,
            _ctx: &Context,
            _method: &str,
            _params: JsonValue,
        ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
            Ok(None)
        }

        fn handle_notification(
            &self,
            _ctx: &Context,
            _method: &str,
            _params: JsonValue,
        ) -> Result<(), GoError> {
            Ok(())
        }
    }

    /// One end of Go `net.Pipe()`.
    struct PipeEnd(UnixStream);

    impl ReadWriteCloser for PipeEnd {
        fn read(&self, buf: &mut [u8]) -> std::io::Result<usize> {
            (&self.0).read(buf)
        }

        fn write(&self, buf: &[u8]) -> std::io::Result<usize> {
            (&self.0).write(buf)
        }

        fn flush(&self) -> std::io::Result<()> {
            (&self.0).flush()
        }

        fn close(&self) -> Result<(), GoError> {
            self.0
                .shutdown(std::net::Shutdown::Both)
                .map_err(|err| errors::new(err.to_string()))
        }
    }

    // Go: ipc/conn_async_test.go:26 TestAsyncConnCallReturnsWhenPeerCloses
    #[test]
    fn test_async_conn_call_returns_when_peer_closes() {
        let (client, server) = UnixStream::pair().expect("socket pair");
        let client: Arc<dyn ReadWriteCloser> = Arc::new(PipeEnd(client));
        let conn = new_async_conn(client.clone(), Rc::new(NoOpHandler));
        let ctx = context::background();

        // The peer reads the request and closes its end.
        let peer = std::thread::spawn(move || {
            let mut buffer = [0u8; 1024];
            let read = (&server).read(&mut buffer);
            drop(server);
            read.map(|_| ())
        });

        let call_err = conn
            .call(&ctx, "transform", None)
            .expect_err("call fails when the peer closes");
        peer.join().expect("peer thread").expect("server read");
        assert!(conn.run(&ctx).is_ok());
        assert!(
            errors::is(&call_err, &ERR_CONN_CLOSED),
            "expected ErrConnClosed, got {}",
            call_err.error()
        );
        client.close().expect("client close");
    }

    // Go: ipc/conn_async_test.go:48 TestAsyncConnCallAfterReadLoopFailureReturnsImmediately
    #[test]
    fn test_async_conn_call_after_read_loop_failure_returns_immediately() {
        let (client, server) = UnixStream::pair().expect("socket pair");
        let conn = new_async_conn(Arc::new(PipeEnd(client)), Rc::new(NoOpHandler));
        let background = context::background();

        (&server).write_all(b"oops\n").expect("server write");
        let run_err = conn.run(&background).expect_err("run fails");
        assert!(
            run_err.error().contains("invalid header"),
            "{}",
            run_err.error()
        );
        // PORT: Go drains the server end (`io.Copy(io.Discard, server)`) so a
        // write cannot block on `net.Pipe`; the socket buffer covers that here.

        let (ctx, cancel) = context::with_timeout(&background, Duration::from_secs(1));
        let err = conn
            .call(&ctx, "transform", None)
            .expect_err("call fails after the read loop ended");
        assert!(
            errors::is(&err, &ERR_CONN_CLOSED),
            "expected ErrConnClosed, got {}",
            err.error()
        );
        assert!(
            !errors::is(&err, &context::DEADLINE_EXCEEDED),
            "call waited for its context deadline: {}",
            err.error()
        );
        let err = conn
            .notify(&ctx, "changed", None)
            .expect_err("notify fails after the read loop ended");
        assert!(
            errors::is(&err, &ERR_CONN_CLOSED),
            "expected ErrConnClosed, got {}",
            err.error()
        );
        cancel();
        drop(server);
    }
}
