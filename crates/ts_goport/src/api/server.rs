//! Port of internal/api/server.go.

use crate::api::prelude::*;

use crate::api::callbackfs::{CallbackFS, new_callback_fs};
use crate::api::protocol_msgpack::new_message_pack_protocol;
use crate::frontend::bundled;
use crate::frontend::vfs::{self, Fs};
use crate::gostd::{Context, GoError, errors};
use crate::ipc::{
    Conn, Handler, Transport, new_async_conn_with_protocol, new_jsonrpc_protocol,
    new_pipe_transport, new_stdio_transport, new_sync_conn,
};
use crate::lsp::lsproto;
use crate::project;
use std::io::{Read, Write};
use std::time::Duration;

// Go: server.go:15 StdioServerOptions
// StdioServerOptions configures the STDIO-based API server.
// PORT: Go `io.ReadCloser` / `io.WriteCloser` / `io.Writer` are boxed
// `Read` / `Write` values; a nil one is `None`. `In` and `Async` are Rust
// keywords, so the fields are `in_` and `async_`.
#[derive(Default)]
pub struct StdioServerOptions {
    pub in_: Option<Box<dyn Read + Send>>,
    pub out: Option<Box<dyn Write + Send>>,
    pub err: Option<Box<dyn Write + Send>>,
    pub cwd: String,
    pub default_library_path: String,
    // PipePath, if set, listens on a named pipe (Windows) or Unix domain
    // socket instead of using In/Out for communication.
    pub pipe_path: String,
    // Callbacks specifies which filesystem operations should be delegated
    // to the client (e.g., "readFile", "fileExists"). Empty means no callbacks.
    pub callbacks: Vec<String>,
    // Async enables JSON-RPC protocol with async connection handling.
    // When false (default), uses MessagePack protocol with sync connection.
    pub async_: bool,
    // CollectTiming enables per-request server processing-time measurement.
    // When enabled, the server accumulates each request's processing time into
    // running totals and a recent-request ring buffer. Response messages are
    // left unchanged; the client folds this data into its own timing snapshot
    // on demand via getServerTiming / resetServerTiming requests.
    pub collect_timing: bool,
}

// Go: server.go:35 StdioServer
// StdioServer runs an API session over STDIO using MessagePack protocol.
// This is the entry point for the synchronous STDIO-based API used by
// native TypeScript tooling integration.
pub struct StdioServer {
    options: StdioServerOptions,
}

// Go: server.go:40 NewStdioServer
// NewStdioServer creates a new STDIO-based API server.
// PORT: Go keeps the `*StdioServerOptions` pointer; the server owns the
// options here (they hold the stdin and stdout handles).
pub fn new_stdio_server(options: StdioServerOptions) -> StdioServer {
    if options.cwd.is_empty() {
        panic!("StdioServerOptions.Cwd is required");
    }

    StdioServer { options }
}

// Go `defer f()`: runs `f` when the guard leaves scope, on every return
// path and during a panic.
struct Defer<F: FnMut()>(F);

impl<F: FnMut()> Drop for Defer<F> {
    fn drop(&mut self) {
        (self.0)();
    }
}

impl StdioServer {
    // Go: server.go:51 Run
    // Run starts the server and blocks until the connection closes.
    // PORT: `&mut self` because Accept moves the stdin and stdout handles
    // out of the options.
    pub fn run(&mut self, ctx: &Context) -> Result<(), GoError> {
        let transport: Box<dyn Transport> = if !self.options.pipe_path.is_empty() {
            let t = match new_pipe_transport(&self.options.pipe_path) {
                Ok(t) => t,
                Err(err) => {
                    return Err(errors::errorf(
                        format!("failed to create pipe transport: {}", err.error()),
                        vec![err],
                    ));
                }
            };
            Box::new(t)
        } else {
            let t = new_stdio_transport(self.options.in_.take(), self.options.out.take());
            Box::new(t)
        };
        // defer t.Close()
        let transport = RefCell::new(transport);
        let _close_transport = Defer(|| {
            let _ = transport.borrow_mut().close();
        });

        let mut fs: Rc<dyn Fs> = bundled::wrap_fs_exported(vfs::osvfs_fs());

        // Wrap the base FS with callbackFS if callbacks are requested
        let mut callback_fs: Option<Rc<CallbackFS>> = None;
        if !self.options.callbacks.is_empty() {
            let cfs = new_callback_fs(fs.clone(), &self.options.callbacks);
            fs = cfs.clone();
            callback_fs = Some(cfs);
        }

        let project_session = project::new_session(&project::SessionInit {
            background_ctx: ctx.clone(),
            logger: None, // TODO: Add logging support
            fs,
            options: Rc::new(project::SessionOptions {
                current_directory: self.options.cwd.clone(),
                default_library_path: self.options.default_library_path.clone(),
                position_encoding: lsproto::PositionEncodingKind::UTF8,
                logging_enabled: false,
                // PORT: Go leaves the other fields at their zero values.
                typings_location: String::new(),
                watch_enabled: false,
                telemetry_enabled: false,
                push_diagnostics_enabled: false,
                debounce_delay: Duration::ZERO,
                checker_pool_options: project::CheckerPoolOptions::default(),
            }),
            client: None,
            npm_executor: None,
            parse_cache: None,
        });

        let session = new_session(
            project_session,
            Some(&SessionOptions {
                use_binary_responses: !self.options.async_, // Only msgpack uses binary responses
            }),
        );
        // defer session.Close()
        let _close_session = Defer(|| {
            session.close();
        });

        // Accept connection from transport
        let accepted = transport.borrow_mut().accept();
        let rwc = match accepted {
            Ok(rwc) => rwc,
            Err(err) => {
                return Err(errors::errorf(
                    format!("failed to accept connection: {}", err.error()),
                    vec![err],
                ));
            }
        };

        // Create protocol and connection based on async mode
        let handler: Rc<dyn Handler> = session.clone();
        let conn: Rc<dyn Conn>;
        if self.options.async_ {
            let protocol = new_jsonrpc_protocol(rwc.clone());
            let async_conn = new_async_conn_with_protocol(rwc, Box::new(protocol), handler);
            async_conn.set_collect_timing(self.options.collect_timing);
            conn = async_conn;
        } else {
            let protocol = new_message_pack_protocol(rwc.clone());
            let sync_conn = new_sync_conn(rwc, Box::new(protocol), handler);
            sync_conn.set_collect_timing(self.options.collect_timing);
            conn = sync_conn;
        }

        // If callbacks are enabled, set the connection on the FS
        if let Some(callback_fs) = &callback_fs {
            callback_fs.set_connection(ctx, conn.clone());
        }

        conn.run(ctx)
    }
}
