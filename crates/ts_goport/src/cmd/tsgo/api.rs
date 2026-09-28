//! Go `cmd/tsgo/api.go`.

use crate::cmd::tsgo::prelude::*;

use crate::cmd::tsgo::main::{ErrorHandling, must_getwd, new_flag_set, notify_context};
use crate::frontend::bundled;
use crate::gostd::context;

// Go: cmd/tsgo/api.go:17 runAPI
pub fn run_api(args: &[String]) -> i32 {
    let mut flag = new_flag_set("api", ErrorHandling::ContinueOnError);
    let cwd = flag.string("cwd", &must_getwd(), "current working directory");
    let pipe_path = flag.string(
        "pipe",
        "",
        "use named pipe or Unix domain socket for communication instead of stdio",
    );
    let callbacks = flag.string(
        "callbacks",
        "",
        "comma-separated list of FS callbacks to enable (readFile,fileExists,directoryExists,getAccessibleEntries,realpath)",
    );
    let async_ = flag.bool(
        "async",
        false,
        "use JSON-RPC protocol instead of MessagePack (for async API)",
    );
    let timing = flag.bool(
        "timing",
        false,
        "collect per-request server processing time, folded into the client's timing snapshot",
    );
    if flag.parse(args).is_err() {
        return 2;
    }

    let default_library_path = bundled::lib_path_exported();

    // Parse callbacks list
    let mut callbacks_list: Vec<String> = Vec::new();
    if !callbacks.borrow().is_empty() {
        callbacks_list = callbacks.borrow().split(',').map(str::to_string).collect();
    }

    // PORT: Go `In io.ReadCloser`, `Out io.WriteCloser` and `Err io.Writer`
    // are nil-able interfaces (`None`).
    let mut options = crate::api::StdioServerOptions {
        in_: None,
        out: None,
        err: Some(Box::new(std::io::stderr())),
        cwd: cwd.borrow().clone(),
        default_library_path,
        pipe_path: String::new(),
        callbacks: callbacks_list,
        async_: async_.get(),
        collect_timing: timing.get(),
    };
    if !pipe_path.borrow().is_empty() {
        options.pipe_path = pipe_path.borrow().clone();
    } else {
        options.in_ = Some(Box::new(std::io::stdin()));
        options.out = Some(Box::new(std::io::stdout()));
    }

    let mut s = crate::api::new_stdio_server(options);

    // Go: ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
    let (ctx, stop) = notify_context(&context::background());

    let result = s.run(&ctx);
    // Go: defer stop()
    stop();
    if let Err(err) = result {
        eprintln!("{}", err.error());
        return 1;
    }
    0
}
