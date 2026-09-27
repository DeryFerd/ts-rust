//! `goport_build`: `tsc -b` with the Go port.
//!
//! - `goport_build -b [projects...] [options]` (also `--b`, `-build`,
//!   `--build`): Go `execute.CommandLine` with a build flag, which is
//!   `tscBuildCompilation` (execute/tsc.go:90). The exit code is the Go
//!   exit status. With `--watch` the run builds, then stays in the watch
//!   loop (Go `WatchManager.RunLoop`) until the process is killed: there is
//!   no signal handling (plan D-W3), so the loop never ends by itself.
//!   Output goes to stdout as it is written.
//! - `goport_build --build-worker <config> [the -b command line...]`: the
//!   build worker (plan D1). It compiles and emits one project the way the
//!   Go build task does and prints one JSON result line (see
//!   `execute::build::worker`). The orchestrator starts these itself.
//!   Without a `-b` command line it runs with the default build options.
//!   It reads the build's cached file system from stdin (empty input, or
//!   a terminal, is an empty cache).
//!
//! Only build mode is ported. Other command lines (Go `tscCompilation`)
//! exit with `EXIT_UNPORTED` (70).
//!
//! Unported Go code that a run reaches is listed on stderr as
//! `unported: <name> <count>`. Such a run, a panic and a failed build
//! worker exit with `EXIT_UNPORTED` (70), a code tsgo never returns (Go
//! uses 0 to 5), like `goport` and `goport_emit`. A Go panic that the port
//! keeps (`core::go_panic`), in the orchestrator or in a worker, ends the
//! build as in Go: the output so far, `panic: <message>` on stderr and
//! exit 2.

use std::any::Any;
use std::io::{IsTerminal, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

use ts_goport::execute::build::worker::{
    BUILD_WORKER_FLAG, compile_and_emit_worker, marshal_worker_compile_result,
    marshal_worker_program_fs_cache, read_worker_fs_cache,
};
use ts_goport::execute::execute_tsc::tsc_build_compilation;
use ts_goport::execute::tsc::compile::{
    EXIT_UNPORTED, ExitStatus, System, new_os_system, write_go_output,
};
use ts_goport::frontend::vfs::CachedFsState;
use ts_goport::gostd::context;
use ts_goport::prelude::*;

const UNPORTED_PREFIX: &str = "unported Go code";

/// Stack size for the main work thread. The checker recurses deeply on
/// large projects.
const STACK_SIZE: usize = 1 << 30;

/// The opt-in `jemalloc` feature makes jemalloc the global allocator
/// (see `goport.rs` `set_malloc_tunables`).
#[cfg(feature = "jemalloc")]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

fn main() {
    set_malloc_tunables();
    let args: Vec<String> = ts_goport::frontend::vfs::os_args();
    install_panic_hook();
    let work = std::thread::Builder::new()
        .name("goport_build".to_string())
        .stack_size(STACK_SIZE)
        .spawn(move || run(&args));
    let code = if let Ok(Ok(code)) = work.map(std::thread::JoinHandle::join) {
        code
    } else {
        eprintln!("goport_build: work thread failed");
        EXIT_UNPORTED
    };
    std::process::exit(code);
}

/// Copied from `goport.rs` `set_malloc_tunables`, which explains the
/// values. A build runs about 20 threads per program, so `arena_max` is 16
/// here. Build workers inherit the variable, so they do not exec again. The
/// `jemalloc` build keeps the jemalloc defaults.
fn set_malloc_tunables() {
    #[cfg(all(target_os = "linux", target_env = "gnu", not(feature = "jemalloc")))]
    {
        use std::os::unix::process::CommandExt;
        const NAME: &str = "GLIBC_TUNABLES";
        const VALUE: &str =
            "glibc.malloc.hugetlb=1:glibc.malloc.arena_max=16:glibc.malloc.top_pad=67108864";
        if std::env::var_os(NAME).is_some() {
            return;
        }
        let Ok(exe) = std::env::current_exe() else {
            return;
        };
        let mut args = std::env::args_os();
        let mut command = std::process::Command::new(exe);
        if let Some(arg0) = args.next() {
            command.arg0(arg0);
        }
        // `exec` returns only when it fails.
        let _ = command.args(args).env(NAME, VALUE).exec();
    }
}

fn run(args: &[String]) -> i32 {
    let sys = match new_os_system() {
        Ok(sys) => sys,
        Err(status) => return status.code(),
    };

    if args.first().map(String::as_str) == Some(BUILD_WORKER_FLAG) {
        let sys: Rc<dyn System> = Rc::new(sys);
        return run_worker(&sys, &args[1..]);
    }

    let sys: Rc<dyn System> = Rc::new(sys.with_writer(Rc::new(RefCell::new(StreamingStdout))));

    // Go: execute/tsc.go:52 CommandLine
    let is_build = args.first().is_some_and(|arg| {
        matches!(
            arg.to_lowercase().as_str(),
            "-b" | "--b" | "-build" | "--build"
        )
    });
    if !is_build {
        eprintln!("goport_build: only build mode (-b) is ported");
        return EXIT_UNPORTED;
    }

    let result = catch_unwind(AssertUnwindSafe(|| {
        // Go: cmd/tsgo/main.go:31 `signal.NotifyContext(context.Background(), ...)`.
        // PORT: no signal handling (plan D-W3), so the context never ends.
        tsc_build_compilation(&context::background(), sys.clone(), args, None)
    }));
    let _ = sys.writer().borrow_mut().flush();
    let code = match result {
        Ok(result) => result.status.code(),
        Err(payload) if print_go_panic(payload.as_ref()) => EXIT_GO_PANIC,
        Err(payload) => {
            note_panic(payload.as_ref());
            ExitStatus::NotImplemented.code()
        }
    };
    finish(code)
}

/// Go `os.Stdout` is not buffered: each `fmt.Fprint` reaches the terminal
/// or pipe at once. Rust stdout keeps a partial line until the next
/// newline, so this writer flushes after each write. A `-b --watch` run
/// stays in the watch loop and prints as it goes. The bytes are the Go
/// bytes of the output, as `GoOutput` (the `new_os_system` writer) writes.
struct StreamingStdout;

impl Write for StreamingStdout {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let mut stdout = std::io::stdout().lock();
        write_go_output(&mut stdout, buf)?;
        stdout.flush()?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        std::io::stdout().flush()
    }
}

/// `--build-worker <config> [command line...]`
fn run_worker(sys: &Rc<dyn System>, args: &[String]) -> i32 {
    let Some(config) = args.first() else {
        eprintln!("usage: goport_build {BUILD_WORKER_FLAG} <config> [-b command line...]");
        return EXIT_UNPORTED;
    };
    let build_command_line = &args[1..];
    let stdin = std::io::stdin();
    let fs_cache = if stdin.is_terminal() {
        Ok(CachedFsState::default())
    } else {
        read_worker_fs_cache(&mut stdin.lock())
    };
    let fs_cache = match fs_cache {
        Ok(fs_cache) => fs_cache,
        Err(message) => {
            eprintln!("goport_build: build worker: cannot read the file system cache: {message}");
            record_unported("build worker");
            report_unported();
            return EXIT_UNPORTED;
        }
    };
    let mut report_program_fs_cache = |state: &CachedFsState| {
        let line = marshal_worker_program_fs_cache(state);
        let mut stdout = std::io::stdout().lock();
        let _ = writeln!(stdout, "{line}");
        let _ = stdout.flush();
    };
    let result = catch_unwind(AssertUnwindSafe(|| {
        compile_and_emit_worker(
            sys.clone(),
            config,
            build_command_line,
            &fs_cache,
            &mut report_program_fs_cache,
            None,
        )
    }));
    match result {
        Ok(result) => {
            let line = marshal_worker_compile_result(&result);
            let mut stdout = std::io::stdout().lock();
            let _ = writeln!(stdout, "{line}");
            let _ = stdout.flush();
            // Exit `EXIT_UNPORTED` after the result line when the worker
            // reached unported code, so the orchestrator marks its run too.
            if report_unported() {
                EXIT_UNPORTED
            } else {
                ExitStatus::Success.code()
            }
        }
        // No result line. After a Go panic the orchestrator ends as Go does
        // (see `WorkerLauncher::run`); after any other panic it reports the
        // failed worker.
        Err(payload) if print_go_panic(payload.as_ref()) => {
            if report_unported() {
                EXIT_UNPORTED
            } else {
                EXIT_GO_PANIC
            }
        }
        Err(payload) => {
            note_panic(payload.as_ref());
            report_unported();
            EXIT_UNPORTED
        }
    }
}

/// Prints the unported counts and returns `code`, or `EXIT_UNPORTED` when
/// the run reached unported code.
fn finish(code: i32) -> i32 {
    if report_unported() {
        return EXIT_UNPORTED;
    }
    code
}

/// Prints `unported: <name> <count>` lines to stderr. True when any.
fn report_unported() -> bool {
    let unported = unported_report();
    let mut stderr = std::io::stderr().lock();
    for (name, count) in &unported {
        let _ = writeln!(stderr, "unported: {name} {count}");
    }
    !unported.is_empty()
}

/// Keeps unported panics quiet (they are counted) and prints other panics.
/// The run prints a Go panic.
fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
        if info.payload().is::<GoPanic>() {
            return;
        }
        let message = payload_message(info.payload());
        if message.starts_with(UNPORTED_PREFIX) {
            if std::env::var_os("GOPORT_TRACE").is_some() {
                eprintln!(
                    "trace: {message}\n{}",
                    std::backtrace::Backtrace::force_capture()
                );
            }
            return;
        }
        let location = info
            .location()
            .map(|l| format!(" at {}:{}", l.file(), l.line()))
            .unwrap_or_default();
        eprintln!("goport_build: panic{location}: {message}");
        if std::env::var_os("GOPORT_TRACE").is_some() {
            eprintln!("{}", std::backtrace::Backtrace::force_capture());
        }
    }));
}

fn payload_message(payload: &(dyn Any + Send)) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        String::new()
    }
}

fn note_panic(payload: &(dyn Any + Send)) {
    if !payload_message(payload).starts_with(UNPORTED_PREFIX) {
        record_unported("panic");
    }
}
