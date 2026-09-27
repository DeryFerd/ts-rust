//! `tsgo`: the Go port of cmd/tsgo.
//!
//! Go: cmd/tsgo/main.go `runMain`. Every command line other than `--lsp`
//! and `--api` goes to `execute_tsc::command_line` (Go
//! `execute.CommandLine`), which parses all arguments.
//!
//! The exit code is the Go `ExitStatus` (0 to 5). Unported Go code that a
//! run reaches is listed on stderr as `unported: <name> <count>`. Such a
//! run, a panic and a failed build worker exit with `EXIT_UNPORTED` (70),
//! a code tsgo never returns, like the other goport bins. A Go panic that
//! the port keeps (`core::go_panic`), also in a build worker, ends the run
//! as in Go: the output so far, `panic: <message>` on stderr and exit 2.
//!
//! `--lsp` and `--api` run `cmd::tsgo::lsp::run_lsp` and
//! `cmd::tsgo::api::run_api` (Go cmd/tsgo/lsp.go and api.go), the entry
//! points that `goport --lsp` and `goport --api` run too.
//!
//! Go `signal.NotifyContext(ctx, SIGINT, SIGTERM)` is
//! `cmd::tsgo::main::notify_context`. Only watch and build mode read the
//! context; a plain compile goes on after a signal, as in Go.
//! PORT: Go `core.ApplyDebugStackLimit` (`TS_GO_DEBUG_STACK_LIMIT`) is a
//! debug setting and is skipped. The work runs on a thread with a 1 GiB
//! stack, like the other goport bins.
//! PORT: Go `osSys` and `newSystem` (cmd/tsgo/sys.go) are ported as
//! `OsSystem` and `new_os_system` in execute/tsc/compile.rs.
//! PORT: `enablevtprocessing_windows.go` (the Windows console) is not
//! ported.

use std::any::Any;
use std::io::{IsTerminal, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

use ts_goport::cmd::tsgo::api::run_api;
use ts_goport::cmd::tsgo::lsp::run_lsp;
use ts_goport::cmd::tsgo::main::notify_context;
use ts_goport::execute::build::worker::{
    BUILD_WORKER_FLAG, compile_and_emit_worker, marshal_worker_compile_result,
    marshal_worker_program_fs_cache, read_worker_fs_cache,
};
use ts_goport::execute::execute_tsc::{GoTsc, command_line};
use ts_goport::execute::tsc::{EXIT_UNPORTED, ExitStatus, System, new_os_system};
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

// Go: cmd/tsgo/main.go:13 main
fn main() {
    // One budget sets the parse and bind threads and the malloc arenas.
    // tsgo has one more thread with an arena than goport: the
    // `notify_context` signal thread.
    let budget = ThreadBudget::one_program(1);
    set_malloc_tunables(&budget);
    budget.install();
    // Go: `System.SinceStart` counts from the process start. The tunables
    // step above may exec the binary again, so the clock starts after it.
    let start = Instant::now();
    install_panic_hook();
    // The thread ends the process itself once `run_main` has written the
    // output, so the exit does not wait for the thread stacks (1 GiB each)
    // to unmap, the thread-local destructors or the join.
    let work = std::thread::Builder::new()
        .name("tsgo".to_string())
        .stack_size(STACK_SIZE)
        .spawn(move || std::process::exit(run_main(start)));
    // Reached only when the thread cannot start or `run_main` panics.
    let _ = work.map(std::thread::JoinHandle::join);
    eprintln!("tsgo: work thread failed");
    std::process::exit(EXIT_UNPORTED);
}

/// Copied from `goport.rs` `set_malloc_tunables`, which explains the
/// values. `arena_max` comes from `budget` (`ThreadBudget::one_program`):
/// with the signal thread it is 7 here, and 10 at 8 or more cores (3 spare
/// arenas for the parse workers that a large program adds). At 6, two
/// checkers share one arena lock (zod: 3.9k voluntary context switches,
/// 0.5k at 7). Build workers inherit the variable, so they do not exec
/// again.
fn set_malloc_tunables(budget: &ThreadBudget) {
    // Unused off Linux and with jemalloc.
    let _ = budget;
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    {
        use std::os::unix::process::CommandExt;
        #[cfg(not(feature = "jemalloc"))]
        let (name, value) = ("GLIBC_TUNABLES", budget.glibc_tunables());
        #[cfg(feature = "jemalloc")]
        let (name, value) = ("_RJEM_MALLOC_CONF", String::from("narenas:4"));
        if std::env::var_os(name).is_some() {
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
        let _ = command.args(args).env(name, value).exec();
    }
}

// Go: cmd/tsgo/main.go:17 runMain
// PORT: the arguments are the port form of the Go `os.Args` bytes (see
// `scanner_util::GO_STRING_MARKER`). The system writer writes the Go bytes
// of the output (`GoOutput`).
fn run_main(start: Instant) -> i32 {
    let args: Vec<String> = ts_goport::frontend::vfs::os_args();

    // PORT: a `-b` build runs each project in a worker process. The
    // orchestrator re-runs this binary with `BUILD_WORKER_FLAG` first
    // (`WorkerLauncher::current`). Go runs build tasks in-process and has
    // no such flag. Any other command line with the flag goes on to
    // `command_line`, which reports it as unknown (TS5023) like Go.
    if let Some((config, build_command_line)) = worker_args(&args) {
        return run_worker(start, config, build_command_line);
    }

    if let Some(first) = args.first() {
        match first.as_str() {
            "--lsp" => return finish(catch_unwind(AssertUnwindSafe(|| run_lsp(&args[1..])))),
            "--api" => return finish(catch_unwind(AssertUnwindSafe(|| run_api(&args[1..])))),
            _ => {}
        }
    }

    // Go: ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGINT, syscall.SIGTERM)
    let (ctx, stop) = notify_context(&context::background());
    // PORT: Go `newSystem()` calls `os.Exit` on this error, so `stop` does
    // not run there either.
    let sys = match new_os_system() {
        Ok(sys) => sys,
        Err(status) => return status.code(),
    };
    let sys: Rc<dyn System> = Rc::new(sys.with_start(start));
    let result = catch_unwind(AssertUnwindSafe(|| {
        command_line(&ctx, sys.clone(), &args, &GoTsc).status.code()
    }));
    // Go: defer stop()
    stop();
    // `--showConfig` output has no trailing newline, and
    // `std::process::exit` runs no destructors, so flush here.
    let _ = sys.writer().borrow_mut().flush();
    finish(result)
}

/// The config and `-b` command line of a build worker run, in the shape
/// `WorkerLauncher::run` passes them: `--build-worker <config>` and then
/// the orchestrator's command line, which starts with a build flag (Go
/// execute/tsc.go:53 `CommandLine`). `None` for any other command line.
fn worker_args(args: &[String]) -> Option<(&str, &[String])> {
    match args {
        [flag, config, build_command_line @ ..]
            if flag.as_str() == BUILD_WORKER_FLAG
                && build_command_line.first().is_some_and(|first| {
                    matches!(
                        first.to_lowercase().as_str(),
                        "-b" | "--b" | "-build" | "--build"
                    )
                }) =>
        {
            Some((config.as_str(), build_command_line))
        }
        _ => None,
    }
}

/// `--build-worker <config> <the -b command line...>`. Copied from
/// `goport_build.rs` `run_worker`.
fn run_worker(start: Instant, config: &str, build_command_line: &[String]) -> i32 {
    let sys = match new_os_system() {
        Ok(sys) => sys,
        Err(status) => return status.code(),
    };
    let sys: Rc<dyn System> = Rc::new(sys.with_start(start));
    let stdin = std::io::stdin();
    let fs_cache = if stdin.is_terminal() {
        Ok(CachedFsState::default())
    } else {
        read_worker_fs_cache(&mut stdin.lock())
    };
    let fs_cache = match fs_cache {
        Ok(fs_cache) => fs_cache,
        Err(message) => {
            eprintln!("tsgo: build worker: cannot read the file system cache: {message}");
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

/// Prints a Go panic and the unported counts and returns the exit code:
/// `EXIT_UNPORTED` when the run panicked or reached unported code,
/// `EXIT_GO_PANIC` after a Go panic, else `result`.
fn finish(result: std::thread::Result<i32>) -> i32 {
    let code = match result {
        Ok(code) => code,
        Err(payload) if print_go_panic(payload.as_ref()) => EXIT_GO_PANIC,
        Err(payload) => {
            note_panic(payload.as_ref());
            EXIT_UNPORTED
        }
    };
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
        eprintln!("tsgo: panic{location}: {message}");
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

/// Counts a caught panic. Unported panics already counted themselves; any
/// other panic is counted as `panic`.
fn note_panic(payload: &(dyn Any + Send)) {
    if !payload_message(payload).starts_with(UNPORTED_PREFIX) {
        record_unported("panic");
    }
}
