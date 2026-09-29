//! `tsgo`: the Go port of cmd/tsgo.
//!
//! Go: cmd/tsgo/main.go `runMain`. Every command line other than `--lsp`
//! and `--api` goes to `execute_tsc::command_line` (Go
//! `execute.CommandLine`), which parses all arguments.
//!
//! The exit code is the Go `ExitStatus` (0 to 5). Unported Go code that a
//! run reaches is listed on stderr as `unported: <name> <count>`. Such a
//! run and a panic exit with `EXIT_UNPORTED` (70), a code tsgo never
//! returns, like the other goport bins. A Go panic that the port keeps
//! (`core::go_panic`) ends the run as in Go: the output so far,
//! `panic: <message>` on stderr and exit 2.
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
use std::io::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

use ts_goport::cmd::tsgo::api::run_api;
use ts_goport::cmd::tsgo::lsp::run_lsp;
use ts_goport::cmd::tsgo::main::notify_context;
use ts_goport::execute::execute_tsc::{GoTsc, command_line};
use ts_goport::execute::tsc::{EXIT_UNPORTED, System, new_os_system};
use ts_goport::gostd::context;
use ts_goport::prelude::*;

const UNPORTED_PREFIX: &str = "unported Go code";

/// Stack size for the main work thread. The checker recurses deeply on
/// large projects.
const STACK_SIZE: usize = 1 << 30;

/// jemalloc is the global allocator (default feature `jemalloc`). A build
/// without the feature uses glibc malloc. See `goport.rs`
/// `set_malloc_tunables`.
#[cfg(feature = "jemalloc")]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

/// The jemalloc settings at start, without huge pages: jemalloc maps and
/// touches its first memory before `main`, and a huge page fault there
/// waits in compaction on fragmented memory (perf16: about 10 ms).
/// `early_thp_conf` then picks `JEMALLOC_THP_CONF` for the work when THP
/// stays on. `scripts/build-release.sh` reads this line: it builds the value
/// into jemalloc and sets it for its BOLT runs.
#[cfg(all(target_os = "linux", target_env = "gnu", feature = "jemalloc"))]
const JEMALLOC_CONF: &str = "narenas:4,thp:default,metadata_thp:disabled";

/// The jemalloc settings of a run that keeps THP. Same as `goport.rs`
/// `JEMALLOC_CONF`, which explains them.
#[cfg(all(target_os = "linux", target_env = "gnu", feature = "jemalloc"))]
const JEMALLOC_THP_CONF: &str = "narenas:4,thp:always,metadata_thp:always";

/// Set in a worker (see `launch`): the number of its end of the pipe that
/// takes the exit code.
#[cfg(target_os = "linux")]
const WORKER_FD: &str = "GOPORT_WORKER_FD";

// Go: cmd/tsgo/main.go:13 main
fn main() {
    // First: before the first large allocation.
    let thp_conf = early_thp_conf();
    #[cfg(target_os = "linux")]
    if let Some(code) = launch(thp_conf) {
        std::process::exit(code);
    }
    #[cfg(all(target_os = "linux", target_env = "gnu", feature = "jemalloc"))]
    if let Some(conf) = thp_conf {
        exec_self("_RJEM_MALLOC_CONF", conf);
    }
    // A worker ends when its launcher is killed.
    #[cfg(target_os = "linux")]
    if std::env::var_os(WORKER_FD).is_some() {
        let _ =
            rustix::process::set_parent_process_death_signal(Some(rustix::process::Signal::KILL));
    }
    ts_goport::thp_guard::thp_guard();
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
        .spawn(move || exit(run_main(start)));
    // Reached only when the thread cannot start or `run_main` panics.
    let _ = work.map(std::thread::JoinHandle::join);
    eprintln!("tsgo: work thread failed");
    std::process::exit(EXIT_UNPORTED);
}

/// Copied from `goport.rs` `set_malloc_tunables`, which explains the
/// values. jemalloc gets `JEMALLOC_CONF`. With glibc malloc, `arena_max`
/// comes from `budget` (`ThreadBudget::one_program`): with the signal thread
/// it is 7 here, and 10 at 8 or more cores (3 spare arenas for the parse
/// workers that a large program adds). At 6, two checkers share one arena
/// lock (zod: 3.9k voluntary context switches, 0.5k at 7). The variable
/// stays set, so the exec runs once. A jemalloc build with `JEMALLOC_CONF`
/// built in does not exec.
fn set_malloc_tunables(budget: &ThreadBudget) {
    // Unused off Linux and with jemalloc.
    let _ = budget;
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    {
        // A build with `JEMALLOC_CONF` built into jemalloc
        // (`JEMALLOC_SYS_WITH_MALLOC_CONF`, set by `scripts/build-release.sh`)
        // needs no exec: jemalloc reads it at its start, and
        // `_RJEM_MALLOC_CONF` still overrides it.
        #[cfg(feature = "jemalloc")]
        if option_env!("JEMALLOC_SYS_WITH_MALLOC_CONF") == Some(JEMALLOC_CONF) {
            return;
        }
        #[cfg(not(feature = "jemalloc"))]
        let (name, value) = ("GLIBC_TUNABLES", budget.glibc_tunables());
        #[cfg(feature = "jemalloc")]
        let (name, value) = ("_RJEM_MALLOC_CONF", String::from(JEMALLOC_CONF));
        if std::env::var_os(name).is_some() {
            return;
        }
        exec_self(name, &value);
    }
}

/// Runs this binary again in this process, with the same arguments and
/// `name` set to `value`. Returns only when the exec fails.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
fn exec_self(name: &str, value: &str) {
    use std::os::unix::process::CommandExt;
    let Ok(exe) = std::env::current_exe() else {
        return;
    };
    let mut args = std::env::args_os();
    let mut command = std::process::Command::new(exe);
    if let Some(arg0) = args.next() {
        command.arg0(arg0);
    }
    let _ = command.args(args).env(name, value).exec();
}

/// Decides THP before jemalloc maps its large memory (perf16 option 2). The
/// THP guard start check runs here, and on fragmented memory it turns THP
/// off for this process and its children. When THP stays on and
/// `_RJEM_MALLOC_CONF` is not set (by the user, or by `launch` or the exec
/// in `main` for this process), returns the settings that the work must
/// run with.
fn early_thp_conf() -> Option<&'static str> {
    #[cfg(all(target_os = "linux", target_env = "gnu", feature = "jemalloc"))]
    if std::env::var_os("_RJEM_MALLOC_CONF").is_none() && ts_goport::thp_guard::thp_start_check() {
        return Some(JEMALLOC_THP_CONF);
    }
    None
}

/// Runs the work in a worker copy of this binary and returns its exit code
/// (perf16 option 1). The worker sends the code over a pipe once its output
/// is written (`exit`), so this process exits before the worker unmaps its
/// memory: 1.3 GB of 4 KiB pages takes about 50 ms at exit. The worker gets
/// `thp_conf` as `_RJEM_MALLOC_CONF`. None when this process runs the work:
/// it is a worker, `GOPORT_LAUNCH=0`, `--lsp`, `--api` or watch mode (they
/// end on their own), or the worker cannot start.
#[cfg(target_os = "linux")]
fn launch(thp_conf: Option<&str>) -> Option<i32> {
    use std::io::Read;
    use std::os::fd::AsRawFd;
    use std::os::unix::process::{CommandExt, ExitStatusExt};
    if std::env::var_os(WORKER_FD).is_some()
        || std::env::var_os("GOPORT_LAUNCH").is_some_and(|v| v == "0")
    {
        return None;
    }
    let mut args = std::env::args_os();
    let arg0 = args.next()?;
    let args: Vec<_> = args.collect();
    let watch = |a: &std::ffi::OsString| {
        a.to_str()
            .is_some_and(|a| a.eq_ignore_ascii_case("--watch") || a.eq_ignore_ascii_case("-w"))
    };
    if args.first().is_some_and(|a| a == "--lsp" || a == "--api") || args.iter().any(watch) {
        return None;
    }
    let exe = std::env::current_exe().ok()?;
    // `pipe` sets no close-on-exec flag, so the worker gets `write` at the
    // same number.
    let (read, write) = rustix::pipe::pipe().ok()?;
    let mut command = std::process::Command::new(exe);
    command
        .arg0(arg0)
        .args(args)
        .env(WORKER_FD, write.as_raw_fd().to_string());
    if let Some(conf) = thp_conf {
        command.env("_RJEM_MALLOC_CONF", conf);
    }
    let mut worker = command.spawn().ok()?;
    drop(write);
    let mut code = [0; 4];
    if std::fs::File::from(read).read_exact(&mut code).is_ok() {
        return Some(i32::from_le_bytes(code));
    }
    // The worker ended without sending a code.
    Some(match worker.wait() {
        Ok(status) => status
            .code()
            .unwrap_or_else(|| 128 + status.signal().unwrap_or(0)),
        Err(_) => EXIT_UNPORTED,
    })
}

/// Ends the process with `code`. A worker (see `launch`) first points its
/// stdout and stderr at /dev/null, so a reader of the launcher's output
/// gets its end of file, and sends the code.
fn exit(code: i32) -> ! {
    #[cfg(target_os = "linux")]
    if let Some(fd) = std::env::var_os(WORKER_FD) {
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
        if let Ok(null) = std::fs::File::options().write(true).open("/dev/null") {
            let _ = rustix::stdio::dup2_stdout(&null);
            let _ = rustix::stdio::dup2_stderr(&null);
        }
        // The inherited end of the pipe, opened again by its number.
        if let Some(fd) = fd.to_str().and_then(|fd| fd.parse::<u32>().ok())
            && let Ok(mut pipe) = std::fs::File::options()
                .write(true)
                .open(format!("/proc/self/fd/{fd}"))
        {
            let _ = pipe.write_all(&code.to_le_bytes());
        }
    }
    std::process::exit(code)
}

// Go: cmd/tsgo/main.go:17 runMain
// PORT: the arguments are the port form of the Go `os.Args` bytes (see
// `scanner_util::GO_STRING_MARKER`). The system writer writes the Go bytes
// of the output (`GoOutput`).
fn run_main(start: Instant) -> i32 {
    let args: Vec<String> = ts_goport::frontend::vfs::os_args();

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
