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
//! Not Go: when the run gets 4 KiB pages, a worker copy of the binary does
//! the work, so the exit does not wait for its memory to unmap (`launch`).
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

/// Same as `goport.rs` `JEMALLOC_CONF`. `scripts/build-release.sh` reads it
/// from this line for its BOLT runs.
#[cfg(all(target_os = "linux", target_env = "gnu", feature = "jemalloc"))]
const JEMALLOC_CONF: &str = "narenas:4,thp:always,metadata_thp:always";

/// Set in a worker (see `launch`): the number of its end of the pipe that
/// takes the exit code.
#[cfg(target_os = "linux")]
const WORKER_FD: &str = "GOPORT_WORKER_FD";

/// Set in a worker (see `launch`): the process id of its launcher.
#[cfg(target_os = "linux")]
const LAUNCHER_PID: &str = "GOPORT_LAUNCHER_PID";

// Go: cmd/tsgo/main.go:14 main
fn main() {
    // First: it must run before the first heap allocation.
    let huge_pages = ts_goport::thp_guard::thp_guard();
    #[cfg(target_os = "linux")]
    if let Some(code) = launch(huge_pages) {
        std::process::exit(code);
    }
    #[cfg(target_os = "linux")]
    if std::env::var_os(WORKER_FD).is_some() {
        end_with_launcher();
    }
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
        use std::os::unix::process::CommandExt;
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

/// Runs the work in a worker copy of this binary and returns its exit code
/// (perf16). The worker sends the code over a pipe once its output is
/// written (`exit`), so this process exits before the worker unmaps its
/// memory. With 4 KiB pages that unmap takes about 50 ms for effect (1.3 GB);
/// with huge pages it takes about 4 ms, less than a second process costs
/// (about 1 ms on query check). So by default the worker runs only when
/// `thp_guard` says the run gets 4 KiB pages (`huge_pages` false).
/// `GOPORT_LAUNCH=0` never starts a worker and `GOPORT_LAUNCH=1` always
/// does. None when this process runs the work: it is a worker, no worker is
/// wanted, `--lsp`, `--api` or watch mode (they end on their own), or the
/// worker cannot start. The launcher sends SIGINT and SIGTERM on to the
/// worker (`forward_signals`). When a signal kills the worker, the launcher
/// ends by the same signal, so the caller sees what a run without a worker
/// would give.
#[cfg(target_os = "linux")]
fn launch(huge_pages: bool) -> Option<i32> {
    use std::io::Read;
    use std::os::fd::AsRawFd;
    use std::os::unix::process::{CommandExt, ExitStatusExt};
    let wanted = match std::env::var_os("GOPORT_LAUNCH") {
        Some(v) if v == "0" => false,
        Some(v) if v == "1" => true,
        _ => !huge_pages,
    };
    if !wanted || std::env::var_os(WORKER_FD).is_some() {
        return None;
    }
    let mut args = std::env::args_os();
    let program = args.next()?;
    let args: Vec<_> = args.collect();
    // Go `getInputOptionName`: an option name has one or two leading '-'.
    let watch = |a: &std::ffi::OsString| {
        a.to_str()
            .and_then(|a| a.strip_prefix('-'))
            .map(|a| a.strip_prefix('-').unwrap_or(a))
            .is_some_and(|a| a.eq_ignore_ascii_case("watch") || a.eq_ignore_ascii_case("w"))
    };
    if args.first().is_some_and(|a| a == "--lsp" || a == "--api") || args.iter().any(watch) {
        return None;
    }
    let exe = std::env::current_exe().ok()?;
    // `pipe` sets no close-on-exec flag, so the worker gets `write` at the
    // same number. THP off (`prctl`) stays off in the worker.
    let (read, write) = rustix::pipe::pipe().ok()?;
    let mut worker = std::process::Command::new(exe)
        .arg0(program)
        .args(args)
        .env(WORKER_FD, write.as_raw_fd().to_string())
        .env(
            LAUNCHER_PID,
            rustix::process::getpid().as_raw_pid().to_string(),
        )
        .spawn()
        .ok()?;
    drop(write);
    forward_signals(&worker);
    let mut code = [0; 4];
    if std::fs::File::from(read).read_exact(&mut code).is_ok() {
        return Some(i32::from_le_bytes(code));
    }
    // The worker ended without sending a code.
    let status = worker.wait();
    if let Some(signal) = status.as_ref().ok().and_then(ExitStatusExt::signal) {
        // End by the same signal. This sets the default action of the
        // signal (the launcher catches SIGINT and SIGTERM, and Rust ignores
        // SIGPIPE) and raises it. It returns for a signal that is not in its
        // table (SIGPWR, SIGSTKFLT) or that it takes as ignored (SIGIO).
        let _ = signal_hook::low_level::emulate_default_handler(signal);
        // Such a signal has its default action here, so sending it ends
        // this process. A real-time signal has no rustix name and falls
        // through to 128 + N.
        if let Some(signal) = rustix::process::Signal::from_named_raw(signal) {
            let _ = rustix::process::kill_process(rustix::process::getpid(), signal);
        }
    }
    Some(match status {
        Ok(status) => status
            .code()
            .unwrap_or_else(|| 128 + status.signal().unwrap_or(0)),
        Err(_) => EXIT_UNPORTED,
    })
}

/// Makes a worker (see `launch`) end when its launcher ends: it sets a
/// parent-death SIGKILL. std and rustix have no safe way to set it between
/// fork and exec, so the launcher can die before this runs. Then no signal
/// comes and this process already has a new parent, so it kills itself as
/// the signal would have.
#[cfg(target_os = "linux")]
fn end_with_launcher() {
    use rustix::process::{
        Pid, Signal, getpid, getppid, kill_process, set_parent_process_death_signal,
    };
    let _ = set_parent_process_death_signal(Some(Signal::KILL));
    let launcher = std::env::var(LAUNCHER_PID)
        .ok()
        .and_then(|pid| pid.parse().ok())
        .and_then(Pid::from_raw);
    if launcher.is_some() && getppid() != launcher {
        let _ = kill_process(getpid(), Signal::KILL);
        std::process::exit(EXIT_UNPORTED);
    }
}

/// Sends each SIGINT and SIGTERM that the launcher gets on to `worker`, on
/// a thread. So a signal reaches the work as in a run without a worker:
/// `notify_context` catches it there, and a plain compile goes on, as in
/// Go. Without this, the signal would end the launcher and then the parent
/// death signal would kill the worker.
#[cfg(target_os = "linux")]
fn forward_signals(worker: &std::process::Child) {
    use signal_hook::consts::{SIGINT, SIGTERM};
    let pid = rustix::process::Pid::from_child(worker);
    let Ok(mut signals) = signal_hook::iterator::Signals::new([SIGINT, SIGTERM]) else {
        return;
    };
    let _ = std::thread::Builder::new()
        .name("forward-signals".to_string())
        .spawn(move || {
            for signal in signals.forever() {
                if let Some(signal) = rustix::process::Signal::from_named_raw(signal) {
                    let _ = rustix::process::kill_process(pid, signal);
                }
            }
        });
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

// Go: cmd/tsgo/main.go:18 runMain
// PORT: the arguments are the port form of the Go `os.Args` bytes (see
// `scanner_util::GO_STRING_MARKER`). The system writer writes the Go bytes
// of the output (`GoOutput`).
fn run_main(start: Instant) -> i32 {
    let args: Vec<String> = ts_goport::frontend::osutil::args()[1..].to_vec();

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
