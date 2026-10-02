//! `tsgo`: the Go port of cmd/tsc.
//!
//! Go: cmd/tsc/main.go `runMain`. Every command line other than `--lsp`
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
//! `cmd::tsgo::api::run_api` (Go cmd/tsc/lsp.go and api.go), the entry
//! points that `goport --lsp` and `goport --api` run too.
//!
//! Go `signal.NotifyContext(ctx, SIGINT, SIGTERM)` is
//! `cmd::tsgo::main::notify_context`. Only watch and build mode read the
//! context; a plain compile goes on after a signal, as in Go.
//! Not Go: when the run gets 4 KiB pages, a worker copy of the binary does
//! the work, so the exit does not wait for its memory to unmap (`launch`).
//!
//! As the Go runtime does at start (`go_runtime_start`): the signals that Go
//! drops get a handler that does nothing, SIGQUIT prints its name and exits
//! 2, and the soft open-file limit goes up (PORTING.md "Process start").
//! PORT: Go `core.ApplyDebugStackLimit` (`TS_GO_DEBUG_STACK_LIMIT`) is a
//! debug setting and is skipped. The work runs on a thread with the stack
//! size of `gostd::stack::max_stack_size` (1 GiB with no address space or
//! data limit), like the other goport bins.
//! PORT: Go `osSys` and `newSystem` (cmd/tsc/sys.go) are ported as
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

/// jemalloc is the global allocator (default feature `jemalloc`). A build
/// without the feature uses glibc malloc. See `goport.rs`
/// `set_malloc_tunables`.
#[cfg(all(feature = "jemalloc", not(windows)))]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

/// Same as `goport.rs` `JEMALLOC_CONF`. `scripts/build-release.sh` reads it
/// from this line for its BOLT runs.
#[cfg(all(target_os = "linux", target_env = "gnu", feature = "jemalloc"))]
const JEMALLOC_CONF: &str = "narenas:4,thp:always,metadata_thp:disabled,cache_oblivious:false";

/// The `arg0` of a worker (see `launch`) is this word, the launcher's
/// process id, and the number, device and inode of the launcher's end of
/// the pipe that takes the exit code: `tsgo-worker 4242 3 15 81234`. The
/// arguments, not the environment, name a worker, so a process that the
/// worker starts gets nothing of it.
#[cfg(target_os = "linux")]
const WORKER_ARG0: &str = "tsgo-worker";

/// A worker's link to its launcher (see `launch`).
#[cfg(target_os = "linux")]
#[derive(Clone, Copy)]
struct Worker {
    /// The number of the launcher's end of the pipe that takes the exit code.
    fd: u32,
    /// The device and inode of that pipe.
    dev: u64,
    ino: u64,
    /// The launcher.
    launcher: rustix::process::Pid,
}

// Go: cmd/tsc/main.go:14 main
fn main() {
    // First: it must run before the first heap allocation.
    let huge_pages = ts_goport::thp_guard::thp_guard();
    #[cfg(target_os = "linux")]
    if let Some(code) = launch(huge_pages) {
        std::process::exit(code);
    }
    // Unused off Linux (`launch` is Linux only).
    #[cfg(not(target_os = "linux"))]
    let _ = huge_pages;
    // A worker gets its parent-death signal here, or ends when its
    // launcher has ended (`worker`).
    #[cfg(target_os = "linux")]
    let _ = worker();
    // One budget sets the parse and bind threads and the malloc arenas.
    // tsgo has one more thread with an arena than goport: the
    // `notify_context` signal thread.
    let budget = ThreadBudget::one_program(1);
    set_malloc_tunables(&budget);
    budget.install();
    // After the exec in `set_malloc_tunables`: an exec resets the handlers,
    // and a raised limit would read as the original one there.
    go_runtime_start();
    // Go: `System.SinceStart` counts from the process start. The tunables
    // step above may exec the binary again, so the clock starts after it.
    let start = Instant::now();
    install_panic_hook();
    // The thread ends the process itself once `run_main` has written the
    // output, so the exit does not wait for the thread stacks (up to 1 GiB
    // each, `max_stack_size`) to unmap, the thread-local destructors or the
    // join. Go runs `runMain` on the main goroutine. A thread that cannot
    // start ends the process as the Go runtime does (`GoThread`).
    let work = ts_goport::core::GoThread::new()
        .name("tsgo".to_string())
        .stack_size(ts_goport::gostd::stack::max_stack_size())
        .spawn(move || exit(run_main(start)));
    // Reached only when `run_main` panics.
    let _ = work.join();
    eprintln!("tsgo: work thread failed");
    std::process::exit(EXIT_UNPORTED);
}

/// Copied from `goport.rs` `set_malloc_tunables`, which explains the
/// values. jemalloc gets `JEMALLOC_CONF`. With glibc malloc, `arena_max`
/// comes from `budget` (`ThreadBudget::one_program`): with the signal thread
/// it is 7 here, and 10 at 8 or more cores (3 spare arenas for the parse
/// workers that a large program adds). At 6, two checkers share one arena
/// lock (zod: 3.9k voluntary context switches, 0.5k at 7). Under an address
/// space or data limit, glibc malloc gets `arena_max=1`, with jemalloc too.
/// The variables stay set, so the exec runs once. A jemalloc build with
/// `JEMALLOC_CONF` built in execs only under a limit.
fn set_malloc_tunables(budget: &ThreadBudget) {
    // Unused off Linux.
    let _ = budget;
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    {
        use std::os::unix::process::CommandExt;
        let mut vars = Vec::new();
        // A build with `JEMALLOC_CONF` built into jemalloc
        // (`JEMALLOC_SYS_WITH_MALLOC_CONF`, set by `scripts/build-release.sh`)
        // needs no exec for it: jemalloc reads it at its start, and
        // `_RJEM_MALLOC_CONF` still overrides it.
        #[cfg(feature = "jemalloc")]
        if option_env!("JEMALLOC_SYS_WITH_MALLOC_CONF") != Some(JEMALLOC_CONF) {
            vars.push(("_RJEM_MALLOC_CONF", String::from(JEMALLOC_CONF)));
        }
        if let Some(value) = budget.glibc_tunables() {
            vars.push(("GLIBC_TUNABLES", value));
        }
        vars.retain(|(name, _)| std::env::var_os(name).is_none());
        if vars.is_empty() {
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
        let _ = command.args(args).envs(vars).exec();
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
/// wanted, `--lsp`, `--api` or watch mode (`long_running`: they end on
/// their own), or the worker cannot start. The launcher sends SIGINT,
/// SIGTERM and the signals that Go throws on to the worker
/// (`forward_signals`), and drops the signals that Go drops. When a signal
/// kills the worker, the launcher ends by the same signal, so the caller
/// sees what a run without a worker would give.
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
    if !wanted || worker().is_some() || ts_goport::thp_guard::long_running() {
        return None;
    }
    let mut args = std::env::args_os();
    args.next()?;
    let args: Vec<_> = args.collect();
    let exe = std::env::current_exe().ok()?;
    // Both ends keep their close-on-exec flag, so the worker and the
    // processes it starts get neither. The worker opens `write` again by
    // the number of `read` (`exit`). THP off (`prctl`) stays off in the
    // worker.
    let (read, write) = rustix::pipe::pipe_with(rustix::pipe::PipeFlags::CLOEXEC).ok()?;
    let launcher = rustix::process::getpid().as_raw_pid();
    let stat = rustix::fs::fstat(&read).ok()?;
    // Before the worker starts, so a failed start leaves no worker behind.
    let forward = forward_signals();
    drop_go_signals();
    let started = std::process::Command::new(exe)
        .arg0(format!(
            "{WORKER_ARG0} {launcher} {} {} {}",
            read.as_raw_fd(),
            stat.st_dev,
            stat.st_ino
        ))
        .args(args)
        .spawn();
    let Ok(mut worker) = started else {
        // No worker: this process runs the work. `forward` drops here, so
        // its thread ends.
        restore_default_actions();
        return None;
    };
    if let Some(forward) = forward {
        let _ = forward.send(rustix::process::Pid::from_child(&worker));
    }
    // `write` stays open until the worker ends, so the read below ends when
    // the code comes or when the worker has ended without it. The thread
    // does not reap the worker (`NOWAIT`): `wait` below does. When the
    // thread cannot start, `write` closes now and the read ends at once:
    // the launcher then takes the code from the worker's exit, which waits
    // for the worker's memory to unmap. No code or signal is lost, so this
    // port-only thread falls back instead of ending the run (`GoThread`).
    let pid = rustix::process::Pid::from_child(&worker);
    let _ = std::thread::Builder::new()
        .name("worker-exit".to_string())
        .spawn(move || {
            use rustix::process::{WaitId, WaitIdOptions, waitid};
            let options = WaitIdOptions::EXITED | WaitIdOptions::NOWAIT;
            while let Err(rustix::io::Errno::INTR) = waitid(WaitId::Pid(pid), options) {}
            drop(write);
        });
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

/// This process as a worker (see `launch`): its `arg0` is `WORKER_ARG0`
/// with a launcher and its pipe, and its parent is that launcher. The
/// first call decides, at the start of `main`. A worker gets a
/// parent-death SIGKILL, so it ends when its launcher ends, as a killed Go
/// tsgo stops at once.
/// A process whose `arg0` names a launcher that is not its parent runs as
/// a plain tsgo, unless that launcher has ended (`has_ended`). Then this
/// process is the launcher's worker and the launcher died before the
/// parent check (a SIGKILL soon after the start), so it kills itself, as
/// the parent-death signal would have. std and rustix have no safe way to
/// set that signal between fork and exec, so the launcher can also die
/// after the check and before the signal is set: the second parent check
/// finds that.
#[cfg(target_os = "linux")]
fn worker() -> Option<Worker> {
    use rustix::process::{Signal, getpid, getppid, kill_process, set_parent_process_death_signal};
    static WORKER: std::sync::OnceLock<Option<Worker>> = std::sync::OnceLock::new();
    *WORKER.get_or_init(|| {
        let arg0 = std::env::args_os().next()?;
        let rest = arg0
            .to_str()?
            .strip_prefix(WORKER_ARG0)?
            .strip_prefix(' ')?;
        let mut fields = rest.split(' ');
        let launcher = rustix::process::Pid::from_raw(fields.next()?.parse().ok()?)?;
        let fd = fields.next()?.parse().ok()?;
        let dev = fields.next()?.parse().ok()?;
        let ino = fields.next()?.parse().ok()?;
        if fields.next().is_some() {
            return None;
        }
        if getppid() == Some(launcher) {
            let _ = set_parent_process_death_signal(Some(Signal::KILL));
            if getppid() == Some(launcher) {
                return Some(Worker {
                    fd,
                    dev,
                    ino,
                    launcher,
                });
            }
        } else if !has_ended(launcher) {
            return None;
        }
        let _ = kill_process(getpid(), Signal::KILL);
        std::process::exit(EXIT_UNPORTED)
    })
}

/// Whether the process `pid` has ended: it is gone, or it is a zombie (it
/// has ended and its parent has not reaped it yet). The state is the field
/// after the command name in /proc/<pid>/stat. Without that file, or
/// without this process's own /proc (`own_proc`: there the file is of
/// another process), `kill` with no signal tells only whether the process
/// is gone: a zombie launcher then gives a plain tsgo.
#[cfg(target_os = "linux")]
fn has_ended(pid: rustix::process::Pid) -> bool {
    let path = format!("/proc/{}/stat", pid.as_raw_pid());
    match own_proc().then(|| std::fs::read(path)) {
        // `<pid> (<name>) <state> ...`: the name can hold ") ".
        Some(Ok(stat)) => {
            let name_end = stat.iter().rposition(|&b| b == b')');
            let state = name_end.and_then(|end| stat.get(end + 2));
            matches!(state, Some(b'Z' | b'X'))
        }
        _ => rustix::process::test_kill_process(pid) == Err(rustix::io::Errno::SRCH),
    }
}

/// Whether /proc is the /proc of this process's PID namespace, so that
/// /proc/<pid> is the process `pid`. In a PID namespace that has the /proc
/// of another one (`bwrap --unshare-pid` without `--proc`, `unshare -pf`
/// without `--mount-proc`), /proc/<pid> is another process or none: for
/// the pid of a worker it can be a kernel thread whose parent has the pid
/// of the launcher. The NSpid line of /proc/self/status has this process's
/// pid in each PID namespace from the one of /proc down to its own, so it
/// is the one pid that `getpid` gives only in its own /proc. A kernel
/// without that line (before 4.1) has the Pid line, the pid in the
/// namespace of /proc. False without /proc. The first call reads the file;
/// the later calls use its result.
#[cfg(target_os = "linux")]
fn own_proc() -> bool {
    static OWN: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *OWN.get_or_init(|| {
        let Ok(status) = std::fs::read_to_string("/proc/self/status") else {
            return false;
        };
        let pid = rustix::process::getpid().as_raw_pid().to_string();
        let field = |name: &str| status.lines().find_map(|line| line.strip_prefix(name));
        match field("NSpid:") {
            Some(pids) => pids.split_whitespace().eq([pid.as_str()]),
            None => field("Pid:").map(str::trim) == Some(pid.as_str()),
        }
    })
}

/// Sends each SIGINT and SIGTERM and each signal that Go throws
/// (`GO_THROWN`) that the launcher gets on to the worker, on a thread. So a
/// signal reaches the work as in a run without a worker: `notify_context`
/// catches SIGINT and SIGTERM there, and a plain compile goes on, as in
/// Go; SIGQUIT prints its name there once, also when it went to the whole
/// process group. Without this, the signal would end the launcher and then
/// the parent-death signal would kill the worker.
/// `launch` calls it before it starts the worker and sends the worker's pid
/// to the returned sender; a signal that comes first waits for it. When no
/// worker starts, `launch` drops the sender and the thread ends. Each
/// signal also waits until the worker catches it (`wait_until_caught`),
/// only with this process's own /proc (`own_proc`). Otherwise it goes on
/// at once.
/// The thread starts as a Go runtime thread does (`GoThread`): when the OS
/// refuses it, the launcher ends with Go's text and exit 2, before there is
/// a worker. Go has no launcher, so its process gets every signal; a
/// launcher that went on without this thread would drop them (dropping
/// `signals` removes their actions, not their handlers).
#[cfg(target_os = "linux")]
fn forward_signals() -> Option<std::sync::mpsc::Sender<rustix::process::Pid>> {
    use signal_hook::consts::{SIGINT, SIGTERM};
    let thrown = GO_THROWN.iter().map(|(signal, _)| signal.as_raw());
    let mut signals =
        signal_hook::iterator::Signals::new([SIGINT, SIGTERM].into_iter().chain(thrown)).ok()?;
    let (send, receive) = std::sync::mpsc::channel();
    ts_goport::core::GoThread::new()
        .name("forward-signals".to_string())
        .spawn(move || {
            let Ok(pid) = receive.recv() else {
                return;
            };
            let hold = own_proc();
            for signal in signals.forever() {
                if let Some(signal) = rustix::process::Signal::from_named_raw(signal) {
                    if hold {
                        wait_until_caught(pid, signal);
                    }
                    let _ = rustix::process::kill_process(pid, signal);
                }
            }
        });
    Some(send)
}

/// Waits until the worker `pid` catches `signal`, so a forwarded signal
/// finds the handlers that the worker sets at its start
/// (`go_runtime_start`, `notify_context`) and does not end it by the
/// default action. A signal that came before them (soon after the start,
/// or while the start of `forward_signals` was tried again) waits here: Go
/// sets its handlers before `main`, and `runMain` calls `NotifyContext`
/// before any work (cmd/tsc/main.go:29).
/// The kernel lists the caught signals in /proc/<pid>/status (`SigCgt`, a
/// hex mask with bit N-1 for signal N). The caller calls it only with
/// this process's own /proc (`own_proc`). The wait ends when the worker has
/// ended, and at once when that file does not show a live child of this
/// process: the signal then goes on at once.
#[cfg(target_os = "linux")]
fn wait_until_caught(pid: rustix::process::Pid, signal: rustix::process::Signal) {
    let path = format!("/proc/{}/status", pid.as_raw_pid());
    let launcher = rustix::process::getpid().as_raw_pid().to_string();
    let bit = 1u64 << (signal.as_raw() - 1).unsigned_abs();
    while let Ok(status) = std::fs::read_to_string(&path) {
        let field = |name: &str| {
            status
                .lines()
                .find_map(|line| line.strip_prefix(name))
                .map(str::trim)
        };
        let child = field("PPid:") == Some(launcher.as_str());
        let live = field("State:").is_some_and(|state| !state.starts_with(['Z', 'X']));
        match field("SigCgt:").and_then(|mask| u64::from_str_radix(mask, 16).ok()) {
            Some(caught) if child && live && caught & bit == 0 => {
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
            _ => return,
        }
    }
}

/// Gives SIGINT, SIGTERM and the signals that Go throws (`GO_THROWN`) their
/// default actions back when `launch` starts no worker after
/// `forward_signals` took them: dropping its `Signals` removes their
/// actions, not their handlers, so they would do nothing until the run
/// sets its own handlers. A run that never was a launcher has the default
/// actions there. Each one does its default action while its flag is set
/// (`register_conditional_default`); `go_runtime_start` and `run_main`
/// clear the flags once their handlers are set (`end_default_actions`).
/// PORT: std and rustix have no safe `SIG_DFL`; signal-hook sets it and
/// raises the signal again. SIGSTKFLT is not in signal-hook's table, so
/// it does nothing there until `go_runtime_start`.
#[cfg(target_os = "linux")]
fn restore_default_actions() {
    use signal_hook::consts::{SIGINT, SIGTERM};
    use signal_hook::flag::register_conditional_default;
    let set = || std::sync::Arc::new(std::sync::atomic::AtomicBool::new(true));
    let notify = NOTIFY_DEFAULT.get_or_init(set);
    let thrown = THROWN_DEFAULT.get_or_init(set);
    for signal in [SIGINT, SIGTERM] {
        let _ = register_conditional_default(signal, notify.clone());
    }
    for (signal, _) in GO_THROWN {
        let _ = register_conditional_default(signal.as_raw(), thrown.clone());
    }
}

/// The flags of the default actions of SIGINT and SIGTERM
/// (`NOTIFY_DEFAULT`) and of the signals that Go throws (`THROWN_DEFAULT`),
/// set only by `restore_default_actions`.
#[cfg(target_os = "linux")]
static NOTIFY_DEFAULT: std::sync::OnceLock<std::sync::Arc<std::sync::atomic::AtomicBool>> =
    std::sync::OnceLock::new();
#[cfg(target_os = "linux")]
static THROWN_DEFAULT: std::sync::OnceLock<std::sync::Arc<std::sync::atomic::AtomicBool>> =
    std::sync::OnceLock::new();

/// Ends the default actions of `restore_default_actions` that `flag` sets,
/// once the run has set its own handlers for those signals.
#[cfg(target_os = "linux")]
fn end_default_actions(flag: &std::sync::OnceLock<std::sync::Arc<std::sync::atomic::AtomicBool>>) {
    if let Some(flag) = flag.get() {
        flag.store(false, std::sync::atomic::Ordering::SeqCst);
    }
}

/// Signals that the Go runtime catches and drops when no `signal.Notify`
/// asks for them: `_SigNotify` alone or with `_SigUnblock` in
/// `runtime/sigtab_linux_generic.go` (go1.27.1). The real-time signals 35 to
/// 64 (`GO_DROPPED_RT`) are such signals too; Go leaves 32 to 34 to the C
/// library. SIGPIPE is apart: Go has its own rule for stdout and stderr.
#[cfg(target_os = "linux")]
const GO_DROPPED: [rustix::process::Signal; 9] = {
    use rustix::process::Signal;
    [
        Signal::USR1,
        Signal::USR2,
        Signal::ALARM,
        Signal::XCPU,
        Signal::XFSZ,
        Signal::VTALARM,
        Signal::PROF,
        Signal::IO,
        Signal::POWER,
    ]
};

/// The real-time signals that Go drops (see `GO_DROPPED`).
#[cfg(target_os = "linux")]
const GO_DROPPED_RT: std::ops::RangeInclusive<i32> = 35..=64;

/// Signals for which the Go runtime prints the name from its table and
/// exits 2 (`_SigThrow` in `runtime/sigtab_linux_generic.go`), also when the
/// signal was ignored at start: Go keeps an inherited `SIG_IGN` only for
/// SIGHUP and SIGINT (`runtime/signal_unix.go` `sigInstallGoHandler`).
/// PORT: Go then prints the goroutines; the port prints only the name.
/// PORT: SIGABRT and SIGTRAP keep their default actions: Rust's abort (a
/// stack overflow too) raises SIGABRT, and debuggers use SIGTRAP.
#[cfg(target_os = "linux")]
const GO_THROWN: [(rustix::process::Signal, &str); 3] = {
    use rustix::process::Signal;
    [
        (Signal::QUIT, "SIGQUIT: quit"),
        (Signal::STKFLT, "SIGSTKFLT: stack fault"),
        (Signal::SYS, "SIGSYS: bad system call"),
    ]
};

/// Gives each signal that Go drops (`GO_DROPPED`, `GO_DROPPED_RT`) a handler
/// that does nothing. Not `SIG_IGN`: an exec resets a caught signal to its
/// default action, so a process that tsgo starts gets the default actions,
/// as from Go.
#[cfg(target_os = "linux")]
fn drop_go_signals() {
    let dropped = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let signals = GO_DROPPED.iter().map(|signal| signal.as_raw());
    for signal in signals.chain(GO_DROPPED_RT) {
        let _ = signal_hook::flag::register(signal, dropped.clone());
    }
}

/// The start of a process that runs the work, as the Go runtime and the Go
/// `syscall` package start: the signals that Go drops get a handler that
/// does nothing (`drop_go_signals`), a signal that Go throws (`GO_THROWN`)
/// ends the process (`throw`), the soft open-file limit goes up to one
/// below the hard limit (`gostd::rlimit::raise_open_file_limit`), and fd 1
/// is checked for `O_NONBLOCK`, as Go `os.NewFile` does at start
/// (`stdio::init`). The thread for the thrown signals waits on a pipe until
/// one comes. Go throws in the signal handler, with no thread. The port's
/// thread starts as a Go runtime thread does (`GoThread`): when the OS
/// refuses it, the run ends with Go's text and exit 2. Going on without it
/// would drop the thrown signals (dropping `signals` removes their actions,
/// not their handlers).
/// PORT: other systems than Linux keep the default actions (Go's tables
/// differ there).
fn go_runtime_start() {
    ts_goport::execute::tsc::stdio::init();
    ts_goport::gostd::rlimit::raise_open_file_limit();
    #[cfg(target_os = "linux")]
    {
        drop_go_signals();
        let thrown = GO_THROWN.iter().map(|(signal, _)| signal.as_raw());
        let Ok(mut signals) = signal_hook::iterator::Signals::new(thrown) else {
            return;
        };
        end_default_actions(&THROWN_DEFAULT);
        ts_goport::core::GoThread::new()
            .name("go-signals".to_string())
            .spawn(move || {
                for signal in signals.forever() {
                    if let Some((_, name)) = GO_THROWN.iter().find(|(s, _)| s.as_raw() == signal) {
                        throw(name);
                    }
                }
            });
    }
}

/// Ends the process after a signal that Go throws (`GO_THROWN`), as the Go
/// runtime does: it writes `name` to fd 2 with a raw write, sends the code
/// to the launcher in a worker (`send_code`) and exits 2 (`EXIT_GO_PANIC`,
/// the exit code of a Go fatal error). An error of the write (a closed or
/// broken stderr) is ignored, as in Go.
/// First it writes the stdout bytes that a report keeps on a regular file
/// (`stdio::flush_cli_stdout_at_exit`), so the file has the pieces written
/// so far, as Go's has (`os.Stdout` has no buffer). It skips them when
/// another thread holds their lock. It waits for no lock, so it cannot
/// wait for the work thread: that thread can hold the stdout or stderr
/// lock in a write that blocks on a full pipe. So it ends with `_exit`:
/// `std::process::exit` flushes the std stdout buffer when no other thread
/// holds its lock, and waits when another thread is in its cleanup.
#[cfg(target_os = "linux")]
fn throw(name: &str) -> ! {
    ts_goport::execute::tsc::stdio::flush_cli_stdout_at_exit();
    let line = format!("{name}\n");
    let _ = rustix::io::write(rustix::stdio::stderr(), line.as_bytes());
    if let Some(worker) = worker() {
        send_code(worker, EXIT_GO_PANIC);
    }
    signal_hook::low_level::exit(EXIT_GO_PANIC)
}

/// Ends the process with `code` once the work has written its output. A
/// worker (see `launch`) flushes stdout and sends the code (`send_code`).
fn exit(code: i32) -> ! {
    #[cfg(target_os = "linux")]
    if let Some(worker) = worker() {
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
        send_code(worker, code);
    }
    std::process::exit(code)
}

/// Sends `code` to the launcher of `worker` (see `launch`). First it points
/// stdout and stderr at /dev/null, so a reader of the launcher's output gets
/// its end of file when the launcher ends, while this process unmaps its
/// memory. It takes no std lock (`throw`).
#[cfg(target_os = "linux")]
fn send_code(worker: Worker, code: i32) {
    use rustix::fs::{FileType, Mode, OFlags, fstat, open};
    use std::os::fd::AsRawFd;
    if let Ok(null) = std::fs::File::options().write(true).open("/dev/null") {
        let _ = rustix::stdio::dup2_stdout(&null);
        let _ = rustix::stdio::dup2_stderr(&null);
    }
    // The launcher's end of the pipe, by its number, through /proc. Only
    // with this process's own /proc (`own_proc`): in another one,
    // /proc/<launcher> is another process or none. The code goes only to a
    // FIFO with the device and inode that the launcher passed. The first
    // open (`O_PATH`) only names the file and opens no FIFO or device, so
    // it cannot wait or change another file. The open for writing opens
    // the checked file again through /proc/self/fd (this process's own
    // files in any /proc that shows it), not the path, and does not wait
    // for a reader (`O_NONBLOCK`). Each new file has a close-on-exec flag.
    // Without its own /proc, or when an open fails, the launcher takes the
    // code from the worker's exit.
    if !own_proc() {
        return;
    }
    let path = format!("/proc/{}/fd/{}", worker.launcher.as_raw_pid(), worker.fd);
    let Ok(file) = open(path, OFlags::PATH | OFlags::CLOEXEC, Mode::empty()) else {
        return;
    };
    let checked = fstat(&file).is_ok_and(|stat| {
        FileType::from_raw_mode(stat.st_mode) == FileType::Fifo
            && stat.st_dev == worker.dev
            && stat.st_ino == worker.ino
    });
    let again = format!("/proc/self/fd/{}", file.as_raw_fd());
    let flags = OFlags::WRONLY | OFlags::NONBLOCK | OFlags::CLOEXEC;
    if checked && let Ok(pipe) = open(again, flags, Mode::empty()) {
        let _ = std::fs::File::from(pipe).write_all(&code.to_le_bytes());
    }
}

// Go: cmd/tsc/main.go:18 runMain
// PORT: the arguments are the port form of the Go `osutil.Args()` bytes (see
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
    #[cfg(target_os = "linux")]
    end_default_actions(&NOTIFY_DEFAULT);
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
/// The run prints a Go panic. A panic that a Go `recover()` catches
/// (`core::go_recover`: an API request answers it) prints nothing, as in Go.
fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
        if info.payload().is::<GoPanic>() {
            return;
        }
        let message = payload_message(info.payload());
        if message.starts_with(UNPORTED_PREFIX) || ts_goport::core::in_go_recover() {
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
        // The output so far comes first, also in one file with stderr.
        ts_goport::execute::tsc::stdio::flush_cli_stdout_at_exit();
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
