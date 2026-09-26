//! `goport_build`: `tsc -b` with the Go port.
//!
//! - `goport_build -b [projects...] [options]` (also `--b`, `-build`,
//!   `--build`): Go `execute.CommandLine` with a build flag, which is
//!   `tscBuildCompilation` (execute/tsc.go:90). The exit code is the Go
//!   exit status.
//! - `goport_build --build-worker <config> [the -b command line...]`: the
//!   build worker (plan D1). It compiles and emits one project the way the
//!   Go build task does and prints one JSON result line (see
//!   `execute::build::worker`). The orchestrator starts these itself.
//!   Without a `-b` command line it runs with the default build options.
//!
//! Only build mode is ported. Other command lines (Go `tscCompilation`)
//! exit with `EXIT_UNPORTED` (70).
//!
//! Unported Go code that a run reaches is listed on stderr as
//! `unported: <name> <count>`. Such a run, a panic and a failed build
//! worker exit with `EXIT_UNPORTED` (70), a code tsgo never returns (Go
//! uses 0 to 5), like `goport` and `goport_emit`.

use std::any::Any;
use std::io::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};

use ts_goport::execute::build::orchestrator::tsc_build_compilation;
use ts_goport::execute::build::worker::{
    BUILD_WORKER_FLAG, compile_and_emit_worker, marshal_worker_compile_result,
};
use ts_goport::execute::tsc::compile::{EXIT_UNPORTED, ExitStatus, System, new_os_system};
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
    let args: Vec<String> = std::env::args().skip(1).collect();
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

fn run(args: &[String]) -> i32 {
    let sys = match new_os_system() {
        Ok(sys) => sys,
        Err(status) => return status.code(),
    };
    let sys: Rc<dyn System> = Rc::new(sys);

    if args.first().map(String::as_str) == Some(BUILD_WORKER_FLAG) {
        return run_worker(&sys, &args[1..]);
    }

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
        tsc_build_compilation(sys.clone(), args)
    }));
    let _ = sys.writer().borrow_mut().flush();
    let status = match result {
        Ok(result) => result.status,
        Err(payload) => {
            note_panic(payload.as_ref());
            ExitStatus::NotImplemented
        }
    };
    finish(status)
}

/// `--build-worker <config> [command line...]`
fn run_worker(sys: &Rc<dyn System>, args: &[String]) -> i32 {
    let Some(config) = args.first() else {
        eprintln!("usage: goport_build {BUILD_WORKER_FLAG} <config> [-b command line...]");
        return EXIT_UNPORTED;
    };
    let build_command_line = &args[1..];
    let result = catch_unwind(AssertUnwindSafe(|| {
        compile_and_emit_worker(sys.clone(), config, build_command_line)
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
        Err(payload) => {
            // No result line: the orchestrator reports the failed worker.
            note_panic(payload.as_ref());
            report_unported();
            EXIT_UNPORTED
        }
    }
}

/// Prints the unported counts and returns the exit code for `status`, or
/// `EXIT_UNPORTED` when the run reached unported code.
fn finish(status: ExitStatus) -> i32 {
    if report_unported() {
        return EXIT_UNPORTED;
    }
    status.code()
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

fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
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
