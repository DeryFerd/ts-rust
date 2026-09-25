//! `goport -p <tsconfig>`: type checks a project with the Go port and prints
//! the diagnostics like `tsgo --noEmit --pretty false`.
//!
//! Go: execute/tsc.go `performCompilation`, which reports through
//! execute/tsc/emit.go `EmitAndReportStatistics` (the non-pretty path). The
//! report is the shared `execute::tsc` one, as for `goport_emit` and
//! `goport_build`.
//!
//! Each Go-ported stage runs under `catch_unwind`, so one unported path does
//! not hide the other diagnostics. Unported hits are printed to stderr as
//! `unported: <name> <count>` lines.
//!
//! Exit codes are the tsc ones (Go: execute/tsc/emit.go:65): 0, 1 when there
//! are diagnostics and the emit was skipped, 2 when there are diagnostics and
//! the emit was not skipped. Under noEmit, only a program with no emittable
//! file (no inputs, or only `.d.ts` files) has diagnostics with exit 2.
//! A run that hit unported code (or another panic) exits
//! `execute::tsc::EXIT_UNPORTED` (70), a code tsgo never returns (Go uses
//! 0 to 5).

use std::any::Any;
use std::io::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

use ts_goport::emitter::program_emit::{EmitOptions, EmitResult, emit_with};
use ts_goport::execute::tsc::{
    CompileTimes, EXIT_UNPORTED, EmitInput, ExitStatus, ProgramLike, Writer,
    create_diagnostic_reporter, create_report_error_summary, emit_and_report_statistics,
    new_os_system,
};
use ts_goport::prelude::*;

const UNPORTED_PREFIX: &str = "unported Go code";

/// Stack size for the worker thread. The checker recurses deeply on large
/// projects.
const STACK_SIZE: usize = 1 << 30;

fn main() {
    set_malloc_tunables();
    // Go: `System.SinceStart` counts from the process start. The tunables
    // step above may exec the binary again, so the clock starts after it.
    let start = Instant::now();
    let config = match parse_args(std::env::args().skip(1).collect()) {
        Ok(config) => config,
        Err(message) => {
            eprintln!("goport: {message}");
            eprintln!("usage: goport -p <tsconfig.json | project dir>");
            std::process::exit(1);
        }
    };
    install_panic_hook();
    // The loading thread keeps the frontend program and the checker pool, so
    // the whole run stays on it. The checkers run on their own threads.
    let worker = std::thread::Builder::new()
        .name("goport".to_string())
        .stack_size(STACK_SIZE)
        .spawn(move || run(&config, start));
    let code = if let Ok(Ok(code)) = worker.map(std::thread::JoinHandle::join) {
        code
    } else {
        eprintln!("goport: worker thread failed");
        EXIT_UNPORTED
    };
    std::process::exit(code);
}

/// Sets glibc malloc tunables for this process.
///
/// - `hugetlb=1` grows each heap in transparent huge page steps. By default
///   the heaps grow in small steps, so the kernel maps 4 KiB pages and the
///   first touch of each page faults (effect: 260k faults, 0.4 s system
///   time; with huge pages 8k faults, 0.08 s).
/// - `arena_max=6` caps the thread arenas. Every parse and bind thread would
///   otherwise keep its own partly used huge pages, which raises peak RSS
///   (query: 125 MB with no cap, 121 MB at 8, 117 MB at 6). At 5 or fewer
///   the threads wait on arena locks.
///
/// glibc reads `GLIBC_TUNABLES` only at process start, so this runs the same
/// binary again once with the tunables set. It does nothing when the caller
/// already set `GLIBC_TUNABLES`, and the run continues without the tunables
/// when the exec fails.
fn set_malloc_tunables() {
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    {
        use std::os::unix::process::CommandExt;
        const MALLOC_TUNABLES: &str = "glibc.malloc.hugetlb=1:glibc.malloc.arena_max=6";
        if std::env::var_os("GLIBC_TUNABLES").is_some() {
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
        let _ = command
            .args(args)
            .env("GLIBC_TUNABLES", MALLOC_TUNABLES)
            .exec();
    }
}

/// Reads `-p <path>`, `--project <path>` and their `=` forms. Without one,
/// the project is the current directory (like tsc).
fn parse_args(args: Vec<String>) -> Result<String, String> {
    let mut project = None;
    let mut iter = args.into_iter();
    while let Some(arg) = iter.next() {
        if arg == "-p" || arg == "--project" {
            project = Some(iter.next().ok_or_else(|| format!("{arg} needs a path"))?);
        } else if let Some(value) = arg
            .strip_prefix("-p=")
            .or_else(|| arg.strip_prefix("--project="))
        {
            project = Some(value.to_string());
        } else if arg == "--noEmit"
            || arg == "--pretty"
            || arg == "false"
            || arg == "--pretty=false"
        {
            // Accepted for tsgo command-line parity; this is always the mode.
        } else {
            return Err(format!("unknown argument {arg}"));
        }
    }
    Ok(project.unwrap_or_else(|| ".".to_string()))
}

/// Keeps panics from unported code quiet (they are counted instead) and
/// prints all other panics to stderr.
fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
        let message = payload_message(info.payload());
        if message.starts_with(UNPORTED_PREFIX) {
            // GOPORT_TRACE=1 prints where each unported hit came from.
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
        eprintln!("goport: panic{location}: {message}");
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

/// Runs `f`, or returns the default value when it panics.
fn guard<T: Default>(f: impl FnOnce() -> T) -> T {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(value) => value,
        Err(payload) => {
            note_panic(payload.as_ref());
            T::default()
        }
    }
}

// Go: execute/tsc.go:289 performCompilation (the non-incremental path) and
// execute/tsc.go:244 (the incremental one), with the command line
// `--noEmit --pretty false`.
// PORT: noEmit is forced, so the emit step writes no files. It still runs,
// because Go reports the declaration transformer diagnostics during emit
// (see `GuardedProgram::emit`). The report goes to a buffer that is
// written to stdout at the end, also when a step panics.
fn run(config: &str, start: Instant) -> i32 {
    let sys = match new_os_system() {
        Ok(sys) => sys,
        Err(status) => return status.code(),
    };
    let buffer: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
    let writer: Writer = buffer.clone();
    let sys = sys.with_start(start).with_writer(writer.clone());

    let mut compile_times = CompileTimes::default();
    let loaded = catch_unwind(AssertUnwindSafe(|| {
        try_load_timed(
            config,
            |options| {
                options.no_emit = Tristate::True;
                options.pretty = Tristate::False;
            },
            &mut compile_times,
        )
    }));
    let mut status = ExitStatus::Success;
    match loaded {
        Ok(Ok(_)) => {
            // Go: execute/tsc.go:294 and :308 time the build info read and
            // the incremental program. PORT: goport reads no build info and
            // makes no incremental program, so both steps are empty. They
            // are still timed, so the table has the same rows as Go.
            if options().is_incremental() {
                let build_info_read_start = Instant::now();
                compile_times.build_info_read_time = build_info_read_start.elapsed();
                let changes_compute_start = Instant::now();
                compile_times.changes_compute_time = changes_compute_start.elapsed();
            }
            let reported = catch_unwind(AssertUnwindSafe(|| {
                let options = options();
                emit_and_report_statistics(&EmitInput {
                    sys: &sys,
                    program_like: &GuardedProgram,
                    config: None,
                    report_diagnostic: create_diagnostic_reporter(&sys, writer.clone(), options),
                    report_error_summary: create_report_error_summary(&sys, Some(options)),
                    writer: writer.clone(),
                    write_file: None,
                    compile_times: Rc::new(RefCell::new(compile_times)),
                })
            }));
            match reported {
                Ok((result, _statistics)) => status = result.status,
                Err(payload) => note_panic(payload.as_ref()),
            }
        }
        Ok(Err(message)) => {
            eprintln!("goport: {message}");
            return 1;
        }
        Err(payload) => note_panic(payload.as_ref()),
    }

    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(&buffer.borrow());
    let _ = stdout.flush();

    let unported = unported_report();
    let mut stderr = std::io::stderr().lock();
    for (name, count) in &unported {
        let _ = writeln!(stderr, "unported: {name} {count}");
    }

    if !unported.is_empty() {
        return EXIT_UNPORTED;
    }
    status.code()
}

/// The installed program as a Go `ProgramLike`, with each step guarded on
/// its own so one unported path does not hide the other diagnostics.
struct GuardedProgram;

impl ProgramLike for GuardedProgram {
    fn options(&self) -> &'static CompilerOptions {
        options()
    }
    fn get_bind_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        guard(|| get_bind_diagnostics(file))
    }
    fn get_global_diagnostics(&self) -> Vec<Diagnostic> {
        guard(get_global_diagnostics)
    }
    fn get_semantic_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        collect_checker_diagnostics_with(file, check_file_guarded)
    }
    fn get_declaration_diagnostics(&self, file: Node) -> Vec<Diagnostic> {
        guard(|| get_declaration_diagnostics(file))
    }
    /// Under noEmit, Go `emitDeclarationFile` still runs the declaration
    /// transformer and reports its diagnostics before it checks `NoEmit`
    /// (compiler/emitter.go:226). Each file is guarded on its own.
    fn emit(&self, emit_options: EmitOptions) -> EmitResult {
        // Go: execute/tsc.go:244 an incremental program is an
        // `incremental.Program`. Its Emit under noEmit
        // (execute/incremental/program.go:205) skips the file emit and only
        // writes the build info.
        // PORT: the build info is not written, so this adds no diagnostics.
        if options().is_incremental() {
            return EmitResult {
                emit_skipped: true,
                ..EmitResult::default()
            };
        }
        // PORT: tsc passes no `WriteFile`. Under noEmit nothing is written.
        guard(|| emit_with(emit_options, |emit_file| guard(emit_file)))
    }
}

/// Semantic diagnostics for one file. A panic drops that file's results and
/// replaces the checker, whose caches may be half written.
fn check_file_guarded(checker: &mut Checker, file: Node) -> Vec<Diagnostic> {
    match catch_unwind(AssertUnwindSafe(|| {
        get_semantic_diagnostics_with_checker(checker, file)
    })) {
        Ok(diagnostics) => diagnostics,
        Err(payload) => {
            note_panic(payload.as_ref());
            let index = (checker.id - 1) as usize;
            *checker = Checker::new(index);
            Vec::new()
        }
    }
}
