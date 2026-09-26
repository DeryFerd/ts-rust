//! `goport [tsc options]`: type checks a project with the Go port, like
//! `tsgo --noEmit`, and without `--pretty` like `tsgo --noEmit --pretty
//! false` (see `CheckBin`).
//!
//! Go: execute/tsc.go `CommandLine` and `tscCompilation`
//! (`execute::execute_tsc`): the Go command line parser, the Go
//! branches for errors, `--init`, `--version`, `--help`, `-p`, the config
//! search and `--showConfig`, then `performCompilation`, which reports
//! through execute/tsc/emit.go `EmitAndReportStatistics`. All output goes
//! to stdout, as in Go. The report is the shared `execute::tsc` one, as for
//! `goport_emit` and `goport_build`.
//!
//! goport never writes an output file: its compile step sets noEmit (see
//! `CheckBin`). `--init` writes a `tsconfig.json`, `--pprofDir` writes two
//! empty profile files (see `ts_goport::pprof`), and `--generateTrace` (or a
//! config `generateTrace`) writes the trace directory (see
//! `ts_goport::tracing`), as in Go.
//!
//! Each Go-ported stage runs under `catch_unwind`, so one unported path does
//! not hide the other diagnostics. Unported hits are printed to stderr as
//! `unported: <name> <count>` lines.
//!
//! Exit codes are the tsc ones (Go: execute/tsc/compile.go:30): 0, 1 when
//! there are diagnostics and the emit was skipped (also command line and
//! project errors), 2 when there are diagnostics and the emit was not
//! skipped (also config file read errors). Under noEmit, only a program
//! with no emittable file (no inputs, or only `.d.ts` files) has
//! diagnostics with exit 2. A run that hit unported code (or another
//! panic) exits `execute::tsc::EXIT_UNPORTED` (70), a code tsgo never
//! returns (Go uses 0 to 5). A Go panic that the port keeps
//! (`core::go_panic`) ends the run as in Go: the output so far, `panic:
//! <message>` on stderr and exit 2.
//!
//! `GOPORT_FRONTEND=legacy` has no effect here: the Go config parser and
//! program loader always run (`execute::execute_tsc`). No script uses
//! the legacy loader with this bin.

use std::any::Any;
use std::io::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Instant;

use ts_goport::emitter::program_emit::{EmitOptions, EmitResult, WriteFile, emit_with};
use ts_goport::execute::execute_tsc::{TscCompilationHooks, command_line};
use ts_goport::execute::tsc::{
    EXIT_UNPORTED, ExitStatus, ProgramLike, System, Writer, new_os_system, write_go_output,
};
use ts_goport::frontend::tsoptions::ParsedCommandLine;
use ts_goport::prelude::*;

const UNPORTED_PREFIX: &str = "unported Go code";

/// Stack size for the worker thread. The checker recurses deeply on large
/// projects.
const STACK_SIZE: usize = 1 << 30;

/// The opt-in `jemalloc` feature makes jemalloc the global allocator. See
/// `set_malloc_tunables` for why it is not the default.
#[cfg(feature = "jemalloc")]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

fn main() {
    set_malloc_tunables();
    // Go: `System.SinceStart` counts from the process start. The tunables
    // step above may exec the binary again, so the clock starts after it.
    let start = Instant::now();
    let args: Vec<String> = ts_goport::frontend::vfs::os_args();
    install_panic_hook();
    // The loading thread keeps the frontend program and the checker pool, so
    // the whole run stays on it. The checkers run on their own threads.
    let worker = std::thread::Builder::new()
        .name("goport".to_string())
        .stack_size(STACK_SIZE)
        .spawn(move || run(&args, start));
    let code = if let Ok(Ok(code)) = worker.map(std::thread::JoinHandle::join) {
        code
    } else {
        eprintln!("goport: worker thread failed");
        EXIT_UNPORTED
    };
    std::process::exit(code);
}

/// Sets the malloc tunables for this process.
///
/// glibc malloc (the default):
/// - `hugetlb=1` grows each heap in transparent huge page steps. By default
///   the heaps grow in small steps, so the kernel maps 4 KiB pages and the
///   first touch of each page faults (effect: 260k faults, 0.4 s system
///   time; with huge pages 8k faults, 0.08 s).
/// - `arena_max=6` caps the thread arenas. Every parse and bind thread would
///   otherwise keep its own partly used huge pages, which raises peak RSS
///   (query: 125 MB with no cap, 121 MB at 8, 117 MB at 6). At 5 or fewer
///   the threads wait on arena locks.
///
/// jemalloc (feature `jemalloc`): `narenas:4` has the same speed as the
/// default (4 arenas per CPU), with less RSS (query: 140 MB against 160 MB).
/// Against glibc with the tunables above, jemalloc is about 10% faster on
/// query, 5% on zod and effect and equal on hono, but query peak RSS is 15%
/// more (140 MB against 123 MB, tsgo 122 MB). Only `thp:never` brings jemalloc
/// under tsgo on query (119 MB), and that makes it slower than glibc on all
/// projects. So glibc stays the default.
///
/// The allocator reads these settings only at process start, so this runs
/// the same binary again once with them set. It does nothing when the caller
/// already set the variable, and the run continues without the settings when
/// the exec fails.
fn set_malloc_tunables() {
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    {
        use std::os::unix::process::CommandExt;
        #[cfg(not(feature = "jemalloc"))]
        const TUNABLES: (&str, &str) = (
            "GLIBC_TUNABLES",
            "glibc.malloc.hugetlb=1:glibc.malloc.arena_max=6",
        );
        #[cfg(feature = "jemalloc")]
        const TUNABLES: (&str, &str) = ("_RJEM_MALLOC_CONF", "narenas:4");
        let (name, value) = TUNABLES;
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

/// Keeps panics from unported code quiet (they are counted instead) and
/// prints all other panics to stderr. `run` prints a Go panic.
fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
        if info.payload().is::<GoPanic>() {
            return;
        }
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

/// Runs `f`, or returns the default value when it panics. A Go panic goes
/// on.
fn guard<T: Default>(f: impl FnOnce() -> T) -> T {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(value) => value,
        Err(payload) => {
            note_panic(resume_go_panic(payload).as_ref());
            T::default()
        }
    }
}

// Go: cmd/tsgo/main.go runMain: `execute.CommandLine` with the process
// system and arguments, then `os.Exit` with the status.
// PORT: the report goes to a buffer that is written to stdout at the end,
// also when a step panics. A panic ends the run; the steps inside
// `GuardedProgram` are guarded on their own. A Go panic (`go_panic`) ends
// the run with the Go runtime exit code.
fn run(args: &[String], start: Instant) -> i32 {
    let sys = match new_os_system() {
        Ok(sys) => sys,
        Err(status) => return status.code(),
    };
    let buffer: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
    let writer: Writer = buffer.clone();
    let sys: Rc<dyn System> = Rc::new(sys.with_start(start).with_writer(writer));

    let result = catch_unwind(AssertUnwindSafe(|| {
        command_line(sys.clone(), args, &CheckBin)
    }));

    let mut stdout = std::io::stdout().lock();
    let _ = write_go_output(&mut stdout, &buffer.borrow());
    let _ = stdout.flush();

    let code = match result {
        Ok(result) => result.status.code(),
        Err(payload) if print_go_panic(payload.as_ref()) => EXIT_GO_PANIC,
        Err(payload) => {
            note_panic(payload.as_ref());
            ExitStatus::Success.code()
        }
    };

    let unported = unported_report();
    let mut stderr = std::io::stderr().lock();
    for (name, count) in &unported {
        let _ = writeln!(stderr, "unported: {name} {count}");
    }

    if !unported.is_empty() {
        return EXIT_UNPORTED;
    }
    code
}

/// The goport part of the compile step (see `TscCompilationHooks`).
struct CheckBin;

impl TscCompilationHooks for CheckBin {
    // PORT: `-b` is unported here: goport never writes an output, and the
    // build workers re-run the bin. `goport_build` runs build mode.
    fn build_mode(&self) -> bool {
        false
    }

    // PORT: without `--pretty` on the command line, goport runs as with
    // `--pretty false`, the tsgo command line that the regression gate and
    // the measure scripts compare it with. The command line value also
    // overrides a config `pretty`, so the diagnostics are plain and there is
    // no error summary, on a TTY too. `--showConfig` keeps the unset value,
    // so it shows the options as Go does.
    fn command_line_parsed(&self, command_line: &mut ParsedCommandLine) {
        let options = command_line.compiler_options();
        if options.pretty.is_unknown() && !options.show_config.is_true() {
            let mut options = (**options).clone();
            options.pretty = Tristate::False;
            command_line.set_compiler_options(Rc::new(options));
        }
    }

    // PORT: goport runs on read-only project inputs and never writes an
    // output, so its compile step sets noEmit on the config, the options
    // the program gets with `--noEmit`. The init, version, help and
    // showConfig branches run before this, so `--showConfig` shows no
    // forced noEmit. Without `--noEmit`, tsgo emits the outputs and goport
    // does not (emit-modes check-without-noEmit-flag, a known divergence).
    fn prepare_compilation(
        &self,
        _sys: &dyn System,
        _command_line_options: &CompilerOptions,
        _config_file_name: &str,
        config: &mut ParsedCommandLine,
    ) -> Result<(), ExitStatus> {
        let mut options = (**config.compiler_options()).clone();
        options.no_emit = Tristate::True;
        config.set_compiler_options(Rc::new(options));
        Ok(())
    }

    fn program_like(&self) -> Option<&dyn ProgramLike> {
        Some(&GuardedProgram)
    }

    // PORT: tsc passes no `WriteFile`. Under noEmit nothing is written.
    fn write_file(&self) -> Option<WriteFile> {
        None
    }
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
        // PORT: the build info is not written, so this adds no diagnostics
        // (see `perform_incremental_compilation` in
        // `execute::execute_tsc`).
        if options().is_incremental() {
            return EmitResult {
                emit_skipped: true,
                ..EmitResult::default()
            };
        }
        // PORT: tsc passes no `WriteFile` (`CheckBin::write_file`). Under
        // noEmit nothing is written.
        guard(|| emit_with(emit_options, |emit_file| guard(emit_file)))
    }
}

/// Semantic diagnostics for one file. A panic drops that file's results and
/// replaces the checker, whose caches may be half written. A Go panic goes
/// on.
fn check_file_guarded(checker: &mut Checker, file: Node) -> Vec<Diagnostic> {
    match catch_unwind(AssertUnwindSafe(|| {
        get_semantic_diagnostics_with_checker(checker, file)
    })) {
        Ok(diagnostics) => diagnostics,
        Err(payload) => {
            note_panic(resume_go_panic(payload).as_ref());
            let index = (checker.id - 1) as usize;
            *checker = Checker::new(index);
            Vec::new()
        }
    }
}
