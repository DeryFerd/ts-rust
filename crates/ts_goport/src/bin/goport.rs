//! `goport -p <tsconfig>`: type checks a project with the Go port and prints
//! the diagnostics like `tsgo --noEmit --pretty false`.
//!
//! Go: execute/tsc/emit.go `EmitFilesAndReportErrors` (the non-pretty path).
//!
//! Each Go-ported stage runs under `catch_unwind`, so one unported path does
//! not hide the other diagnostics. Unported hits are printed to stderr as
//! `unported: <name> <count>` lines.
//!
//! Exit codes: 2 when any unported code (or other panic) was hit, else 1 when
//! there are diagnostics, else 0.

use std::any::Any;
use std::io::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};

use ts_goport::prelude::*;

const UNPORTED_PREFIX: &str = "unported Go code";

/// Stack size for the worker thread. The checker recurses deeply on large
/// projects.
const STACK_SIZE: usize = 1 << 30;

fn main() {
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
        .spawn(move || run(&config));
    let code = if let Ok(Ok(code)) = worker.map(std::thread::JoinHandle::join) {
        code
    } else {
        eprintln!("goport: worker thread failed");
        2
    };
    std::process::exit(code);
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

// Go: execute/tsc/emit.go:72 EmitFilesAndReportErrors
// PORT: noEmit is forced, so the emit step writes no files. It still runs,
// because Go reports the declaration transformer diagnostics during emit
// (see `collect_all_diagnostics`). The error summary is only written in
// pretty mode, so it is not written.
fn run(config: &str) -> i32 {
    let loaded = catch_unwind(AssertUnwindSafe(|| {
        try_load_with(config, |options| options.no_emit = Tristate::True)
    }));
    let diagnostics = match loaded {
        Ok(Ok(_)) => guard(collect_all_diagnostics),
        Ok(Err(message)) => {
            eprintln!("goport: {message}");
            return 1;
        }
        Err(payload) => {
            note_panic(payload.as_ref());
            Vec::new()
        }
    };

    let mut output = String::new();
    write_format_diagnostics(&mut output, &diagnostics);
    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(output.as_bytes());
    let _ = stdout.flush();

    let unported = unported_report();
    let mut stderr = std::io::stderr().lock();
    for (name, count) in &unported {
        let _ = writeln!(stderr, "unported: {name} {count}");
    }

    if unported.is_empty() {
        i32::from(!diagnostics.is_empty())
    } else {
        2
    }
}

/// The tsc diagnostics pipeline, with each checker call guarded per file.
fn collect_all_diagnostics() -> Vec<Diagnostic> {
    let all_diagnostics = get_diagnostics_of_any_program(
        Node::NIL,
        false,
        &mut |file| guard(|| get_bind_diagnostics(file)),
        &mut |file| collect_checker_diagnostics_with(file, check_file_guarded),
        &mut || guard(get_global_diagnostics),
        &mut |file| guard(|| get_declaration_diagnostics(file)),
    );

    let mut all_diagnostics = all_diagnostics;
    let options = options();
    if !options.list_files_only.is_true() {
        all_diagnostics.extend(guard(emit_diagnostics).diagnostics);
    }

    sort_and_deduplicate_diagnostics(all_diagnostics)
}

/// The diagnostics of the emit step (Go: execute/tsc/emit.go:103
/// `ProgramLike.Emit`). Under noEmit, Go `emitDeclarationFile` still runs the
/// declaration transformer and reports its diagnostics before it checks
/// `NoEmit` (compiler/emitter.go:226). Each file is guarded on its own.
fn emit_diagnostics() -> EmitResult {
    // Go: execute/tsc.go:244 an incremental program is an
    // `incremental.Program`. Its Emit under noEmit
    // (execute/incremental/program.go:205) skips the file emit and only
    // writes the build info.
    // PORT: the build info is not written, so this adds no diagnostics.
    if options().is_incremental() {
        return EmitResult {
            emit_skipped: true,
            diagnostics: Vec::new(),
        };
    }
    emit(Node::NIL, &mut |file| guard(|| emit_source_file(file)))
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
