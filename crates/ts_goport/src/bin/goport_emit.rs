//! `goport_emit -p <tsconfig> --outDir <dir>`: compiles a project with the Go
//! port and writes the `.js`, `.d.ts` and `.map` outputs like `tsgo`.
//!
//! Go: execute/tsc/emit.go `EmitFilesAndReportErrors` (the non-pretty path).
//!
//! Output paths are the Go paths. A config `declarationDir`, or a `.js`
//! file of a source outside the common source directory, can put an output
//! outside `--outDir`.
//!
//! Safety: every write must be under the write root, and no write may
//! replace a program source file. By default the write root is `--outDir`,
//! and the run stops before it writes anything when `--outDir` is inside the
//! project directory or a source directory. A write outside the root is
//! refused and reported as TS5033, so the project inputs are never written.
//!
//! Options:
//! - `--outDir <dir>` (required) replaces the config `outDir`.
//! - `--writeRoot <dir>` sets the write root. Use it when Go writes outside
//!   `--outDir` (for example a config `declarationDir`) and every such path
//!   is in a scratch copy under `<dir>`. The `--outDir` location checks are
//!   then skipped.
//! - `--declarationDir <dir>` replaces the config `declarationDir`, as in tsgo.
//!
//! - `--declaration`, `--declarationMap`, `--emitDeclarationOnly`,
//!   `--sourceMap`, `--inlineSourceMap`, `--inlineSources`,
//!   `--removeComments` and `--noEmit` set those options, as in tsgo. Each
//!   takes an optional `true` or `false` (`--noEmit false`).
//!
//! `.tsbuildinfo` is not written.
//!
//! Exit codes are the tsc ones: 0, 1 when there are diagnostics and the
//! emit was skipped, 2 when there are diagnostics and outputs were written.
//! A run that hit unported code (or another panic) exits `EXIT_UNPORTED`
//! (70), a code tsgo never returns (Go uses 0 to 5), and says so on stderr.

use std::any::Any;
use std::collections::HashSet;
use std::io::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::{Arc, Mutex};

use ts_goport::emitter::emitter::EmitOnly;
use ts_goport::emitter::program_emit::{EmitOptions, EmitResult, WriteFile, WriteFileData, emit};
use ts_goport::prelude::*;

const UNPORTED_PREFIX: &str = "unported Go code";

/// Exit code when unported code or another panic was hit. It is outside the
/// Go `ExitStatus` range (execute/tsc/compile.go:32, 0 to 5), so it never
/// looks like a tsgo status. 70 is `EX_SOFTWARE` (internal software error).
const EXIT_UNPORTED: i32 = 70;

/// Stack size for the worker thread. The checker recurses deeply on large
/// projects.
const STACK_SIZE: usize = 1 << 30;

struct Config {
    project: String,
    out_dir: String,
    /// `--writeRoot`, or `None` for the default root `out_dir`.
    write_root: Option<String>,
    declaration_dir: Option<String>,
    /// Boolean compiler options set on the command line, like tsgo `--flag`
    /// or `--flag false`.
    flags: Vec<(String, bool)>,
}

/// The boolean compiler options the command line can set (tsgo names).
const BOOLEAN_FLAGS: &[&str] = &[
    "--declaration",
    "--declarationMap",
    "--emitDeclarationOnly",
    "--sourceMap",
    "--inlineSourceMap",
    "--inlineSources",
    "--removeComments",
    "--noEmit",
];

/// Sets one of `BOOLEAN_FLAGS` on `options`.
fn apply_flag(options: &mut CompilerOptions, flag: &str, value: bool) {
    let value = if value {
        Tristate::True
    } else {
        Tristate::False
    };
    match flag {
        "--declaration" => options.declaration = value,
        "--declarationMap" => options.declaration_map = value,
        "--emitDeclarationOnly" => options.emit_declaration_only = value,
        "--sourceMap" => options.source_map = value,
        "--inlineSourceMap" => options.inline_source_map = value,
        "--inlineSources" => options.inline_sources = value,
        "--removeComments" => options.remove_comments = value,
        "--noEmit" => options.no_emit = value,
        _ => {}
    }
}

fn main() {
    let config = match parse_args(std::env::args().skip(1).collect()) {
        Ok(config) => config,
        Err(message) => {
            eprintln!("goport_emit: {message}");
            eprintln!(
                "usage: goport_emit -p <tsconfig.json | project dir> --outDir <dir> [--writeRoot <dir>] [--declarationDir <dir>] [--declaration ...]"
            );
            std::process::exit(1);
        }
    };
    install_panic_hook();
    let worker = std::thread::Builder::new()
        .name("goport_emit".to_string())
        .stack_size(STACK_SIZE)
        .spawn(move || run(&config));
    let code = if let Ok(Ok(code)) = worker.map(std::thread::JoinHandle::join) {
        code
    } else {
        eprintln!("goport_emit: worker thread failed");
        EXIT_UNPORTED
    };
    std::process::exit(code);
}

fn parse_args(args: Vec<String>) -> Result<Config, String> {
    let mut project = None;
    let mut out_dir = None;
    let mut write_root = None;
    let mut declaration_dir = None;
    let mut flags = Vec::new();
    let mut iter = args.into_iter().peekable();
    while let Some(arg) = iter.next() {
        let (name, inline) = match arg.split_once('=') {
            Some((name, value)) if name.starts_with('-') => {
                (name.to_string(), Some(value.to_string()))
            }
            _ => (arg.clone(), None),
        };
        let mut value = |name: &str| -> Result<String, String> {
            match inline.clone() {
                Some(value) => Ok(value),
                None => iter.next().ok_or_else(|| format!("{name} needs a value")),
            }
        };
        match name.as_str() {
            "-p" | "--project" => project = Some(value(&name)?),
            "--outDir" => out_dir = Some(value(&name)?),
            "--writeRoot" => write_root = Some(value(&name)?),
            "--declarationDir" => declaration_dir = Some(value(&name)?),
            "--pretty" => {
                if inline.is_none() {
                    // `--pretty false` for tsgo command-line parity.
                    let _ = value(&name)?;
                }
            }
            flag if BOOLEAN_FLAGS.contains(&flag) => {
                // tsgo reads an optional `true` or `false` after a boolean flag.
                let value = match inline.as_deref() {
                    Some(value) => value != "false",
                    None => match iter.peek().map(String::as_str) {
                        Some("true" | "false") => iter.next().is_some_and(|v| v == "true"),
                        _ => true,
                    },
                };
                flags.push((name.clone(), value));
            }
            _ => return Err(format!("unknown argument {arg}")),
        }
    }
    let out_dir = out_dir.ok_or_else(|| "--outDir is required".to_string())?;
    Ok(Config {
        project: project.unwrap_or_else(|| ".".to_string()),
        out_dir: absolute(&out_dir),
        write_root: write_root.map(|d| absolute(&d)),
        declaration_dir: declaration_dir.map(|d| absolute(&d)),
        flags,
    })
}

/// `path` made absolute against the current directory and normalized.
fn absolute(path: &str) -> String {
    let cwd = std::env::current_dir()
        .map(|d| d.to_string_lossy().replace('\\', "/"))
        .unwrap_or_default();
    ts_path::normalize_path(&ts_path::resolve_path(&cwd, &[path]))
}

/// Whether `path` is `dir` or inside it (both absolute and normalized).
fn is_inside(path: &str, dir: &str) -> bool {
    let dir = dir.trim_end_matches('/');
    path == dir || path.starts_with(&format!("{dir}/"))
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
        eprintln!("goport_emit: panic{location}: {message}");
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

fn guard<T: Default>(f: impl FnOnce() -> T) -> T {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(value) => value,
        Err(payload) => {
            note_panic(payload.as_ref());
            T::default()
        }
    }
}

/// The config directory of `project` (a tsconfig path or a directory).
fn config_directory(project: &str) -> String {
    let path = absolute(project);
    if std::path::Path::new(&path).is_dir() {
        path
    } else {
        ts_path::directory_path(&path).clone()
    }
}

// Go: execute/tsc/emit.go:72 EmitFilesAndReportErrors
fn run(config: &Config) -> i32 {
    let config_dir = config_directory(&config.project);
    if config.write_root.is_none() && is_inside(&config.out_dir, &config_dir) {
        eprintln!(
            "goport_emit: refusing --outDir {} inside the project directory {config_dir}",
            config.out_dir
        );
        return 1;
    }
    let loaded = catch_unwind(AssertUnwindSafe(|| {
        // `options` are the command line options, applied over the config.
        try_load_with(&config.project, |options| {
            if let Some(dir) = &config.declaration_dir {
                options.declaration_dir.clone_from(dir);
            }
            options.out_dir.clone_from(&config.out_dir);
            for (flag, value) in &config.flags {
                apply_flag(options, flag, *value);
            }
        })
    }));
    match loaded {
        Ok(Ok(_)) => {}
        Ok(Err(message)) => {
            eprintln!("goport_emit: {message}");
            return 1;
        }
        Err(payload) => {
            note_panic(payload.as_ref());
            return report(&[], true);
        }
    }

    // Refuse before any write when the out dir is inside a source directory.
    let inputs: HashSet<String> = source_files()
        .into_iter()
        .map(|file| ts_path::normalize_path(source_file_file_name(file)))
        .collect();
    for file in source_files() {
        let dir = ts_path::directory_path(source_file_file_name(file)).clone();
        if config.write_root.is_none()
            && !source_file_info(file).is_declaration_file
            && is_inside(&config.out_dir, &dir)
        {
            eprintln!(
                "goport_emit: refusing --outDir {} inside the source directory {dir}",
                config.out_dir
            );
            return 1;
        }
    }

    let mut all_diagnostics = guard(collect_all_diagnostics);

    let refused: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let write_root = config.write_root.as_ref().unwrap_or(&config.out_dir);
    let write_file = new_write_file(write_root.clone(), inputs, refused.clone());
    // Go: execute/tsc/emit.go:103 listFilesOnly skips the emit.
    let mut emit_result = EmitResult {
        emit_skipped: true,
        ..EmitResult::default()
    };
    if !options().list_files_only.is_true() {
        emit_result = guard(|| {
            emit(EmitOptions {
                target_source_file: Node::NIL,
                emit_only: EmitOnly::All,
                write_file: Some(write_file),
            })
        });
    }
    let emit_skipped = emit_result.emit_skipped;
    all_diagnostics.extend(emit_result.diagnostics);
    let all_diagnostics = sort_and_deduplicate_diagnostics(all_diagnostics);

    let refused = refused.lock().map(|r| r.clone()).unwrap_or_default();
    for path in &refused {
        eprintln!("goport_emit: refused to write {path} (outside {write_root} or an input file)");
    }
    // A refused write is also a TS5033 diagnostic, so the status is the tsc one.
    report(&all_diagnostics, emit_skipped)
}

/// The Go `WriteFile` callback: writes only under `root`, and never over a
/// program source file (`inputs`).
fn new_write_file(
    root: String,
    inputs: HashSet<String>,
    refused: Arc<Mutex<Vec<String>>>,
) -> WriteFile {
    Arc::new(
        move |file_name: &str, text: &str, _data: &mut WriteFileData| -> Result<(), String> {
            let path = ts_path::normalize_path(file_name);
            if !is_inside(&path, &root)
                || path == root.trim_end_matches('/')
                || inputs.contains(&path)
            {
                if let Ok(mut refused) = refused.lock() {
                    refused.push(path.clone());
                }
                return Err(format!("{path} is outside the output directory"));
            }
            let target = std::path::Path::new(&path);
            if let Some(parent) = target.parent() {
                std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
            }
            std::fs::write(target, text).map_err(|e| e.to_string())
        },
    )
}

/// Prints the diagnostics and unported counts and returns the exit code:
/// the Go tsc status (0, 1 when outputs were skipped, 2 when generated with
/// diagnostics), or `EXIT_UNPORTED` when something was unported.
// Go: execute/tsc/emit.go:65 (the exit status)
fn report(diagnostics: &[Diagnostic], emit_skipped: bool) -> i32 {
    let mut output = String::new();
    write_format_diagnostics(&mut output, diagnostics);
    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(output.as_bytes());
    let _ = stdout.flush();

    let unported = unported_report();
    let mut stderr = std::io::stderr().lock();
    for (name, count) in &unported {
        let _ = writeln!(stderr, "unported: {name} {count}");
    }

    if !unported.is_empty() {
        EXIT_UNPORTED
    } else if diagnostics.is_empty() {
        0
    } else if emit_skipped {
        1
    } else {
        2
    }
}

/// The tsc diagnostics pipeline, with each checker call guarded per file.
fn collect_all_diagnostics() -> Vec<Diagnostic> {
    get_diagnostics_of_any_program(
        Node::NIL,
        false,
        &mut |file| guard(|| get_bind_diagnostics(file)),
        &mut |file| collect_checker_diagnostics_with(file, check_file_guarded),
        &mut || guard(get_global_diagnostics),
        &mut |file| guard(|| get_declaration_diagnostics(file)),
    )
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
