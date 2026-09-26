//! `goport_typesyms -p <tsconfig> -o <outdir>`: writes the harness `.types`
//! and `.symbols` baselines for a project with the Go port, in the format of
//! the Go tool `tools/tsgo-src/cmd/typesymdump`.
//!
//! Flow (same as the Go dumper):
//! 1. Load the tsconfig as is (no `noEmit` override).
//! 2. Run the `tsgo --noEmit` diagnostics pass. Type ids and union order
//!    depend on the check order, so the walk must follow the same pass.
//! 3. Walk types for every non-default-lib file, then symbols for every file.
//!    Output names are the path relative to the tsconfig directory with `/`
//!    replaced by `!`. The header is that relative path.
//! 4. Write `files.txt`: unit names in walk order, then
//!    `hadErrorBaseline <bool>`.
//!
//! Each node's checker work runs under `catch_unwind`. A panicking node gets
//! `<<goport panic: MESSAGE>>` as its type or symbol text; the checker is
//! kept so later type ids do not shift. stderr gets `unported: <name>
//! <count>` lines and the frontend setting. Exit 2 when anything panicked.

use std::any::Any;
use std::io::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};

use ts_goport::baseline::type_symbol::{TestFile, generate_baseline, new_type_writer_walker};
use ts_goport::frontend::vfs::raw_file_bytes;
use ts_goport::prelude::*;

const UNPORTED_PREFIX: &str = "unported Go code";

/// Stack size for the worker thread. The checker recurses deeply.
const STACK_SIZE: usize = 1 << 30;

/// The opt-in `jemalloc` feature makes jemalloc the global allocator
/// (see `goport.rs` `set_malloc_tunables`).
#[cfg(feature = "jemalloc")]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mut project, mut out_dir) = (None, None);
    let mut iter = args.into_iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "-p" => project = iter.next(),
            "-o" => out_dir = iter.next(),
            _ => {
                eprintln!("goport_typesyms: unknown argument {arg}");
                std::process::exit(1);
            }
        }
    }
    let (Some(project), Some(out_dir)) = (project, out_dir) else {
        eprintln!("usage: goport_typesyms -p <tsconfig> -o <outdir>");
        std::process::exit(1);
    };
    install_panic_hook();
    // The loading thread keeps the frontend program and the checker pool, so
    // the whole run stays on it. The checkers run on their own threads.
    let worker = std::thread::Builder::new()
        .name("goport_typesyms".to_string())
        .stack_size(STACK_SIZE)
        .spawn(move || run(&project, &out_dir));
    let code = if let Ok(Ok(code)) = worker.map(std::thread::JoinHandle::join) {
        code
    } else {
        eprintln!("goport_typesyms: worker thread failed");
        2
    };
    std::process::exit(code);
}

/// Keeps unported panics quiet (they are counted) and prints other panics.
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
        eprintln!("goport_typesyms: panic{location}: {message}");
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

/// Go `compiler.GetDiagnosticsOfAnyProgram(ctx, program, nil, false,
/// program.GetBindDiagnostics, program.GetSemanticDiagnostics)`, with the
/// same per-file guards as `goport`. A file whose check panics gets a new
/// checker, as in `goport`, so the walk sees the `goport` checker state.
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

/// Go `filepath.Clean` of an absolute `/` path: drops `.` and resolves `..`
/// lexically.
fn clean_components(path: &str) -> Vec<&str> {
    let mut parts: Vec<&str> = Vec::new();
    for part in path.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            _ => parts.push(part),
        }
    }
    parts
}

/// Go `filepath.Rel(base, target)` for two absolute paths.
fn relative_path(base: &str, target: &str) -> String {
    let base = clean_components(base);
    let target = clean_components(target);
    let common = base.iter().zip(&target).take_while(|(a, b)| a == b).count();
    let mut parts: Vec<&str> = vec![".."; base.len() - common];
    parts.extend_from_slice(&target[common..]);
    if parts.is_empty() {
        return ".".to_string();
    }
    parts.join("/")
}

/// Go `filepath.Abs(filepath.Dir(project))`.
fn project_dir(project: &str) -> String {
    let dir = match project.rfind('/') {
        Some(0) => "/",
        Some(index) => &project[..index],
        None => ".",
    };
    if dir.starts_with('/') {
        return format!("/{}", clean_components(dir).join("/"));
    }
    let cwd = std::env::current_dir().expect("current directory");
    let joined = format!("{}/{dir}", cwd.to_string_lossy());
    format!("/{}", clean_components(&joined).join("/"))
}

struct Unit {
    file: TestFile,
    header: String,
    name: String,
}

fn run(project: &str, out_dir: &str) -> i32 {
    let frontend = std::env::var("GOPORT_FRONTEND").unwrap_or_else(|_| "go (default)".to_string());
    eprintln!("frontend: {frontend}");
    match catch_unwind(AssertUnwindSafe(|| try_load(project))) {
        Ok(Ok(_)) => {}
        Ok(Err(message)) => {
            eprintln!("goport_typesyms: {message}");
            return 1;
        }
        Err(payload) => {
            note_panic(payload.as_ref());
            eprintln!("goport_typesyms: load panicked");
            return 2;
        }
    }

    let diagnostics = guard(collect_all_diagnostics);
    let had_error_baseline = !diagnostics.is_empty();

    let dir = project_dir(project);
    let units: Vec<Unit> = source_files()
        .into_iter()
        .filter(|&f| !is_source_file_default_library(&source_file_info(f).path))
        .map(|f| {
            let file_name = source_file_file_name(f);
            let header = relative_path(&dir, file_name);
            Unit {
                name: header.replace('/', "!"),
                header,
                file: TestFile {
                    unit_name: file_name.to_string(),
                    content: source_file_text(f).to_string(),
                },
            }
        })
        .collect();

    std::fs::create_dir_all(out_dir).expect("create output directory");
    let mut walker = new_type_writer_walker(had_error_baseline);
    walker.catch_panics = true;
    for is_symbol in [false, true] {
        let ext = if is_symbol { ".symbols" } else { ".types" };
        for unit in &units {
            let text = generate_baseline(
                std::slice::from_ref(&unit.file),
                &mut walker,
                &unit.header,
                is_symbol,
            );
            // Go writes the baseline string bytes unchanged, so write each
            // invalid source byte sentinel as its raw byte.
            std::fs::write(
                format!("{out_dir}/{}{ext}", unit.name),
                raw_file_bytes(&text),
            )
            .expect("write baseline");
        }
    }

    let mut list = String::new();
    for unit in &units {
        list.push_str(&unit.file.unit_name);
        list.push('\n');
    }
    list.push_str("hadErrorBaseline ");
    list.push_str(if had_error_baseline { "true" } else { "false" });
    list.push('\n');
    std::fs::write(format!("{out_dir}/files.txt"), list).expect("write files.txt");

    let unported = unported_report();
    let mut stderr = std::io::stderr().lock();
    let _ = writeln!(
        stderr,
        "files {} diagnostics {} node panics {}",
        units.len(),
        diagnostics.len(),
        walker.panic_count
    );
    for (name, count) in &unported {
        let _ = writeln!(stderr, "unported: {name} {count}");
    }
    if unported.is_empty() && walker.panic_count == 0 {
        0
    } else {
        2
    }
}
