//! `goport_live_programs`: several live programs in one process, the way the
//! language server holds them (one per project, checkers of each on one
//! thread, a program released while another one works).
//!
//! `live <out-dir> <mode>:<tsconfig>...` loads each project as a program
//! version, in order, and keeps them all live. `<mode>` is `check` (the
//! `goport -p` report: `--noEmit --pretty false`) or `emit` (the `goport_emit`
//! report and outputs: `--outDir <out-dir>/<i>/out --pretty false`). Then:
//! 1. It reports each program in load order and writes `<out-dir>/<i>/report.txt`,
//!    `<out-dir>/<i>/status` and, for `emit`, the outputs under
//!    `<out-dir>/<i>/out`.
//! 2. It reports each program again in load order, then once more in
//!    reverse order. The reverse-order reports must equal the load-order
//!    ones. A `check` report must also equal step 1. An `emit` report must
//!    have the outputs of step 1, but it can have more diagnostics: the emit
//!    resolves names with error reports (Go `MarkLinkedReferencesRecursively`),
//!    and the checker returns those errors in later reports, as tsgo does
//!    (Hono: two TS2448 errors after the first emit).
//! 3. It makes two checkers of each program on this thread and checks every
//!    file with each, the programs taking turns file by file. For each file
//!    it writes the semantic diagnostics and the type of each top-level
//!    variable (printed at its declaration, so a type from a module the file
//!    does not import is an `import(...)` type) to `<out-dir>/<i>/checker.txt`,
//!    in Go bytes: a type cut inside a char keeps the bytes of that char, as
//!    in Go. The two checkers of a program must write the same text.
//! 4. Symbol ids of those checkers: a binder symbol has one id in every
//!    checker, and the symbols that a checker adds have ids that no other
//!    symbol has.
//!
//! `release <out-dir> <tsconfig-p> <tsconfig-q>` checks (`check` mode) P on
//! this thread and Q on a second loading thread, then releases P (and joins
//! its workers) while a job of Q waits on Q's checker pool, and reports P
//! again while that job waits. It writes `p.txt`, `p.status`, `q.txt` and
//! `q.status`. Every later report must equal the first one.
//!
//! A failed check or an unported hit panics. Exit codes: 0 when every check
//! passes, 1 when one fails, 2 for a usage error.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, mpsc};

use ts_goport::emitter::program_emit::{WriteFile, WriteFileData};
use ts_goport::execute::tsc::{
    CompileTimes, CompilerProgram, EmitInput, ProgramLike, Writer, create_diagnostic_reporter,
    create_report_error_summary, emit_and_report_statistics, new_os_system,
};
use ts_goport::frontend::tspath::{normalize_path, resolve_path};
use ts_goport::prelude::*;

const USAGE: &str = "usage: goport_live_programs live <out-dir> <check|emit>:<tsconfig>...
       goport_live_programs release <out-dir> <tsconfig-p> <tsconfig-q>";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let worker = std::thread::Builder::new()
        .name("goport_live_programs".to_string())
        .stack_size(ts_goport::gostd::stack::max_stack_size())
        .spawn(move || run(&args));
    let code = match worker.map(std::thread::JoinHandle::join) {
        Ok(Ok(Ok(()))) => 0,
        Ok(Ok(Err(message))) => {
            eprintln!("goport_live_programs: {message}\n{USAGE}");
            2
        }
        _ => {
            eprintln!("goport_live_programs: FAIL");
            1
        }
    };
    std::process::exit(code);
}

/// Reads the command line and runs one mode. `Err` is a usage error.
fn run(args: &[String]) -> Result<(), String> {
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match args.as_slice() {
        ["live", out, projects @ ..] if !projects.is_empty() => {
            let projects = projects
                .iter()
                .map(|project| match project.split_once(':') {
                    Some(("check", config)) => Ok((Mode::Check, config.to_string())),
                    Some(("emit", config)) => Ok((Mode::Emit, config.to_string())),
                    _ => Err(format!("bad project {project}")),
                })
                .collect::<Result<Vec<_>, _>>()?;
            live(Path::new(out), &projects);
        }
        ["release", out, p, q] => release(Path::new(out), p, q),
        _ => return Err(format!("wrong arguments {args:?}")),
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum Mode {
    /// `goport -p`.
    Check,
    /// `goport_emit -p --outDir`.
    Emit,
}

/// One report: stdout bytes, exit code and, for `emit`, the outputs by path.
#[derive(PartialEq)]
struct Report {
    stdout: Vec<u8>,
    status: i32,
    outputs: BTreeMap<String, String>,
}

/// A live program and how it reports.
struct Live {
    program: &'static GoProgram,
    mode: Mode,
    dir: PathBuf,
}

/// The `live` mode. Each step number matches the file comment.
fn live(out: &Path, projects: &[(Mode, String)]) {
    let lives: Vec<Live> = projects
        .iter()
        .enumerate()
        .map(|(i, (mode, config))| load_live(&out.join(i.to_string()), *mode, config))
        .collect();

    // 1.
    let first: Vec<Report> = lives.iter().map(report).collect();
    for (live, report) in lives.iter().zip(&first) {
        write(&live.dir.join("report.txt"), &report.stdout);
        write(
            &live.dir.join("status"),
            report.status.to_string().as_bytes(),
        );
        let root = format!("{}/", go_path(&live.dir.join("out")));
        for (path, text) in &report.outputs {
            assert!(
                path.starts_with(&root),
                "program {} wrote {path} outside {root}",
                live.program.id
            );
            write(Path::new(path), text.as_bytes());
        }
    }

    // 2.
    let settled: Vec<Report> = lives.iter().map(report).collect();
    for ((live, first), settled) in lives.iter().zip(&first).zip(&settled) {
        let same = match live.mode {
            Mode::Check => settled == first,
            Mode::Emit => settled.outputs == first.outputs,
        };
        if !same {
            write_second_report(live, settled);
            panic!(
                "program {}: a second report differs from the first (see {}/second)",
                live.program.id,
                live.dir.display()
            );
        }
    }
    for (live, expected) in lives.iter().zip(&settled).rev() {
        let again = report(live);
        if again != *expected {
            write_second_report(live, &again);
            panic!(
                "program {}: a reverse-order report differs from the load-order one (see {}/second)",
                live.program.id,
                live.dir.display()
            );
        }
    }

    // 3.
    let checkers = check_on_this_thread(&lives);

    // 4.
    let arenas: Vec<(&SymbolArena, usize)> = lives
        .iter()
        .zip(&checkers)
        .flat_map(|(live, pair)| {
            let shared = ts_goport::program::bound_symbols_of(live.program)
                .expect("program bound")
                .symbol_count();
            pair.iter().map(move |checker| (&checker.symbols, shared))
        })
        .collect();
    check_symbol_ids(&arenas);

    drop(checkers);
    for live in &lives {
        release_program(live.program);
    }
    assert_no_unported();
    println!("live: pass programs={}", lives.len());
}

/// Writes a step 2 report that differs from the one it must equal under
/// `<dir>/second`: `report.txt`, `status` and the outputs at their paths
/// under `out`.
fn write_second_report(live: &Live, report: &Report) {
    let second = live.dir.join("second");
    create_dir(&second);
    write(&second.join("report.txt"), &report.stdout);
    write(&second.join("status"), report.status.to_string().as_bytes());
    let root = format!("{}/", go_path(&live.dir.join("out")));
    for (path, text) in &report.outputs {
        let relative = path.strip_prefix(&root).unwrap_or(path);
        write(&second.join("out").join(relative), text.as_bytes());
    }
}

/// Loads `config` as a new program version that reports in `mode`, with
/// its outputs under `<dir>/out`.
fn load_live(dir: &Path, mode: Mode, config: &str) -> Live {
    create_dir(dir);
    let out_dir = go_path(&dir.join("out"));
    let program = try_load_version(config, |options| {
        options.pretty = Tristate::False;
        match mode {
            Mode::Check => options.no_emit = Tristate::True,
            Mode::Emit => options.out_dir.clone_from(&out_dir),
        }
    })
    .unwrap_or_else(|e| panic!("load {config}: {e}"));
    Live {
        program,
        mode,
        dir: dir.to_path_buf(),
    }
}

/// Step 3 of `live`: two checkers of each program on this thread, which
/// check the files of every program by turns. Returns the checkers, each
/// in a box (a `Checker` is too large for an array on the stack).
fn check_on_this_thread(lives: &[Live]) -> Vec<[Box<Checker>; 2]> {
    let mut checkers: Vec<[Box<Checker>; 2]> = lives
        .iter()
        .map(|live| {
            let _scope = enter_program(Some(live.program));
            [Box::new(Checker::new(0)), Box::new(Checker::new(1))]
        })
        .collect();
    let mut texts: Vec<[String; 2]> = vec![[String::new(), String::new()]; lives.len()];
    let most_files = lives
        .iter()
        .map(|live| live.program.source_file_order().len())
        .max()
        .unwrap_or(0);
    for position in 0..most_files {
        for ((live, pair), text) in lives.iter().zip(&mut checkers).zip(&mut texts) {
            let Some(&file) = live.program.source_file_order().get(position) else {
                continue;
            };
            let _scope = enter_program(Some(live.program));
            for (checker, text) in pair.iter_mut().zip(text.iter_mut()) {
                check_file(checker, go_file(file).root, text);
            }
        }
    }
    for ((live, text), pair) in lives.iter().zip(&texts).zip(&checkers) {
        assert!(
            text[0] == text[1],
            "program {}: two checkers of one program wrote different text",
            live.program.id
        );
        assert!(
            pair.iter()
                .all(|checker| std::ptr::eq(checker.program, live.program)),
            "a checker has another program"
        );
        write(&live.dir.join("checker.txt"), &go_string_bytes(&text[0]));
    }
    checkers
}

/// Step 3 of `live` for one checker and one file of the current program.
fn check_file(checker: &mut Checker, file: Node, text: &mut String) {
    let info = source_file_info(file);
    let _ = writeln!(text, "== {}", info.file_name);
    for diagnostic in get_semantic_diagnostics_with_checker(
        &ts_goport::gostd::context::background(),
        checker,
        file,
    ) {
        let _ = writeln!(text, "{}", format_diagnostic(&diagnostic));
    }
    if info.is_declaration_file {
        return;
    }
    for statement in file.statements() {
        if !is_variable_statement(statement) {
            continue;
        }
        for declaration in statement.declaration_list().declarations().nodes() {
            let symbol = checker.get_symbol_of_declaration(declaration);
            let t = checker.get_type_of_symbol(symbol);
            // Without `UseAliasDefinedOutsideCurrentScope`, a type that the
            // file cannot name gets a module specifier.
            let printed = checker.type_to_string_ex(t, declaration, TypeFormatFlags::NONE, None);
            let _ = writeln!(text, "{}: {printed}", checker.symbols.sym(symbol).name);
        }
    }
}

/// Step 4 of `live`. `arenas` holds each checker arena with the symbol
/// count of its program's binder arena. The ids of binder symbols (the
/// even chunks below the count) must agree between arenas, and the ids of
/// the symbols that a checker added (`SymbolArena::own_symbols`) must be
/// unique.
fn check_symbol_ids(arenas: &[(&SymbolArena, usize)]) {
    let mut binder: BTreeMap<usize, u64> = BTreeMap::new();
    for (arena, shared) in arenas {
        for index in (1..*shared).filter(|&index| !is_own_index(symbol_at(index).0)) {
            let id = get_symbol_id(arena, symbol_at(index));
            let known = *binder.entry(index).or_insert(id);
            assert!(
                known == id,
                "binder symbol {index} has id {known} in one checker and {id} in another"
            );
        }
    }
    // Who has each id: (checker, index), where checker is None for binder
    // symbols.
    let mut owners: BTreeMap<u64, (Option<usize>, usize)> = BTreeMap::new();
    for (&index, &id) in &binder {
        if let Some(other) = owners.insert(id, (None, index)) {
            panic!("binder symbols {index} and {other:?} have id {id}");
        }
    }
    for (checker, (arena, _)) in arenas.iter().enumerate() {
        for symbol in arena.own_symbols() {
            let id = get_symbol_id(arena, symbol);
            let index = symbol.index();
            if let Some(other) = owners.insert(id, (Some(checker), index)) {
                panic!(
                    "own symbol {index:#x} of checker {checker} has id {id}, like symbol {other:?}"
                );
            }
        }
    }
}

/// The symbol handle of arena index `index`.
fn symbol_at(index: usize) -> SymbolId {
    SymbolId(u32::try_from(index).expect("symbol index"))
}

/// The `release` mode.
fn release(out: &Path, p_config: &str, q_config: &str) {
    create_dir(out);
    let p = load_check(p_config);
    let p_first = report_check(p);
    write(&out.join("p.txt"), &p_first.0);
    write(&out.join("p.status"), p_first.1.to_string().as_bytes());

    let (busy_sender, busy) = mpsc::channel::<()>();
    let (released_sender, released) = mpsc::channel::<()>();
    let q_config = q_config.to_string();
    let q_out = out.to_path_buf();
    // Q loads after P is loaded and bound, so the two loads do not overlap.
    let q_thread = std::thread::Builder::new()
        .name("second-loading-thread".to_string())
        .stack_size(ts_goport::gostd::stack::max_stack_size())
        .spawn(move || {
            let q = load_check(&q_config);
            let q_first = report_check(q);
            write(&q_out.join("q.txt"), &q_first.0);
            write(&q_out.join("q.status"), q_first.1.to_string().as_bytes());
            let scope = enter_program(Some(q));
            let file = go_file(
                *q.source_file_order()
                    .last()
                    .expect("the second program has files"),
            )
            .root;
            let before =
                with_type_checker_for_file(file, move |checker| diagnostics_text(checker, file));
            // This job holds a checker of Q while P is released.
            let during = with_type_checker_for_file(file, move |checker| {
                busy_sender.send(()).expect("the first thread waits");
                released.recv().expect("the first thread releases P");
                diagnostics_text(checker, file)
            });
            assert!(
                before == during,
                "a check of Q changed while P was released"
            );
            drop(scope);
            assert!(
                report_check(q) == q_first,
                "a report of Q changed after P was released"
            );
            release_program(q);
        })
        .expect("cannot start the second loading thread");

    busy.recv().expect("Q's job starts");
    // P works while a job of Q waits on Q's pool.
    assert!(
        report_check(p) == p_first,
        "a report of P changed while Q was live"
    );
    release_program(p);
    released_sender.send(()).expect("Q's job waits");
    if let Err(payload) = q_thread.join() {
        std::panic::resume_unwind(payload);
    }
    assert_no_unported();
    println!("release: pass");
}

/// The formatted semantic diagnostics of `file`, with the checker of its
/// program on a worker thread.
fn diagnostics_text(checker: &mut Checker, file: Node) -> String {
    get_semantic_diagnostics_with_checker(&ts_goport::gostd::context::background(), checker, file)
        .iter()
        .map(|diagnostic| format_diagnostic(diagnostic) + "\n")
        .collect()
}

/// A new program version of `config` with the `goport` options.
fn load_check(config: &str) -> &'static GoProgram {
    try_load_version(config, |options| {
        options.no_emit = Tristate::True;
        options.pretty = Tristate::False;
    })
    .unwrap_or_else(|e| panic!("load {config}: {e}"))
}

/// The `goport -p` stdout and exit code of `p`.
fn report_check(p: &'static GoProgram) -> (Vec<u8>, i32) {
    let report = report(&Live {
        program: p,
        mode: Mode::Check,
        dir: PathBuf::new(),
    });
    (report.stdout, report.status)
}

/// The report of `live.program`: `goport` for `check`, `goport_emit` for
/// `emit`, with the outputs kept in memory.
fn report(live: &Live) -> Report {
    let _scope = enter_program(Some(live.program));
    let sys = new_os_system().unwrap_or_else(|status| panic!("no system: {status:?}"));
    let buffer: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
    let writer: Writer = buffer.clone();
    let sys = sys.with_writer(writer.clone());
    let options = options();
    let outputs: Arc<Mutex<BTreeMap<String, String>>> = Arc::default();
    let write_file: Option<WriteFile> = match live.mode {
        Mode::Check => None,
        Mode::Emit => {
            let outputs = Arc::clone(&outputs);
            Some(Arc::new(
                move |file_name: &str, text: &str, _data: &mut WriteFileData| {
                    outputs
                        .lock()
                        .expect("outputs")
                        .insert(normalize_path(file_name), text.to_string());
                    Ok(())
                },
            ))
        }
    };
    // #4407: under `noEmit`, Go's incremental `Program.Emit` gives the
    // result of the plain one (goport writes no build info), so `check`
    // uses the plain program as `emit` does, and its report equals a fresh
    // `goport` run.
    let program_like: &dyn ProgramLike = &CompilerProgram;
    let (result, _statistics) = emit_and_report_statistics(&EmitInput {
        sys: &sys,
        program_like,
        config: None,
        report_diagnostic: create_diagnostic_reporter(
            &sys,
            writer.clone(),
            &ts_goport::locale::DEFAULT,
            options,
        ),
        report_error_summary: create_report_error_summary(
            &sys,
            &ts_goport::locale::DEFAULT,
            Some(options),
        ),
        writer,
        write_file,
        compile_times: Rc::new(RefCell::new(CompileTimes::default())),
        testing: None,
        testing_m_times_cache: None,
    });
    assert_no_unported();
    let outputs = std::mem::take(&mut *outputs.lock().expect("outputs"));
    Report {
        stdout: buffer.take(),
        status: result.status.code(),
        outputs,
    }
}

/// Panics when any unported code was hit.
fn assert_no_unported() {
    let hits = unported_report();
    assert!(hits.is_empty(), "unported code was hit: {hits:?}");
}

/// `path` as a Go path: absolute and normalized.
fn go_path(path: &Path) -> String {
    let cwd = std::env::current_dir().expect("no current directory");
    resolve_path(
        &normalize_path(&cwd.to_string_lossy()),
        &[&path.to_string_lossy()],
    )
}

fn create_dir(path: &Path) {
    std::fs::create_dir_all(path).unwrap_or_else(|e| panic!("create {}: {e}", path.display()));
}

fn write(path: &Path, bytes: &[u8]) {
    if let Some(parent) = path.parent() {
        create_dir(parent);
    }
    std::fs::write(path, bytes).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
}
