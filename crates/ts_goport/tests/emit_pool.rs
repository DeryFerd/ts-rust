//! The emit pool (`program::send_emit_pool_jobs`). A project whose JS
//! transforms need no checker writes the same files and returns the same
//! `EmitResult` with the pool as with `--singleThreaded` (no pool) and with
//! `--checkers 1`, through `emit` and then `emit_batch` in the same program.
//! Each file's `.js` is written before its `.d.ts`, as in Go.
//!
//! The fixture (`fixtures/emit_pool`) uses `verbatimModuleSyntax`, so Go
//! picks the binder reference resolver. `shapes.ts` has class fields that
//! the class fields transform lowers (target ES2020), a method that reads
//! `arguments`, a class expression and a namespace. `colors.ts` has an
//! enum, so its JS part stays on the checker thread. `legacy.js` is a JS
//! file. Without declarations, whole files run on the pool.
//!
//! The test needs the pool on: do not set `GOPORT_EMIT_THREADS=0`.
//!
//! The d.ts part of a split file prints on the d.ts twin of its checker
//! (`program::send_dts_twin_job`). With the twins in check mode (each print
//! also runs on the checker, and the twin panics on a different text) the
//! emit writes and returns the same as with the twins off.
//!
//! A file whose JS transforms call the checker emits on its checker thread,
//! and the twin prints its JS and d.ts parts. The second fixture
//! (`fixtures/js_twin`) has import elision on (no `verbatimModuleSyntax`),
//! decorators with metadata, enums and a const enum, private names and
//! async generators that target ES2017 lowers (helpers and generated
//! names), so every file's JS part needs the checker. Each file's outputs
//! are written in Go's order: map, JS, declaration map, d.ts.
//!
//! A panic in a file's declaration transforms or in its JS print
//! (`set_emit_test_panic`) writes the same files and returns the same with
//! the twins on as with the twins off, with a guard around each file (as the
//! goport bin has) and without one.

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use ts_goport::core::enter_program;
use ts_goport::emitter::emitter::{EmitOnly, EmitTestPanic, set_emit_test_panic};
use ts_goport::emitter::program_emit::{
    DtsTwinMode, EmitOptions, EmitResult, WriteFile, WriteFileData, combine_emit_results, emit,
    emit_batch, emit_with, js_twin_print_count, set_dts_twin_mode,
};
use ts_goport::options::{CompilerOptions, Tristate};
use ts_goport::program::{
    dts_twin_job_count, emit_pool_job_count, format_diagnostic, release_program, source_files,
    try_load_version,
};

/// The tests of this file run one at a time: the d.ts twin mode and the
/// twin job count are process-wide.
static SERIAL: Mutex<()> = Mutex::new(());

const CONFIG: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/emit_pool/tsconfig.json"
);

const JS_TWIN_CONFIG: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/js_twin/tsconfig.json"
);

/// What one emit wrote and returned.
#[derive(Debug, PartialEq)]
struct Written {
    /// The written text by file name.
    files: BTreeMap<String, String>,
    emit_skipped: bool,
    diagnostics: Vec<String>,
    emitted_files: Vec<String>,
    source_maps: Vec<String>,
}

/// The `emit` and `emit_batch` of one load of the fixture, and the number of
/// jobs its emit pool got.
struct Run {
    emit: Written,
    batch: Written,
    pool_jobs: usize,
}

#[test]
fn pool_emits_like_the_checker_threads() {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let pool = run(|_| {});
    assert!(pool.pool_jobs > 0, "the emit pool got no job");
    assert!(
        pool.emit
            .files
            .keys()
            .any(|name| name.ends_with("/out/shapes.js")),
        "the fixture must emit shapes.js: {:?}",
        pool.emit.files.keys()
    );

    let single = run(single_threaded);
    assert_eq!(
        single.pool_jobs, 0,
        "--singleThreaded must not use the pool"
    );
    assert_same(&pool, &single, "the pool against --singleThreaded");

    let one_checker = run(|options| options.checkers = Some(1));
    assert!(one_checker.pool_jobs > 0, "--checkers 1 must use the pool");
    assert_same(&pool, &one_checker, "4 checkers against --checkers 1");

    let whole = run(no_declarations);
    assert!(
        whole.pool_jobs > 0,
        "without declarations the pool must run"
    );
    let whole_single = run(|options| {
        no_declarations(options);
        single_threaded(options);
    });
    assert_same(
        &whole,
        &whole_single,
        "no declarations: the pool against --singleThreaded",
    );
}

#[test]
fn dts_twins_print_like_the_checker_threads() {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    for edit in [
        (|_: &mut CompilerOptions| {}) as fn(&mut CompilerOptions),
        |options| options.checkers = Some(1),
    ] {
        set_dts_twin_mode(Some(DtsTwinMode::Check));
        let twin_jobs = dts_twin_job_count();
        let twins = run(edit);
        let twin_jobs = dts_twin_job_count() - twin_jobs;
        set_dts_twin_mode(Some(DtsTwinMode::Off));
        let checkers = run(edit);
        set_dts_twin_mode(None);

        assert!(twin_jobs > 0, "the d.ts twins got no job");
        assert!(
            twins
                .emit
                .files
                .keys()
                .any(|name| name.ends_with("/out/shapes.d.ts")),
            "the fixture must emit shapes.d.ts: {:?}",
            twins.emit.files.keys()
        );
        assert_same(&twins, &checkers, "d.ts twins against the checker threads");
    }
}

#[test]
fn twins_print_js_like_the_checker_threads() {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    for (edit, prints_js) in [
        (
            (|_: &mut CompilerOptions| {}) as fn(&mut CompilerOptions),
            true,
        ),
        (|options| options.checkers = Some(1), true),
        (no_declarations, true),
        (
            |options| options.emit_declaration_only = Tristate::True,
            false,
        ),
    ] {
        set_dts_twin_mode(Some(DtsTwinMode::Check));
        let js_prints = js_twin_print_count();
        let twin_jobs = dts_twin_job_count();
        let twins = run_config(JS_TWIN_CONFIG, edit);
        let js_prints = js_twin_print_count() - js_prints;
        let twin_jobs = dts_twin_job_count() - twin_jobs;
        set_dts_twin_mode(Some(DtsTwinMode::Off));
        let checkers = run_config(JS_TWIN_CONFIG, edit);
        set_dts_twin_mode(None);

        assert!(twin_jobs > 0, "the twins got no job");
        // `emit` and `emit_batch` each print the 3 files.
        assert_eq!(
            js_prints,
            if prints_js { 6 } else { 0 },
            "JS prints on the twins"
        );
        assert_eq!(
            twins.emit.files.len(),
            checkers.emit.files.len(),
            "the twins and the checkers wrote other files"
        );
        assert!(
            twins
                .emit
                .files
                .keys()
                .any(|name| name.ends_with("/out/model.d.ts") || name.ends_with("/out/model.js")),
            "the fixture must emit model.js or model.d.ts: {:?}",
            twins.emit.files.keys()
        );
        assert_same(&twins, &checkers, "twins against the checker threads");
    }
}

#[test]
fn twin_panics_write_like_the_checker_threads() {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    for step in [EmitTestPanic::DeclarationTransforms, EmitTestPanic::JsPrint] {
        set_emit_test_panic(Some((step, "/src/model.ts")));
        set_dts_twin_mode(Some(DtsTwinMode::On));
        let js_prints = js_twin_print_count();
        let twins = run_panic(JS_TWIN_CONFIG);
        let js_prints = js_twin_print_count() - js_prints;
        set_dts_twin_mode(Some(DtsTwinMode::Off));
        let checkers = run_panic(JS_TWIN_CONFIG);
        set_dts_twin_mode(None);
        set_emit_test_panic(None);

        assert!(js_prints > 0, "{step:?}: the twins printed no JS file");
        assert_eq!(twins.guard_panics, 1, "{step:?}: guarded panics");
        assert!(
            twins.panic.as_deref().is_some_and(
                |message| message.starts_with(&format!("emit test panic: {step:?} in "))
            ),
            "{step:?}: the emit without a guard must go on with the test panic: {:?}",
            twins.panic
        );
        assert_eq!(
            twins.guarded.files, twins.unguarded.files,
            "{step:?}: the guard must not change the writes"
        );
        let model = |extension: &str| {
            twins
                .guarded
                .files
                .keys()
                .any(|name| name.ends_with(&format!("/out/model{extension}")))
        };
        let written: Vec<bool> = GO_ORDER.iter().map(|extension| model(extension)).collect();
        let expected = match step {
            // Go writes the map and the JS before the declaration transforms.
            EmitTestPanic::DeclarationTransforms => [true, true, false, false],
            EmitTestPanic::JsPrint => [false; 4],
        };
        assert_eq!(written, expected, "{step:?}: model outputs {GO_ORDER:?}");
        assert!(
            twins
                .guarded
                .files
                .keys()
                .any(|name| name.ends_with("/out/shape.d.ts")),
            "{step:?}: the other files must emit: {:?}",
            twins.guarded.files.keys()
        );
        assert_eq!(
            twins, checkers,
            "{step:?}: twins against the checker threads"
        );
    }
}

/// What one load of a fixture wrote and returned with a test panic
/// (`set_emit_test_panic`).
#[derive(Debug, PartialEq)]
struct PanicRun {
    /// `emit_with` with a guard around each file.
    guarded: Written,
    /// The panics that the guard caught.
    guard_panics: usize,
    /// `emit` without a guard, which panics.
    unguarded: Written,
    /// The message of the panic of `emit`, if it panicked.
    panic: Option<String>,
}

/// The panics that `guard` caught.
static GUARD_PANICS: AtomicUsize = AtomicUsize::new(0);

/// The guard around each file's emit, as the goport bin has: a panic gives
/// the file an empty result.
fn guard(emit_file: &dyn Fn() -> EmitResult) -> EmitResult {
    catch_unwind(AssertUnwindSafe(emit_file)).unwrap_or_else(|_| {
        GUARD_PANICS.fetch_add(1, Ordering::Relaxed);
        EmitResult::default()
    })
}

/// Loads `config`, emits it with `emit_with` and `guard`, then with `emit`,
/// and releases it.
fn run_panic(config: &str) -> PanicRun {
    let program = try_load_version(config, |_| {})
        .unwrap_or_else(|error| panic!("cannot load {config}: {error}"));
    let run = {
        let _scope = enter_program(Some(program));
        let guard_panics = GUARD_PANICS.load(Ordering::Relaxed);
        let guarded = record_writes(|write_file| {
            emit_with(
                EmitOptions {
                    write_file: Some(write_file),
                    ..EmitOptions::default()
                },
                guard,
            )
        });
        let guard_panics = GUARD_PANICS.load(Ordering::Relaxed) - guard_panics;
        let mut panic = None;
        let unguarded = record_writes(|write_file| {
            catch_unwind(AssertUnwindSafe(|| {
                emit(EmitOptions {
                    write_file: Some(write_file),
                    ..EmitOptions::default()
                })
            }))
            .unwrap_or_else(|payload| {
                panic = Some(
                    payload
                        .downcast_ref::<String>()
                        .cloned()
                        .unwrap_or_default(),
                );
                EmitResult::default()
            })
        });
        PanicRun {
            guarded,
            guard_panics,
            unguarded,
            panic,
        }
    };
    release_program(program);
    run
}

/// Asserts that two runs wrote and returned the same, for `emit` and for
/// the `emit_batch` that follows it in the same program.
fn assert_same(a: &Run, b: &Run, what: &str) {
    assert_eq!(a.emit, b.emit, "{what}: emit");
    assert_eq!(a.batch, b.batch, "{what}: emit_batch");
}

fn single_threaded(options: &mut CompilerOptions) {
    options.single_threaded = Tristate::True;
}

fn no_declarations(options: &mut CompilerOptions) {
    options.declaration = Tristate::False;
    options.declaration_map = Tristate::False;
}

/// Loads the fixture with `edit` applied to its options, emits it with
/// `emit` and with `emit_batch`, and releases it.
fn run(edit: impl FnOnce(&mut CompilerOptions)) -> Run {
    run_config(CONFIG, edit)
}

/// `run` of the fixture `config`.
fn run_config(config: &str, edit: impl FnOnce(&mut CompilerOptions)) -> Run {
    let program = try_load_version(config, edit)
        .unwrap_or_else(|error| panic!("cannot load {config}: {error}"));
    let run = {
        let _scope = enter_program(Some(program));
        let emitted = record_writes(|write_file| {
            emit(EmitOptions {
                write_file: Some(write_file),
                ..EmitOptions::default()
            })
        });
        let batch = record_writes(|write_file| {
            let targets = source_files()
                .into_iter()
                .map(|file| EmitOptions {
                    target_source_files: Some(vec![file]),
                    emit_only: EmitOnly::All,
                    force_emit: false,
                    write_file: Some(write_file.clone()),
                })
                .collect();
            combine_emit_results(emit_batch(targets))
        });
        Run {
            emit: emitted,
            batch,
            pool_jobs: emit_pool_job_count(),
        }
    };
    release_program(program);
    run
}

/// The outputs of one file in the order Go writes them.
const GO_ORDER: [&str; 4] = [".js.map", ".js", ".d.ts.map", ".d.ts"];

/// Runs `run_emit` with a write callback that records each write, and
/// returns what it wrote and returned. It asserts that the outputs of each
/// file are written in Go's order: the `.js.map`, the `.js`, the
/// `.d.ts.map`, then the `.d.ts`.
fn record_writes(run_emit: impl FnOnce(WriteFile) -> EmitResult) -> Written {
    let writes: Arc<Mutex<Vec<(String, String)>>> = Arc::default();
    let sink = Arc::clone(&writes);
    let write_file: WriteFile =
        Arc::new(move |name: &str, text: &str, _data: &mut WriteFileData| {
            sink.lock()
                .expect("writes lock")
                .push((name.to_string(), text.to_string()));
            Ok(())
        });
    let result = run_emit(write_file);
    let writes = std::mem::take(&mut *writes.lock().expect("writes lock"));

    let order: Vec<&str> = writes.iter().map(|(name, _)| name.as_str()).collect();
    for (index, name) in order.iter().enumerate() {
        let Some((stem, rank)) = GO_ORDER
            .iter()
            .enumerate()
            .find_map(|(rank, extension)| name.strip_suffix(extension).map(|stem| (stem, rank)))
        else {
            continue;
        };
        for before in &GO_ORDER[..rank] {
            let before = format!("{stem}{before}");
            if let Some(before_index) = order.iter().position(|other| *other == before) {
                assert!(
                    before_index < index,
                    "{before} is written after {name}: {order:?}"
                );
            }
        }
    }

    Written {
        files: writes.into_iter().collect(),
        emit_skipped: result.emit_skipped,
        diagnostics: result.diagnostics.iter().map(format_diagnostic).collect(),
        emitted_files: result.emitted_files,
        source_maps: result
            .source_maps
            .iter()
            .map(|source_map| format!("{source_map:?}"))
            .collect(),
    }
}
