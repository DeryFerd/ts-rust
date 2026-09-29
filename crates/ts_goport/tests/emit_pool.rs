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

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use ts_goport::core::enter_program;
use ts_goport::emitter::emitter::EmitOnly;
use ts_goport::emitter::program_emit::{
    EmitOptions, EmitResult, WriteFile, WriteFileData, combine_emit_results, emit, emit_batch,
};
use ts_goport::options::{CompilerOptions, Tristate};
use ts_goport::program::{
    emit_pool_job_count, format_diagnostic, release_program, source_files, try_load_version,
};

const CONFIG: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/emit_pool/tsconfig.json"
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
    let program = try_load_version(CONFIG, edit)
        .unwrap_or_else(|error| panic!("cannot load {CONFIG}: {error}"));
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

/// Runs `run_emit` with a write callback that records each write, and
/// returns what it wrote and returned. It asserts that each `.d.ts` is
/// written after the `.js` of the same file.
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
        let Some(stem) = name.strip_suffix(".d.ts") else {
            continue;
        };
        let js = format!("{stem}.js");
        if let Some(js_index) = order.iter().position(|other| *other == js) {
            assert!(js_index < index, "{js} is written after {name}: {order:?}");
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
