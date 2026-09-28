//! The early emit of `tsc -p` with an incremental program
//! (`execute::incremental::Program::start_check_and_emit`). Each checker gets
//! its emit jobs right behind its check job, so it emits when its own check
//! ends and the emit pool runs during the check. The outputs, the build
//! info, stdout and the exit code must be the same as with
//! `GOPORT_EARLY_EMIT=0`, which keeps Go's barrier (the emit starts after
//! the whole check).
//!
//! The fixture is `fixtures/emit_pool`: 4 program files and the es2020 lib
//! files, so 4 checkers get files. With declarations the JS parts of
//! `shapes.ts`, `legacy.js` and `index.ts` go to the emit pool and the d.ts
//! parts stay on the checker threads. `GOPORT_EMIT_THREADS=2` turns the pool
//! on at any core count. Each `tsgo` run writes to the same new directory
//! under the system temp dir, so the source map and build info paths are
//! the same. A passing test deletes it.
//!
//! The rule test checks `emit_can_start_with_check` on the same fixture:
//! each case that a check could see the outputs of keeps the barrier. Do not
//! set `GOPORT_EARLY_EMIT=0` for this test. Its F2 cases load
//! `tsconfig.rules.json` (the same config with `"exclude": []`): without an
//! `exclude`, the config excludes `outDir` and `declarationDir` from its
//! files, so no program file would be inside them.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use ts_goport::core::enter_program;
use ts_goport::emitter::program_emit::emit_can_start_with_check;
use ts_goport::flags::{ModuleKind, ModuleResolutionKind};
use ts_goport::options::{CompilerOptions, Tristate};
use ts_goport::program::{release_program, try_load_version};

const FIXTURE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/emit_pool");

const CONFIG: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/emit_pool/tsconfig.json"
);

/// `CONFIG` with `"exclude": []`, so program files can be in the output
/// directories.
const RULES_CONFIG: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/emit_pool/tsconfig.rules.json"
);

/// What one `tsgo` run wrote and printed.
#[derive(Debug, PartialEq)]
struct Run {
    /// The bytes of each file under the out dir, by relative path.
    files: BTreeMap<String, Vec<u8>>,
    stdout: String,
    status: Option<i32>,
}

#[test]
fn early_emit_writes_what_the_barrier_writes() {
    let root = scratch_dir();
    let out = root.join("out");
    let cases: [(&str, &[&str]); 3] = [
        ("js and d.ts", &[]),
        (
            "js only",
            &["--declaration", "false", "--declarationMap", "false"],
        ),
        ("d.ts only", &["--emitDeclarationOnly"]),
    ];
    for (case, extra) in cases {
        let barrier = tsgo(&out, extra, false);
        let early = tsgo(&out, extra, true);
        assert_eq!(
            barrier.status,
            Some(0),
            "{case}: the fixture must compile without diagnostics, so the check is sent: {}",
            barrier.stdout
        );
        assert!(
            barrier.files.contains_key("tsconfig.tsbuildinfo")
                && barrier
                    .files
                    .keys()
                    .any(|name| name.ends_with(".js") || name.ends_with(".d.ts")),
            "{case}: the run must write outputs and build info: {:?}",
            barrier.files.keys()
        );
        assert_eq!(early, barrier, "{case}: the early emit against the barrier");
    }
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
}

#[test]
fn rules_keep_the_barrier_when_a_check_could_see_the_outputs() {
    let out_dir = std::env::temp_dir()
        .join("goport-early-emit-rules")
        .to_string_lossy()
        .into_owned();
    // As in `early_emit_writes_what_the_barrier_writes`.
    let out = out_dir.clone();
    assert!(
        can_start(move |options| options.out_dir = out),
        "the fixture with a temp outDir must start its emit with the check"
    );

    // F1: `index.ts` imports "./shapes" without an extension.
    assert!(!can_start(|options| {
        options.module = ModuleKind::NODE_NEXT;
        options.module_resolution = ModuleResolutionKind::NODE_NEXT;
    }));
    // F2: the program files are inside the outDir or declarationDir.
    assert!(!can_start_with(RULES_CONFIG, |options| {
        options.out_dir = format!("{FIXTURE}/src");
    }));
    assert!(!can_start_with(RULES_CONFIG, |options| {
        options.declaration_dir = FIXTURE.to_string();
    }));
    // F3: an output directory under `node_modules`.
    let under_node_modules = format!("{out_dir}/node_modules/out");
    assert!(!can_start(move |options| {
        options.out_dir = under_node_modules;
    }));
    // F4 and the option rules.
    assert!(!can_start(|options| {
        options.preserve_symlinks = Tristate::True;
    }));
    assert!(!can_start(|options| {
        options.no_emit_on_error = Tristate::True;
    }));
    assert!(!can_start(|options| {
        options.single_threaded = Tristate::True;
    }));
}

/// Loads the fixture with `edit` applied to its options and returns
/// `emit_can_start_with_check` for it.
fn can_start(edit: impl FnOnce(&mut CompilerOptions)) -> bool {
    can_start_with(CONFIG, edit)
}

/// `can_start` with the fixture config `config`.
fn can_start_with(config: &str, edit: impl FnOnce(&mut CompilerOptions)) -> bool {
    let program = try_load_version(config, edit)
        .unwrap_or_else(|error| panic!("cannot load {config}: {error}"));
    let can_start = {
        let _scope = enter_program(Some(program));
        emit_can_start_with_check()
    };
    release_program(program);
    can_start
}

/// Runs `tsgo -p` on the fixture as an incremental program, with `out` as
/// the out dir and the build info in it, and `extra` arguments. `early`
/// false sets `GOPORT_EARLY_EMIT=0`. It removes `out` first and returns what
/// the run wrote there and printed.
fn tsgo(out: &Path, extra: &[&str], early: bool) -> Run {
    if out.exists() {
        fs::remove_dir_all(out).unwrap_or_else(|error| panic!("remove {}: {error}", out.display()));
    }
    let output = Command::new(env!("CARGO_BIN_EXE_tsgo"))
        .args(["-p", CONFIG, "--incremental", "--outDir"])
        .arg(out)
        .arg("--tsBuildInfoFile")
        .arg(out.join("tsconfig.tsbuildinfo"))
        .args(["--listEmittedFiles", "--pretty", "false"])
        .args(extra)
        .env("GOPORT_EMIT_THREADS", "2")
        .env("GOPORT_EARLY_EMIT", if early { "1" } else { "0" })
        .output()
        .expect("run tsgo");
    let mut files = BTreeMap::new();
    if out.exists() {
        read_files(out, out, &mut files);
    }
    Run {
        files,
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        status: output.status.code(),
    }
}

/// Reads every file under `dir` into `files`, by path relative to `root`.
fn read_files(root: &Path, dir: &Path, files: &mut BTreeMap<String, Vec<u8>>) {
    for entry in fs::read_dir(dir).unwrap_or_else(|error| panic!("read {}: {error}", dir.display()))
    {
        let path = entry.expect("out dir entry").path();
        if path.is_dir() {
            read_files(root, &path, files);
        } else {
            let name = path
                .strip_prefix(root)
                .expect("a path under the out dir")
                .to_string_lossy()
                .into_owned();
            let bytes =
                fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
            files.insert(name, bytes);
        }
    }
}

/// A new directory under the system temp dir, by its real path (the
/// program sees real paths).
fn scratch_dir() -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after 1970")
        .as_nanos();
    let dir =
        std::env::temp_dir().join(format!("goport-early-emit-{}-{nanos}", std::process::id()));
    fs::create_dir(&dir).unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
    fs::canonicalize(&dir).expect("canonical scratch dir")
}
