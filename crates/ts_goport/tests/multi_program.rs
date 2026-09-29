//! Multi-program checks for `goport_multiprog pair` and
//! `goport_live_programs`.
//!
//! The `pair` tests copy `fixtures/multiprog/basic` to a new directory under
//! the system temp dir and run `goport_multiprog pair` there. Program A is
//! the original project. Program B is the project after one edit of
//! `src/a.ts`. Each report must be byte-identical to a fresh
//! `goport -p tsconfig.json` on the same text, with the same exit code.
//!
//! The live tests hold several projects (`basic`, `emit`, `linked` and `cut`
//! under `fixtures/multiprog`) at once, as the language server does. Each
//! report must equal a fresh `goport` or `goport_emit` run of that project
//! alone.
//!
//! The watch test runs `tsc --watch` through `goport_watch` and edits
//! `src/a.ts` between builds.
//!
//! The build test runs `goport_build -b` on `fixtures/multiprog/build-dedup`,
//! whose projects share parsed files in one process, as Go `tsc -b` does.
//!
//! `pair` writes these files to its out dir: `a.txt`, `a.status`, `b.txt`,
//! `b.status`, `b.reused` and, with `--first`, `first.txt`. A status file
//! holds the decimal exit code. `b.reused` holds `true` or `false`.
//!
//! Each test uses its own directory and processes, so the tests can run in
//! parallel. A passing test deletes its directory. A failing test keeps it
//! and names it in the message.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use ts_goport::execute::tsc::EXIT_UNPORTED;

const FIXTURE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/multiprog/basic"
);

const EMIT_FIXTURE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/multiprog/emit");

const BUILD_DEDUP_FIXTURE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/multiprog/build-dedup"
);

/// The file that each test edits, relative to the project.
const CHANGED: &str = "src/a.ts";

/// The stdout text and exit code of one report.
#[derive(Debug, PartialEq)]
struct Report {
    stdout: String,
    status: i32,
}

/// The two reports of one `pair` run, and whether B reused A's files.
struct Pair {
    a: Report,
    b: Report,
    reused: bool,
}

#[test]
fn edit_that_keeps_imports_shares_files() {
    let pair = check_pair("keeps-imports", Some("edits/a.ts"), false);
    assert!(
        pair.reused,
        "an edit with the same imports must reuse the other files"
    );
    assert_new_c_error(&pair);
}

#[test]
fn edit_that_changes_imports_rebuilds() {
    let pair = check_pair("changes-imports", Some("edits/a-imports.ts"), false);
    assert!(
        !pair.reused,
        "an edit that adds an import must rebuild the program"
    );
    assert_new_c_error(&pair);
}

#[test]
fn no_op_edit_equals_first_program() {
    let pair = check_pair("no-op", None, false);
    assert_eq!(pair.b, pair.a, "the same text must give the same report");
}

#[test]
fn programs_after_an_unrelated_program() {
    let pair = check_pair("after-first", Some("edits/a.ts"), true);
    assert!(
        pair.reused,
        "an edit with the same imports must reuse the other files"
    );
    assert_new_c_error(&pair);
}

/// lsshells M3b. `GOPORT_FREE_FILE_VERSIONS=1` turns freeing on in
/// `goport_multiprog` (a CLI process, where it is off by default).
const FREE_FILE_VERSIONS: &[(&str, &str)] = &[("GOPORT_FREE_FILE_VERSIONS", "1")];

/// lsshells M3b: with freeing on, each new parse of B is a freeable file
/// version (its store and `GoFile` belong to the version, not to a leaked
/// tier 1 publish), and `goport_multiprog` checks that. A and B still report
/// like fresh runs, for an edit that keeps the imports (only the changed
/// file is new) and for one that adds an import (every file is new).
// PORT: no Go counterpart.
#[test]
fn freeable_file_versions_report_like_fresh_runs() {
    let pair = check_pair_with_env(
        "free-keeps-imports",
        Some("edits/a.ts"),
        false,
        FREE_FILE_VERSIONS,
    );
    assert!(
        pair.reused,
        "an edit with the same imports must reuse the other files"
    );
    assert_new_c_error(&pair);
    let pair = check_pair_with_env(
        "free-changes-imports",
        Some("edits/a-imports.ts"),
        false,
        FREE_FILE_VERSIONS,
    );
    assert!(
        !pair.reused,
        "an edit that adds an import must rebuild the program"
    );
    assert_new_c_error(&pair);
}

/// lsshells M3b: `goport_multiprog cycles` with freeing on frees every
/// freeable file version once no program has it: after the last release,
/// each version it made is dead. Each report equals the report of the last
/// version with the same text (`cycles` checks it). A CLI process with the
/// flag unset makes no file version and frees nothing.
// PORT: no Go counterpart.
#[test]
fn cycles_free_file_versions_only_when_the_flag_is_on() {
    const CYCLES: usize = 4;
    let (made, dead) = run_cycles("cycles-default", CYCLES, &[]);
    assert_eq!((made, dead), (0, 0), "a CLI process makes no file version");
    let (made, dead) = run_cycles("cycles-free", CYCLES, FREE_FILE_VERSIONS);
    assert!(
        made >= CYCLES,
        "each cycle parses the changed file again, so it makes a file version (made {made})"
    );
    assert_eq!(
        dead, made,
        "a file version outlives every program that had it (a missed holder)"
    );
}

/// Runs `goport_multiprog cycles` `count` times on a new copy of the fixture
/// with `env` set, and gives the numbers of its last line,
/// `file_versions made=<n> dead=<m>`. `GOPORT_FREE_FILE_VERSIONS` is unset
/// unless `env` sets it, so the test environment does not change the
/// default.
fn run_cycles(test: &str, count: usize, env: &[(&str, &str)]) -> (usize, usize) {
    let root = scratch_dir(test);
    let project = root.join("project");
    copy_dir(Path::new(FIXTURE), &project);
    let changed = project.join(CHANGED);
    let original = read(&changed);
    let run = Command::new(env!("CARGO_BIN_EXE_goport_multiprog"))
        .arg("cycles")
        .arg("tsconfig.json")
        .arg(&changed)
        .arg(count.to_string())
        .env_remove("GOPORT_FREE_FILE_VERSIONS")
        .envs(env.iter().copied())
        .current_dir(&project)
        .output()
        .expect("run goport_multiprog");
    let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
    assert!(
        run.status.success(),
        "goport_multiprog cycles failed ({}) in {}:\n{stdout}\n{}",
        run.status,
        root.display(),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(read(&changed), original, "cycles must restore {CHANGED}");
    let counts = stdout
        .lines()
        .last()
        .and_then(|line| line.strip_prefix("file_versions made="))
        .and_then(|rest| rest.split_once(" dead="))
        .and_then(|(made, dead)| Some((made.parse().ok()?, dead.parse().ok()?)))
        .unwrap_or_else(|| panic!("no file_versions line in the cycles output:\n{stdout}"));
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
    counts
}

/// The projects of the live tests: the fixture dir, the
/// `goport_live_programs` mode and a line that its `checker.txt` must hold.
/// The `emit` and `linked` lines are `import(...)` types, so the checkers
/// on the shared thread make module specifiers. The `linked` one needs the
/// symlink cache of its own program (see `link_shelf`).
const LIVE_PROJECTS: [(&str, &str, &str); 3] = [
    ("basic", "check", "side: \"left\" | \"right\""),
    ("emit", "emit", "b: import(\"./shapes\").Box"),
    ("linked", "emit", "second: import(\"shelf\").Book"),
];

/// Three live projects, loaded in both orders: `basic` checked like
/// `goport`, `emit` and `linked` compiled like `goport_emit`. Each report
/// and output equals a fresh run of that project alone. The checkers of all
/// programs share the loading thread (`checker.txt`, see
/// `goport_live_programs`), and what they write does not depend on the load
/// order or the other programs.
#[cfg(unix)]
#[test]
fn three_live_projects_report_like_fresh_runs() {
    let root = scratch_dir("live");
    let fixtures = Path::new(FIXTURE).parent().expect("fixture root");
    for (dir, _, _) in LIVE_PROJECTS {
        copy_dir(&fixtures.join(dir), &root.join(dir));
    }
    link_shelf(&root.join("linked"));
    let projects: Vec<String> = LIVE_PROJECTS
        .iter()
        .map(|(dir, mode, _)| format!("{mode}:{dir}/tsconfig.json"))
        .collect();
    let mut args = vec!["live", "out-1"];
    args.extend(projects.iter().map(String::as_str));
    run_live_programs(&root, &args);
    let mut args = vec!["live", "out-2"];
    args.extend(projects.iter().rev().map(String::as_str));
    run_live_programs(&root, &args);

    let last = LIVE_PROJECTS.len() - 1;
    for (i, (dir, mode, line)) in LIVE_PROJECTS.into_iter().enumerate() {
        let config = format!("{dir}/tsconfig.json");
        let fresh_dir = format!("fresh-{dir}");
        let (fresh, fresh_outputs) = if mode == "check" {
            (goport(&root, Path::new(&config)), None)
        } else {
            let fresh = goport_emit(&root, &config, &fresh_dir);
            (fresh, Some(read_tree(&root.join(&fresh_dir))))
        };
        let mut texts = Vec::new();
        for (out, index) in [("out-1", i), ("out-2", last - i)] {
            let program = root.join(out).join(index.to_string());
            assert_eq!(
                read_live_report(&program),
                fresh,
                "{out} {dir}: report against a fresh run ({})",
                root.display()
            );
            if let Some(fresh_outputs) = &fresh_outputs {
                assert_eq!(
                    read_tree(&program.join("out")),
                    *fresh_outputs,
                    "{out} {dir}: outputs against goport_emit ({})",
                    root.display()
                );
            }
            texts.push(read(&program.join("checker.txt")));
        }
        assert_eq!(
            texts[0],
            texts[1],
            "{dir}: checker text depends on the load order ({})",
            root.display()
        );
        assert!(
            texts[0].lines().any(|text| text == line),
            "{dir}: checker text has no line {line:?}:\n{}",
            texts[0]
        );
    }
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
}

/// A type longer than Go's limit is cut inside a 2-byte char (the `cut`
/// fixture), in a live program next to another one. Go `typeToStringEx`
/// keeps the first 317 bytes and adds "...", so the type line in
/// `checker.txt` ends with the first byte of the char. Go
/// `diagnostics.Format` turns that byte into U+FFFD in the error message.
/// Pinned tsgo prints the same message.
#[test]
fn type_cut_inside_a_char_keeps_go_bytes() {
    let root = scratch_dir("cut");
    let fixtures = Path::new(FIXTURE).parent().expect("fixture root");
    for dir in ["basic", "cut"] {
        copy_dir(&fixtures.join(dir), &root.join(dir));
    }
    run_live_programs(
        &root,
        &[
            "live",
            "out",
            "check:basic/tsconfig.json",
            "check:cut/tsconfig.json",
        ],
    );
    let program = root.join("out").join("1");

    let source = read(&root.join("cut/src/word.ts"));
    let word = source
        .split('"')
        .find(|text| text.starts_with('x') && text.len() > 320)
        .expect("the fixture declares a long word");
    let literal = format!("\"{word}\"");
    let cut = &literal.as_bytes()[..317];
    assert!(
        std::str::from_utf8(cut).is_err(),
        "byte 317 of the fixture type must be inside a char"
    );

    let line = [b"word: ", cut, b"..."].concat();
    let checker = fs::read(program.join("checker.txt")).expect("read checker.txt");
    assert!(
        checker.split(|&b| b == b'\n').any(|text| text == line),
        "checker.txt has no line {:?} ({})",
        String::from_utf8_lossy(&line),
        root.display()
    );

    let report = read_live_report(&program);
    assert_eq!(
        report,
        goport(&root, Path::new("cut/tsconfig.json")),
        "report against a fresh run ({})",
        root.display()
    );
    let message = format!(
        "Type '{}...' is not assignable to type '\"x\"'.",
        String::from_utf8_lossy(cut)
    );
    assert!(
        report.stdout.contains(&message),
        "the report has no message {message:?}:\n{}",
        report.stdout
    );
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
}

/// Links `node_modules/shelf` to `packages/shelf` in a copy of the `linked`
/// fixture, as a workspace package manager does. The program resolves
/// `shelf` through the link and keeps it in its symlink cache.
#[cfg(unix)]
fn link_shelf(project: &Path) {
    let modules = project.join("node_modules");
    fs::create_dir(&modules)
        .unwrap_or_else(|error| panic!("create {}: {error}", modules.display()));
    std::os::unix::fs::symlink("../packages/shelf", modules.join("shelf"))
        .unwrap_or_else(|error| panic!("link shelf in {}: {error}", project.display()));
}

/// A program is released (its checker workers joined) while a job of another
/// program waits on that program's pool. Both still report like fresh runs.
#[test]
fn release_while_another_program_checks_on_the_pool() {
    let root = scratch_dir("release");
    copy_dir(Path::new(FIXTURE), &root.join("p"));
    copy_dir(Path::new(EMIT_FIXTURE), &root.join("q"));
    run_live_programs(
        &root,
        &["release", "out", "p/tsconfig.json", "q/tsconfig.json"],
    );
    let out = root.join("out");
    for name in ["p", "q"] {
        let config = format!("{name}/tsconfig.json");
        assert_eq!(
            read_report(&out, name),
            goport(&root, Path::new(&config)),
            "{name} against goport ({})",
            root.display()
        );
    }
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
}

/// `tsc --watch` makes a program version per build (`goport_watch`). After
/// each edit of `src/a.ts`, the errors of the build equal a fresh `goport`
/// run on the same text. The first edit gives the unchanged `c.ts` an error,
/// so the build sees the edit through a file it shares with the last build.
#[test]
fn watch_builds_report_like_fresh_runs() {
    let root = scratch_dir("watch");
    let project = root.join("project");
    copy_dir(Path::new(FIXTURE), &project);
    let changed = project.join(CHANGED);
    let original = read(&changed);
    let original_file = root.join("original.ts");
    write(&original_file, &original);
    let edits = [
        project.join("edits/a.ts"),
        project.join("edits/a-imports.ts"),
        original_file,
    ];
    let out = root.join("watch.txt");
    let run = Command::new(env!("CARGO_BIN_EXE_goport_watch"))
        .arg(&out)
        .arg(CHANGED)
        .args(&edits)
        .args(["--", "--watch", "-p", "tsconfig.json", "--noEmit"])
        .current_dir(&project)
        .output()
        .expect("run goport_watch");
    assert!(
        run.status.success(),
        "goport_watch failed ({}) in {}:\n{}",
        run.status,
        root.display(),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        read(&changed),
        original,
        "goport_watch must restore {CHANGED}"
    );

    let watch = read(&out);
    let builds: Vec<&str> = watch
        .split_inclusive("Watching for file changes.")
        .filter(|build| build.contains("Watching for file changes."))
        .collect();
    assert_eq!(
        builds.len(),
        4,
        "one build per edit after the first:\n{watch}"
    );
    let texts = [original.clone(), read(&edits[0]), read(&edits[1]), original];
    for (i, (build, text)) in builds.iter().zip(&texts).enumerate() {
        write(&changed, text);
        let fresh = goport(&project, Path::new("tsconfig.json"));
        assert_eq!(
            error_lines(build),
            error_lines(&fresh.stdout),
            "build {i} against goport ({})",
            root.display()
        );
        assert_eq!(
            build.contains("src/c.ts("),
            i == 1 || i == 2,
            "build {i}: c.ts error:\n{build}"
        );
    }
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
}

/// `goport_build -b` makes the program of each project in one process, and
/// the build host shares parsed `.d.ts` files between them. `p1` imports
/// `a` and `b`, so the copy of `a` under `b/node_modules` is a duplicate
/// package: `p1` parses it and its `dep.d.ts` and leaves both out. `p2`
/// imports only `b`, so both are program files of `p2`. `expected.txt` is
/// the pinned tsgo output of the same command.
#[test]
fn build_includes_files_that_an_earlier_project_left_out() {
    let root = scratch_dir("build-dedup");
    copy_dir(Path::new(BUILD_DEDUP_FIXTURE), &root);
    let run = Command::new(env!("CARGO_BIN_EXE_goport_build"))
        .args(["-b", "tsconfig.json", "--explainFiles", "--pretty", "false"])
        .current_dir(&root)
        .output()
        .expect("run goport_build");
    let report = Report {
        stdout: String::from_utf8(run.stdout).expect("goport_build stdout is UTF-8"),
        status: run.status.code().expect("goport_build exited with a code"),
    };
    let expected = Report {
        stdout: read(&root.join("expected.txt")),
        status: 0,
    };
    assert_eq!(
        report,
        expected,
        "goport_build against tsgo ({}):\n{}",
        root.display(),
        String::from_utf8_lossy(&run.stderr)
    );
    for project in ["p1", "p2"] {
        let build_info = root.join(project).join("tsconfig.tsbuildinfo");
        assert!(build_info.is_file(), "no {}", build_info.display());
    }
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
}

/// The diagnostic lines of a tsc report.
fn error_lines(report: &str) -> Vec<&str> {
    report
        .lines()
        .filter(|line| line.contains("): error TS"))
        .collect()
}

/// Runs `goport_live_programs` with `cwd` as the current directory and
/// fails the test when it fails.
fn run_live_programs(cwd: &Path, args: &[&str]) {
    let run = Command::new(env!("CARGO_BIN_EXE_goport_live_programs"))
        .args(args)
        .current_dir(cwd)
        .output()
        .expect("run goport_live_programs");
    assert!(
        run.status.success(),
        "goport_live_programs {args:?} failed ({}) in {}:\n{}",
        run.status,
        cwd.display(),
        String::from_utf8_lossy(&run.stderr)
    );
}

/// Runs a fresh `goport_emit -p <config> --outDir <out_dir>` in `cwd`.
fn goport_emit(cwd: &Path, config: &str, out_dir: &str) -> Report {
    let run = Command::new(env!("CARGO_BIN_EXE_goport_emit"))
        .args(["-p", config, "--outDir", out_dir])
        .current_dir(cwd)
        .output()
        .expect("run goport_emit");
    let status = run.status.code().expect("goport_emit exited with a code");
    assert_ne!(
        status,
        EXIT_UNPORTED,
        "goport_emit hit unported code in {}:\n{}",
        cwd.display(),
        String::from_utf8_lossy(&run.stderr)
    );
    Report {
        stdout: String::from_utf8(run.stdout).expect("goport_emit stdout is UTF-8"),
        status,
    }
}

/// Reads `report.txt` and `status` of one `live` program dir.
fn read_live_report(dir: &Path) -> Report {
    let status = read(&dir.join("status"));
    Report {
        stdout: read(&dir.join("report.txt")),
        status: status
            .trim()
            .parse()
            .unwrap_or_else(|_| panic!("{} must hold an exit code", dir.display())),
    }
}

/// The files under `dir` by path relative to `dir`, with their text.
fn read_tree(dir: &Path) -> BTreeMap<String, String> {
    let mut files = BTreeMap::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(current) = pending.pop() {
        for entry in fs::read_dir(&current).unwrap_or_else(|error| {
            panic!("read {}: {error}", current.display());
        }) {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                pending.push(path);
            } else {
                let name = path
                    .strip_prefix(dir)
                    .expect("a path under the dir")
                    .to_string_lossy()
                    .into_owned();
                files.insert(name, read(&path));
            }
        }
    }
    files
}

/// Runs `pair` on a new copy of the fixture and checks each report against a
/// fresh `goport`. `edit` is the fixture file whose text replaces `src/a.ts`.
/// `None` writes the original text again. With `with_first`, `pair` first
/// loads, reports and releases a second copy, so A and B are not the first
/// program of the process.
fn check_pair(test: &str, edit: Option<&str>, with_first: bool) -> Pair {
    check_pair_with_env(test, edit, with_first, &[])
}

/// `check_pair` with `env` set for `goport_multiprog` (not for the fresh
/// `goport` runs).
fn check_pair_with_env(
    test: &str,
    edit: Option<&str>,
    with_first: bool,
    env: &[(&str, &str)],
) -> Pair {
    let root = scratch_dir(test);
    let project = root.join("project");
    copy_dir(Path::new(FIXTURE), &project);
    let changed = project.join(CHANGED);
    let original = read(&changed);
    let new_text = edit.map_or_else(|| original.clone(), |edit| read(&project.join(edit)));
    let new_text_file = root.join("new-text.ts");
    write(&new_text_file, &new_text);
    let out = root.join("out");
    fs::create_dir(&out).unwrap_or_else(|error| panic!("create {}: {error}", out.display()));

    let fresh_a = goport(&project, Path::new("tsconfig.json"));

    let mut args: Vec<OsString> = vec![
        "pair".into(),
        "tsconfig.json".into(),
        changed.clone().into(),
        new_text_file.into(),
        out.clone().into(),
    ];
    let first_config = with_first.then(|| {
        let other = root.join("other");
        copy_dir(Path::new(FIXTURE), &other);
        other.join("tsconfig.json")
    });
    if let Some(config) = &first_config {
        args.push("--first".into());
        args.push(config.into());
    }
    let run = Command::new(env!("CARGO_BIN_EXE_goport_multiprog"))
        .args(&args)
        .envs(env.iter().copied())
        .current_dir(&project)
        .output()
        .expect("run goport_multiprog");
    assert!(
        run.status.success(),
        "goport_multiprog pair failed ({}) in {}:\n{}",
        run.status,
        root.display(),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(read(&changed), original, "pair must restore {CHANGED}");

    let a = read_report(&out, "a");
    assert_eq!(
        a,
        fresh_a,
        "a.txt against goport on the original ({})",
        root.display()
    );

    write(&changed, &new_text);
    let fresh_b = goport(&project, Path::new("tsconfig.json"));
    let b = read_report(&out, "b");
    assert_eq!(
        b,
        fresh_b,
        "b.txt against goport on the edited text ({})",
        root.display()
    );

    if let Some(config) = &first_config {
        assert_eq!(
            read(&out.join("first.txt")),
            goport(&project, config).stdout,
            "first.txt against goport on the other copy ({})",
            root.display()
        );
    }

    let reused = match read(&out.join("b.reused")).trim() {
        "true" => true,
        "false" => false,
        other => panic!("b.reused must be true or false, not {other:?}"),
    };
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
    Pair { a, b, reused }
}

/// Both edits make `Point.y` a string, so the unchanged `c.ts` has an error
/// in B only. This makes sure the edit is visible in the reports.
fn assert_new_c_error(pair: &Pair) {
    assert!(
        !pair.a.stdout.contains("src/c.ts("),
        "c.ts must have no error before the edit:\n{}",
        pair.a.stdout
    );
    assert!(
        pair.b.stdout.contains("src/c.ts("),
        "c.ts must have an error after the edit:\n{}",
        pair.b.stdout
    );
}

/// Runs a fresh `goport -p <config>` with `cwd` as the current directory.
fn goport(cwd: &Path, config: &Path) -> Report {
    let run = Command::new(env!("CARGO_BIN_EXE_goport"))
        .arg("-p")
        .arg(config)
        .current_dir(cwd)
        .output()
        .expect("run goport");
    let status = run.status.code().expect("goport exited with a code");
    assert_ne!(
        status,
        EXIT_UNPORTED,
        "goport hit unported code in {}:\n{}",
        cwd.display(),
        String::from_utf8_lossy(&run.stderr)
    );
    Report {
        stdout: String::from_utf8(run.stdout).expect("goport stdout is UTF-8"),
        status,
    }
}

/// Reads `<name>.txt` and `<name>.status` from the `pair` out dir.
fn read_report(out: &Path, name: &str) -> Report {
    let status = read(&out.join(format!("{name}.status")));
    Report {
        stdout: read(&out.join(format!("{name}.txt"))),
        status: status
            .trim()
            .parse()
            .unwrap_or_else(|_| panic!("{name}.status must hold an exit code, not {status:?}")),
    }
}

/// Makes a new empty directory for one test run.
fn scratch_dir(test: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after 1970")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "goport-multiprog-{test}-{}-{nanos}",
        std::process::id()
    ));
    fs::create_dir(&dir).unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
    // The programs see the real current directory, so the paths given to
    // `pair` must use the real path too.
    fs::canonicalize(&dir).expect("canonical scratch dir")
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap_or_else(|error| panic!("create {}: {error}", to.display()));
    for entry in fs::read_dir(from).expect("read fixture dir") {
        let entry = entry.expect("fixture dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("fixture file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target)
                .unwrap_or_else(|error| panic!("copy to {}: {error}", target.display()));
        }
    }
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
}

fn write(path: &Path, text: &str) {
    fs::write(path, text).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
}
