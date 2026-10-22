//! Fast mode (`fast_mode.rs`, not in Go) from the command line. Without
//! `--fast` and `GOPORT_FAST=1`, tsgo keeps Go's 4 checkers and Go's eager
//! member tables. `--fast` and `GOPORT_FAST=1` change both, and `--fast`
//! gives the same output on every run. Each test runs `tsgo` in a new
//! scratch dir with no fast-mode variable set, except the ones that the
//! test sets. A passing test deletes its dir.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// The variables that turn fast mode or one of its parts on or off.
const FAST_VARS: &[&str] = &[
    "GOPORT_FAST",
    "GOPORT_FAST_ARENAS",
    "GOPORT_FAST_NEVER_ORDER",
    "GOPORT_FAST_SPLIT",
    "GOPORT_FAST_SPLIT_DEP",
    "GOPORT_FAST_STEAL",
    "GOPORT_LAZY_MEMBERS",
];

/// Writes `files` to a new scratch dir and returns it.
fn scratch(name: &str, files: &[(String, String)]) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tsgo_fast_{}_{name}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    for (file, text) in files {
        fs::write(dir.join(file), text).unwrap();
    }
    dir
}

/// Runs tsgo with `args` in `dir`, with only the fast-mode variables in
/// `vars`.
fn tsgo(dir: &Path, args: &[&str], vars: &[(&str, &str)]) -> Output {
    run_bin(env!("CARGO_BIN_EXE_tsgo"), dir, args, vars)
}

/// Runs the bin `exe` as `tsgo` does.
fn run_bin(exe: &str, dir: &Path, args: &[&str], vars: &[(&str, &str)]) -> Output {
    let mut command = Command::new(exe);
    command.args(args).current_dir(dir);
    for var in FAST_VARS {
        command.env_remove(var);
    }
    command.envs(vars.iter().copied()).output().unwrap()
}

/// stdout with `\n` line ends.
fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n")
}

/// A class with 8 members, of which the program reads 1 from an instance.
/// Lazy members make only that one, so `Symbols` goes down.
const BOX_TS: &str = "export class Box<T> {
  a!: T; b!: T; c!: T; d!: T; e!: T; f!: T; g!: T; h!: T;
}
export const first: string = new Box<string>().a;
";

/// The first `Symbols` count of a run with `--extendedDiagnostics` that
/// exits 0.
fn symbols(output: &Output) -> u64 {
    assert_eq!(output.status.code(), Some(0), "{}", stdout(output));
    let text = stdout(output);
    text.lines()
        .find_map(|line| line.strip_prefix("Symbols:"))
        .unwrap_or_else(|| panic!("no Symbols line in {text}"))
        .trim()
        .parse()
        .unwrap()
}

/// The checker count and the `Symbols` count of a run with
/// `--generateTrace <trace> --extendedDiagnostics`: the trace has one
/// `types_<n>.json` per checker.
fn checkers_and_symbols(dir: &Path, trace: &str, output: &Output) -> (usize, u64) {
    let symbols = symbols(output);
    let checkers = fs::read_dir(dir.join(trace))
        .unwrap()
        .filter(|entry| {
            let name = entry.as_ref().unwrap().file_name();
            name.to_string_lossy().starts_with("types_")
        })
        .count();
    (checkers, symbols)
}

/// The fast parts that change `Symbols`, set off.
const PARTS_OFF: &[(&str, &str)] = &[
    ("GOPORT_LAZY_MEMBERS", "0"),
    ("GOPORT_FAST_NEVER_ORDER", "0"),
];

/// 200 one-line files and `BOX_TS`: 201 source files, so fast mode starts
/// up to 7 checkers (one per 32 files).
fn project_201() -> Vec<(String, String)> {
    let mut files: Vec<(String, String)> = (0..200)
        .map(|i| {
            (
                format!("f{i}.ts"),
                format!("export const v{i}: number = {i};\n"),
            )
        })
        .collect();
    files.push(("box.ts".into(), BOX_TS.into()));
    files.push((
        "tsconfig.json".into(),
        r#"{ "compilerOptions": { "noEmit": true, "types": [], "lib": ["es2015"] }, "include": ["*.ts"] }"#.into(),
    ));
    files
}

/// The default path: Go's 4 checkers on 201 source files, and the same
/// `Symbols` count as with the fast parts set off. `--fast` and
/// `GOPORT_FAST=1` start one checker per core, up to 16 and at most one per
/// 32 source files (7), but never fewer than 4. At 4 checkers, `--fast`
/// makes fewer symbols (lazy members). Each checker makes its own symbols,
/// so only runs with the same count compare `Symbols`.
#[test]
fn fast_mode_is_off_by_default() {
    let dir = scratch("off", &project_201());
    let run = |trace: &str, flag: &[&str], vars: &[(&str, &str)]| {
        let mut args = vec!["--extendedDiagnostics", "--generateTrace", trace];
        args.extend_from_slice(flag);
        let output = tsgo(&dir, &args, vars);
        checkers_and_symbols(&dir, trace, &output)
    };
    let (checkers, symbols) = run("default", &[], &[]);
    assert_eq!(checkers, 4);
    assert_eq!(run("parts-off", &[], PARTS_OFF), (4, symbols));

    let cores = std::thread::available_parallelism().map_or(4, usize::from);
    let fast = run("flag", &["--fast"], &[]);
    // At most 16 and 7 (201 files / 32), at least 4.
    assert_eq!(fast.0, cores.clamp(4, 7));
    assert_eq!(run("env", &[], &[("GOPORT_FAST", "1")]), fast);
    let (checkers, lazy_symbols) = run("flag-4", &["--fast", "--checkers", "4"], &[]);
    assert_eq!(checkers, 4);
    assert!(lazy_symbols < symbols, "{lazy_symbols} < {symbols}");
    fs::remove_dir_all(&dir).unwrap();
}

/// `tsc -b` keeps Go's 4 checkers in fast mode (it can check several
/// projects at once), in the tsc bin and in `goport_build`. A build writes
/// no trace, so the test reads `Symbols` with the fast parts that change it
/// set off: each checker makes its own symbols, so the count shows in it.
/// Outside a build, fast mode starts up to 7 checkers on this project.
#[test]
fn build_keeps_four_checkers() {
    let dir = scratch("build", &project_201());
    let build = |exe: &str, flag: &[&str], vars: &[(&str, &str)]| {
        let mut args = vec!["-b", "--force", "--extendedDiagnostics"];
        args.extend_from_slice(flag);
        symbols(&run_bin(exe, &dir, &args, vars))
    };
    let tsc = env!("CARGO_BIN_EXE_tsgo");
    let goport_build = env!("CARGO_BIN_EXE_goport_build");
    let four = build(tsc, &[], &[]);
    assert_ne!(build(tsc, &["--checkers", "7"], &[]), four);
    let fast_env = [PARTS_OFF, &[("GOPORT_FAST", "1")]].concat();
    for exe in [tsc, goport_build] {
        assert_eq!(build(exe, &[], &[]), four, "{exe}");
        assert_eq!(build(exe, &["--fast"], PARTS_OFF), four, "{exe} --fast");
        assert_eq!(build(exe, &[], &fast_env), four, "{exe} GOPORT_FAST=1");
    }
    fs::remove_dir_all(&dir).unwrap();
}

/// `Rec<300>` instantiates too deep. A checker reports TS5114 at the first
/// reference to it that it checks and keeps the result, so a later file on
/// the same checker gets no error. Which of `f1.ts` to `f6.ts` report it
/// depends on which files share a checker.
const REC_TS: &str = r#"export type Rec<N extends number, A extends unknown[] = []> = A["length"] extends N ? A : [0, ...Rec<N, [...A, 0]>];"#;

/// The files that report TS5114 in Go's output for the
/// `same_output_on_every_run` project with `--checkers N`, for N from 1 to
/// 7 (tsgo-oracle-fed0bf24149f; exit code 2 at each count). No `--checkers`
/// is 4. Go's output is different at each count.
const SPLIT_GO: [&[u8]; 7] = [
    &[1],
    &[1, 5],
    &[1, 4],
    &[1, 2, 3],
    &[1, 2, 3, 4],
    &[1, 2, 3, 4, 5],
    &[1, 2, 3, 4, 5, 6],
];

/// Go's output for that project with `--checkers checkers`.
fn split_go(checkers: usize) -> String {
    let mut out = String::new();
    for i in SPLIT_GO[checkers - 1] {
        writeln!(
            out,
            "f{i}.ts(2,18): error TS5114: Instantiations of type 'Rec' appear infinitely circular."
        )
        .unwrap();
    }
    out
}

/// On a project whose output depends on which files share a checker,
/// `--fast` gives Go's `--checkers 4` output in each of 5 runs: with 7
/// source files its count is 4 on every machine (at most one checker per
/// 32 files, at least 4). `--fast --checkers N` gives Go's output for N in
/// each of 3 runs, for each other N from 2 to 7. The `--checkers 1` run
/// shows that the port's output also depends on the split.
///
/// `skipLibCheck` keeps the lib files out of the check work, so the
/// work-stealing pass (`GOPORT_FAST_STEAL=1`, not deterministic) would move
/// some of these files to another checker. tsgo gets no `GOPORT_FAST_STEAL`
/// of the caller (`run_bin`), so the result does not depend on it. Only the
/// last run sets it, without `--fast`: the steal pass is part of fast mode,
/// so the default keeps Go's split.
#[test]
fn same_output_on_every_run() {
    let mut files = vec![("deep.ts".to_string(), format!("{REC_TS}\n"))];
    files.extend((1..=6).map(|i| {
        (
            format!("f{i}.ts"),
            format!("import type {{ Rec }} from \"./deep\";\nexport type T{i} = Rec<300>;\n"),
        )
    }));
    files.push((
        "tsconfig.json".into(),
        r#"{ "compilerOptions": { "noEmit": true, "strict": true, "skipLibCheck": true, "types": [], "lib": ["es2015"] }, "files": ["deep.ts", "f1.ts", "f2.ts", "f3.ts", "f4.ts", "f5.ts", "f6.ts"] }"#.into(),
    ));
    let dir = scratch("same", &files);
    let check_with = |args: &[&str], vars: &[(&str, &str)], checkers: usize, label: &str| {
        let output = tsgo(&dir, args, vars);
        assert_eq!(stdout(&output), split_go(checkers), "{label}");
        assert_eq!(output.status.code(), Some(2), "{label}");
    };
    let check =
        |args: &[&str], checkers: usize, label: &str| check_with(args, &[], checkers, label);
    check(&["--checkers", "1"], 1, "--checkers 1");
    for run in 0..5 {
        check(&["--fast"], 4, &format!("--fast, run {run}"));
    }
    for checkers in [2, 3, 5, 6, 7] {
        let count = checkers.to_string();
        for run in 0..3 {
            let label = format!("--fast --checkers {checkers}, run {run}");
            check(&["--fast", "--checkers", &count], checkers, &label);
        }
    }
    let steal = [("GOPORT_FAST_STEAL", "1")];
    check_with(&[], &steal, 4, "GOPORT_FAST_STEAL=1 without --fast");
    fs::remove_dir_all(&dir).unwrap();
}
