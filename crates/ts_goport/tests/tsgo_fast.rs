//! Fast mode (`fast_mode.rs`, not in Go) from the command line. Without
//! `--fast` and `GOPORT_FAST=1`, tsgo keeps Go's 4 checkers and Go's eager
//! member tables. `--fast` and `GOPORT_FAST=1` change both, and `--fast`
//! gives the same output on every run. Each test runs `tsgo` in a new
//! scratch dir with no fast-mode variable set, except the ones that the
//! test sets. A passing test deletes its dir.

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
    let mut command = Command::new(env!("CARGO_BIN_EXE_tsgo"));
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

/// The checker count and the `Symbols` count of a run with
/// `--generateTrace <trace> --extendedDiagnostics`: the trace has one
/// `types_<n>.json` per checker.
fn checkers_and_symbols(dir: &Path, trace: &str, output: &Output) -> (usize, u64) {
    assert_eq!(output.status.code(), Some(0), "{}", stdout(output));
    let checkers = fs::read_dir(dir.join(trace))
        .unwrap()
        .filter(|entry| {
            let name = entry.as_ref().unwrap().file_name();
            name.to_string_lossy().starts_with("types_")
        })
        .count();
    let text = stdout(output);
    let symbols = text
        .lines()
        .find_map(|line| line.strip_prefix("Symbols:"))
        .unwrap_or_else(|| panic!("no Symbols line in {text}"))
        .trim()
        .parse()
        .unwrap();
    (checkers, symbols)
}

/// The default path: Go's 4 checkers on 201 source files, and the same
/// `Symbols` count as with the fast parts set off. `--fast` and
/// `GOPORT_FAST=1` start one checker per core, up to 16 and at most one per
/// 32 source files (7), but never fewer than 4. At 4 checkers, `--fast`
/// makes fewer symbols (lazy members). Each checker makes its own symbols,
/// so only runs with the same count compare `Symbols`.
#[test]
fn fast_mode_is_off_by_default() {
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
    let dir = scratch("off", &files);
    let run = |trace: &str, flag: &[&str], vars: &[(&str, &str)]| {
        let mut args = vec!["--extendedDiagnostics", "--generateTrace", trace];
        args.extend_from_slice(flag);
        let output = tsgo(&dir, &args, vars);
        checkers_and_symbols(&dir, trace, &output)
    };
    let parts_off = [
        ("GOPORT_LAZY_MEMBERS", "0"),
        ("GOPORT_FAST_NEVER_ORDER", "0"),
    ];

    let (checkers, symbols) = run("default", &[], &[]);
    assert_eq!(checkers, 4);
    assert_eq!(run("parts-off", &[], &parts_off), (4, symbols));

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

/// Go's output for the `same_output_on_every_run` project, at every
/// checker count from 1 to 4 (tsgo-oracle-fed0bf24149f; exit code 2).
const SAME_OUTPUT_GO: &str = r#"b.ts(1,14): error TS2322: Type '"w"' is not assignable to type '"x" | "y" | "z"'.
d.ts(1,14): error TS2322: Type '"v"' is not assignable to type '"x" | "y" | "z"'.
e.ts(5,14): error TS2322: Type 'string' is not assignable to type 'number'.
f.ts(2,14): error TS2322: Type '"z"' is not assignable to type '"a" | "b"'.
"#;

/// `--fast --checkers 2` on 6 files gives Go's output in each of 5 runs:
/// each file goes to the checker of Go's split, so no run differs.
#[test]
fn same_output_on_every_run() {
    let files: Vec<(String, String)> = [
        ("a.ts", r#"export const order = ["z", "y", "x"] as const;"#),
        ("b.ts", r#"export const pick: "x" | "y" | "z" = "w";"#),
        ("c.ts", r#"export const other = ["x", "y"] as const;"#),
        ("d.ts", r#"export const again: "z" | "x" | "y" = "v";"#),
        (
            "e.ts",
            "export class Box<T> {
  value!: T;
  map<U>(fn: (value: T) => U): Box<U> { return new Box<U>(); }
}
export const n: number = new Box<string>().map((s) => s).value;",
        ),
        (
            "f.ts",
            r#"import { order } from "./a";
export const first: "a" | "b" = order[0];"#,
        ),
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "noEmit": true, "strict": true, "types": [], "lib": ["es2015"] }, "files": ["a.ts", "b.ts", "c.ts", "d.ts", "e.ts", "f.ts"] }"#,
        ),
    ]
    .iter()
    .map(|(file, text)| ((*file).to_string(), format!("{text}\n")))
    .collect();
    let dir = scratch("same", &files);
    for run in 0..5 {
        let output = tsgo(&dir, &["--fast", "--checkers", "2"], &[]);
        assert_eq!(stdout(&output), SAME_OUTPUT_GO, "run {run}");
        assert_eq!(output.status.code(), Some(2), "run {run}");
    }
    fs::remove_dir_all(&dir).unwrap();
}
