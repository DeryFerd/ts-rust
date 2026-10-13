//! The stat cache of a parallel load (`files_parser.rs` `SharedStatCache`,
//! `LoaderStatFs`) must answer as Go's file system. One stat answers
//! `FileExists` and `DirectoryExists` of an OS path (Go `vfs.Common` answers
//! each with a stat of its own), but not of a bundled path: Go
//! `Stat("bundled:///")` is a directory while
//! `DirectoryExists("bundled:///")` is false (bundled/embed.go:66 and :85).
//! statcut1 round 1 answered `bundled:///` from the stat, so a parallel
//! load saw a directory there and the single-threaded load did not.
//!
//! Each test runs `tsgo -p tsconfig.json --traceResolution` in a new
//! scratch dir in the default mode, with 4 parse workers
//! (`GOPORT_PARSE_THREADS=4`, so a small machine runs them too) and with
//! `--singleThreaded`. Each run must give the result of Go N prime
//! (tsgo-oracle-fed0bf24149f) on the same files. A passing test deletes its
//! dir.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// One run of a test: the extra arguments and variables.
type Mode = (
    &'static [&'static str],
    &'static [(&'static str, &'static str)],
);

/// The runs of each test.
const MODES: [Mode; 3] = [
    (&[], &[]),
    (&[], &[("GOPORT_PARSE_THREADS", "4")]),
    (&["--singleThreaded"], &[]),
];

/// Writes `files` to a new scratch dir, runs `tsgo -p tsconfig.json
/// --traceResolution` there in each of `MODES`, and returns the dir and,
/// per mode, the exit code and the output (stdout, then stderr).
fn runs(name: &str, files: &[(&str, &str)]) -> (PathBuf, Vec<(Option<i32>, String)>) {
    let dir = std::env::temp_dir().join(format!("stat_cache_{}_{name}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    for (file, text) in files {
        fs::write(dir.join(file), text).unwrap();
    }
    let runs = MODES
        .iter()
        .map(|(args, vars)| {
            let out = Command::new(env!("CARGO_BIN_EXE_tsgo"))
                .args(["-p", "tsconfig.json", "--traceResolution"])
                .args(*args)
                .env_remove("GOPORT_PARSE_THREADS")
                .envs(vars.iter().copied())
                .current_dir(&dir)
                .output()
                .unwrap();
            let mut text = String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n");
            text.push_str(&String::from_utf8_lossy(&out.stderr));
            (out.status.code(), text)
        })
        .collect();
    (dir, runs)
}

/// Skeptic repro 1: with `typeRoots` at the bundled root, Go finds no type
/// root there (no directory), so `types: ["*"]` adds no type reference. The
/// parallel load of round 1 enumerated it and reported TS2688 for `libs`.
#[test]
fn type_roots_at_the_bundled_root() {
    let (dir, runs) = runs(
        "type_roots",
        &[
            (
                "tsconfig.json",
                r#"{ "compilerOptions": { "typeRoots": ["bundled:///"], "types": ["*"], "noEmit": true }, "files": ["a.ts"] }"#,
            ),
            ("a.ts", "export const x: number = 1;\n"),
        ],
    );
    for ((args, vars), run) in MODES.iter().zip(&runs) {
        assert_eq!(
            run,
            &(Some(0), String::new()),
            "{args:?} {vars:?}: kept {}",
            dir.display()
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

/// Skeptic repro 2: a `paths` substitution to the bundled root. Go skips
/// the lookups in it (no directory). The parallel load of round 1 looked
/// for its package.json and index files. The other trace lines name the
/// scratch dir and its parents, so only the lines of the bundled root and
/// the errors are compared.
#[test]
fn paths_to_the_bundled_root() {
    let (dir, runs) = runs(
        "paths",
        &[
            (
                "tsconfig.json",
                r#"{ "compilerOptions": { "paths": { "x": ["bundled:///"] }, "noEmit": true }, "files": ["a.ts"] }"#,
            ),
            ("a.ts", "import * as x from \"x\"; export const y = x;\n"),
        ],
    );
    let go = "\
Trying substitution 'bundled:///', candidate module location: 'bundled:///'.
Loading module as file / folder, candidate module location 'bundled:///', target file types: TypeScript, JavaScript, Declaration, JSON.
Directory 'bundled:///' does not exist, skipping all lookups in it.
a.ts(1,20): error TS2307: Cannot find module 'x' or its corresponding type declarations.
";
    for ((args, vars), (code, text)) in MODES.iter().zip(&runs) {
        let lines: String = text
            .lines()
            .filter(|line| line.contains("bundled:///") || line.contains("error TS"))
            .flat_map(|line| [line, "\n"])
            .collect();
        assert_eq!(
            (*code, lines.as_str()),
            (Some(2), go),
            "{args:?} {vars:?}: kept {}",
            dir.display()
        );
    }
    let _ = fs::remove_dir_all(&dir);
}
