//! Port-only tests of a `.tsbuildinfo` that is valid JSON with bad values
//! (portgaps1 N2, N4). Go N panics where it reads or prints them and exits
//! 2. The port hung on a negative diagnostic `pos` and exited 70 with Rust
//! panic text on the other values.
//!
//! PORT: no Go counterpart. Each test makes the build info with `tsgo -p .`
//! (the same bytes as Go N), changes one value and runs `tsgo -p .` and
//! `tsgo -b` again. The expected exit code, stdout and first stderr line are
//! Go N's (the pin N oracle). In `-b`, Go panics in a builder goroutine of
//! `sync.WaitGroup.Go`, so its line ends with ` [recovered, repanicked]`,
//! and the task output that it buffers is not written.
#![cfg(unix)]

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// The longest run. Without the fix, a negative `pos` spins forever.
const LIMIT: Duration = Duration::from_secs(60);

/// A new empty dir under the system temp dir; removed on drop.
struct TmpDir(PathBuf);

impl TmpDir {
    fn new(name: &str) -> TmpDir {
        let dir = std::env::temp_dir().join(format!("goport-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src"))
            .unwrap_or_else(|e| panic!("mkdir {}: {e}", dir.display()));
        TmpDir(dir)
    }

    fn write(&self, name: &str, text: &str) {
        std::fs::write(self.0.join(name), text).unwrap_or_else(|e| panic!("write {name}: {e}"));
    }
}

impl Drop for TmpDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// The result of one run: exit code, stdout and the first stderr line.
#[derive(Debug, PartialEq)]
struct Run {
    code: Option<i32>,
    stdout: String,
    panic: String,
}

/// Runs `tsgo` with `args` in `dir`, killed after `LIMIT`.
fn tsgo(dir: &Path, args: &[&str]) -> Run {
    let mut child = Command::new(env!("CARGO_BIN_EXE_tsgo"))
        .args(args)
        .current_dir(dir)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run tsgo");
    let start = Instant::now();
    while child.try_wait().expect("wait for tsgo").is_none() {
        if start.elapsed() > LIMIT {
            let _ = child.kill();
            let _ = child.wait();
            panic!("tsgo {args:?} did not end in {LIMIT:?}");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().expect("tsgo output");
    Run {
        code: output.status.code(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        panic: String::from_utf8_lossy(&output.stderr)
            .lines()
            .next()
            .unwrap_or("")
            .to_string(),
    }
}

/// Builds the project, replaces `from` (once) with `to` in its build info,
/// and checks `tsgo -p .` and `tsgo -b`: exit 2, Go's panic line, and
/// `p_stdout` (the text Go prints before the panic) in `-p`.
fn check(name: &str, from: &str, to: &str, p_stdout: &str, panic: &str) {
    let dir = TmpDir::new(&format!("build-info-{name}"));
    dir.write(
        "tsconfig.json",
        r#"{ "compilerOptions": { "outDir": "dist", "rootDir": "src", "incremental": true, "strict": true, "lib": ["es5"] }, "include": ["src"] }"#,
    );
    dir.write("src/a.ts", "export const a: number = 1;\n");
    dir.write(
        "src/b.ts",
        "import { a } from \"./a\"; export const b: string = a;\n",
    );
    let first = tsgo(&dir.0, &["-p", "."]);
    assert_eq!(first.code, Some(2), "first build: {first:?}");
    let build_info =
        std::fs::read_to_string(dir.0.join("tsconfig.tsbuildinfo")).expect("build info");
    assert_eq!(
        build_info.matches(from).count(),
        1,
        "{from:?} once in {build_info}"
    );
    let bad = build_info.replace(from, to);
    for (args, stdout, panic) in [
        (&["-p", "."][..], p_stdout, panic.to_string()),
        (&["-b"][..], "", format!("{panic} [recovered, repanicked]")),
    ] {
        dir.write("tsconfig.tsbuildinfo", &bad);
        let want = Run {
            code: Some(2),
            stdout: stdout.to_string(),
            panic: format!("panic: {panic}"),
        };
        assert_eq!(tsgo(&dir.0, args), want, "{name} {args:?}");
    }
}

// Go: scanner/scanner.go:2687 `lineMap[line]` with line -1.
#[test]
fn negative_diagnostic_pos_panics_index_out_of_range() {
    check(
        "neg-pos",
        r#""pos":38,"#,
        r#""pos":-1,"#,
        "",
        "runtime error: index out of range [-1]",
    );
}

// Go: scanner/scanner.go:2687 `text[lineMap[line]:pos]` past the text.
#[test]
fn diagnostic_pos_past_the_text_panics_slice_bounds_out_of_range() {
    check(
        "big-pos",
        r#""pos":38,"#,
        r#""pos":999,"#,
        "",
        "runtime error: slice bounds out of range [:999] with length 53",
    );
}

// Go: execute/incremental/buildinfotosnapshot.go:62 `t.filePaths[fileId-1]`.
#[test]
fn file_id_past_the_file_names_panics_index_out_of_range() {
    check(
        "big-id",
        r#""referencedMap":[[5,"#,
        r#""referencedMap":[[999,"#,
        "",
        "runtime error: index out of range [998] with length 5",
    );
}

// Go: execute/incremental/buildinfotosnapshot.go:62, a file id 0.
#[test]
fn file_id_zero_panics_index_out_of_range() {
    check(
        "zero-id",
        r#""semanticDiagnosticsPerFile":[[5,"#,
        r#""semanticDiagnosticsPerFile":[[0,"#,
        "",
        "runtime error: index out of range [-1]",
    );
}

// Go: diagnostics/diagnostics.go:38 `Category.Name`, when the diagnostic is
// printed (after its location).
#[test]
fn unhandled_category_panics_when_printed() {
    check(
        "bad-cat",
        r#""category":1,"#,
        r#""category":999,"#,
        "src/b.ts(1,39): ",
        "Unhandled diagnostic category",
    );
}

// Go: diagnostics/diagnostics.go:88 `Localize`, when the message is printed
// (after the location, category and code).
#[test]
fn unknown_message_key_panics_when_printed() {
    check(
        "bad-key",
        r#""messageKey":"Type_0_is_not_assignable_to_type_1_2322""#,
        r#""messageKey":"x""#,
        "src/b.ts(1,39): error TS2322: ",
        "Unknown diagnostic message: x",
    );
}
