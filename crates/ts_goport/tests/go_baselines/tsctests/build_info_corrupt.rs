//! Port-only tests of a `.tsbuildinfo` that is valid JSON with bad values
//! (portgaps1 N2, N4, and the bifix1 review). Go N panics where it reads or
//! prints them and exits 2. The port hung on a negative diagnostic `pos`,
//! exited 70 with Rust panic text on other values, and did not keep a bad
//! category as Go does (sort order, build info written again).
//!
//! PORT: no Go counterpart. Each test makes the build info with `tsgo -p .`
//! (the same bytes as Go N), changes one value (or adds a changed copy of a
//! diagnostic) and runs `tsgo -p .` and `tsgo -b` again. The expected exit code, stdout and first stderr line are
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
    check_runs(name, from, to, p_stdout, panic, false);
}

/// As `check`, but the project also has `src/x.ts` (no imports, no errors),
/// and each run edits it first. Go then writes the build info again before
/// the panic, from the diagnostics that it read. The new build info must
/// keep `to`.
fn check_written_again(name: &str, from: &str, to: &str, p_stdout: &str, panic: &str) {
    check_runs(name, from, to, p_stdout, panic, true);
}

/// The runs of `check` and `check_written_again`.
fn check_runs(name: &str, from: &str, to: &str, p_stdout: &str, panic: &str, edit_x: bool) {
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
    if edit_x {
        dir.write("src/x.ts", "export const x = 1;\n");
    }
    let first = tsgo(&dir.0, &["-p", "."]);
    assert_eq!(first.code, Some(2), "first build: {first:?}");
    let build_info_path = dir.0.join("tsconfig.tsbuildinfo");
    let build_info = std::fs::read_to_string(&build_info_path).expect("build info");
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
        if edit_x {
            dir.write("src/x.ts", "export const x = 2;\n");
        }
        let want = Run {
            code: Some(2),
            stdout: stdout.to_string(),
            panic: format!("panic: {panic}"),
        };
        assert_eq!(tsgo(&dir.0, args), want, "{name} {args:?}");
        if edit_x {
            let written = std::fs::read_to_string(&build_info_path).expect("build info");
            assert_ne!(
                written, bad,
                "{name} {args:?}: build info not written again"
            );
            assert!(
                written.contains(to),
                "{name} {args:?}: {to:?} not in {written}"
            );
        }
    }
}

/// The one diagnostic of `src/b.ts` in the build info.
const B_DIAGNOSTIC: &str = r#"{"pos":38,"end":39,"code":2322,"category":1,"messageKey":"Type_0_is_not_assignable_to_type_1_2322","messageArgs":["number","string"]}"#;

/// `B_DIAGNOSTIC`, then a copy of it with category `category`.
fn with_copy_of_category(category: i32) -> String {
    let copy = B_DIAGNOSTIC.replace(r#""category":1,"#, &format!(r#""category":{category},"#));
    format!("{B_DIAGNOSTIC},{copy}")
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

// Go: tsoptions/parsinghelpers.go:574 `value.(float64)` in
// floatOrInt32ToFlag, when the build info options are read.
#[test]
fn module_option_of_another_json_type_panics_interface_conversion() {
    check(
        "bad-module",
        r#""strict":true}"#,
        r#""strict":true,"module":"x"}"#,
        "",
        "interface conversion: interface {} is string, not float64",
    );
}

// Go: diagnostics/diagnostics.go:142 `Format`, when the message is printed
// with fewer `messageArgs` than it has placeholders.
#[test]
fn too_few_message_args_panic_when_printed() {
    check(
        "few-args",
        r#""messageArgs":["number","string"]"#,
        r#""messageArgs":["number"]"#,
        "src/b.ts(1,39): error TS2322: ",
        "Invalid formatting placeholder",
    );
}

// Go: ast/diagnostic.go:502 `CompareDiagnostics` compares the categories
// as ints, so a negative category sorts before the error at the same place
// and is printed (and panics) first.
#[test]
fn negative_category_sorts_first() {
    check(
        "neg-cat-sort",
        B_DIAGNOSTIC,
        &with_copy_of_category(-1),
        "src/b.ts(1,39): ",
        "Unhandled diagnostic category",
    );
}

// Go: execute/incremental/snapshottobuildinfo.go:166 writes the category
// that the read diagnostic keeps, not a fixed value.
#[test]
fn unhandled_category_is_written_again() {
    check_written_again(
        "bad-cat-written",
        r#""category":1,"#,
        r#""category":999,"#,
        "src/b.ts(1,39): ",
        "Unhandled diagnostic category",
    );
}

// Go: ast/diagnostic.go:502 subtracts the categories as Go ints (64 bits),
// so -2147483648 sorts before 1. An `i32` difference wraps.
#[test]
fn far_apart_categories_sort_as_go_ints() {
    check(
        "min-cat-sort",
        B_DIAGNOSTIC,
        &with_copy_of_category(i32::MIN),
        "src/b.ts(1,39): ",
        "Unhandled diagnostic category",
    );
}

/// Builds the project with `src/x.ts`, replaces `from` (once) with `to` in
/// its build info, and gives `src/x.ts` a syntax error, so no semantic
/// diagnostic is asked for and those of `src/b.ts` are written from the
/// read form. `tsgo -p .` and `tsgo -b` report the syntax error (Go N's
/// text) and write a build info that has `written`.
fn check_read_form_written_again(name: &str, from: &str, to: &str, written: &str) {
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
    dir.write("src/x.ts", "export const x = 1;\n");
    let first = tsgo(&dir.0, &["-p", "."]);
    assert_eq!(first.code, Some(2), "first build: {first:?}");
    let build_info_path = dir.0.join("tsconfig.tsbuildinfo");
    let build_info = std::fs::read_to_string(&build_info_path).expect("build info");
    assert_eq!(
        build_info.matches(from).count(),
        1,
        "{from:?} once in {build_info}"
    );
    let bad = build_info.replace(from, to);
    for args in [&["-p", "."][..], &["-b"][..]] {
        dir.write("tsconfig.tsbuildinfo", &bad);
        dir.write("src/x.ts", "export const x = ;\n");
        let want = Run {
            code: Some(2),
            stdout: "src/x.ts(1,18): error TS1109: Expression expected.\n".to_string(),
            panic: String::new(),
        };
        assert_eq!(tsgo(&dir.0, args), want, "{name} {args:?}");
        let new = std::fs::read_to_string(&build_info_path).expect("build info");
        assert_ne!(new, bad, "{name} {args:?}: build info not written again");
        assert!(
            new.contains(written),
            "{name} {args:?}: {written:?} not in {new}"
        );
    }
}

// Go: execute/incremental/buildInfo.go:209 writes `messageArgs` with
// `omitzero`. A read `"messageArgs":[]` is an empty slice, not nil, and the
// snapshot keeps it (buildinfotosnapshot.go:85, snapshottobuildinfo.go:140),
// so the build info written again has `[]` too. Texts and bytes from the pin
// N oracle.
// PORT: when the read diagnostics are reported first (no syntax error),
// Go writes them from its `ast.Diagnostic` copies, which also keep `[]`.
// The port's `Diagnostic.message_args` (core.rs) has no nil, so that path
// still drops it (followups25).
#[test]
fn empty_message_args_are_written_again() {
    check_read_form_written_again(
        "empty-args",
        r#""messageArgs":["number","string"]"#,
        r#""messageArgs":[]"#,
        r#""messageKey":"Type_0_is_not_assignable_to_type_1_2322","messageArgs":[]}"#,
    );
}

// Go: execute/incremental/buildInfo.go:210 and :211 write `messageChain`
// and `relatedInformation` with `omitzero`, as `messageArgs`. Go `core.Map`
// keeps a read empty list empty (buildinfotosnapshot.go:86 and :87,
// snapshottobuildinfo.go:141 and :142), so the build info written again has
// both `[]`. Bytes from the pin N oracle.
// PORT: the ast path drops them, as for `messageArgs`.
#[test]
fn empty_message_chain_and_related_information_are_written_again() {
    let lists = r#""messageArgs":["number","string"],"messageChain":[],"relatedInformation":[]}"#;
    check_read_form_written_again(
        "empty-lists",
        r#""messageArgs":["number","string"]}"#,
        lists,
        lists,
    );
}

// Go: diagnosticwriter/diagnosticwriter.go:266 `start+length` is a Go int,
// and `length` is the wrapped int32 difference of the ends (core/text.go:30).
// An `end` of ±2^31 (int32 -2^31 either way) gives `38 + 2147483610`, past
// the text, so `--pretty` panics in `text[lineMap[line]:pos]` after it
// writes the diagnostic's first line. The port added the two as `i32`,
// which wrapped to line -1 (`index out of range [-1]`).
#[test]
fn far_diagnostic_end_panics_slice_bounds_with_pretty() {
    for end in ["2147483648", "-2147483648"] {
        let dir = TmpDir::new(&format!("build-info-far-end{end}"));
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
        let build_info_path = dir.0.join("tsconfig.tsbuildinfo");
        let build_info = std::fs::read_to_string(&build_info_path).expect("build info");
        let bad = build_info.replace(r#""end":39,"#, &format!(r#""end":{end},"#));
        assert_ne!(bad, build_info, "end in {build_info}");
        dir.write("tsconfig.tsbuildinfo", &bad);
        let want = Run {
            code: Some(2),
            stdout: "\u{1b}[96msrc/b.ts\u{1b}[0m:\u{1b}[93m1\u{1b}[0m:\u{1b}[93m39\u{1b}[0m - \u{1b}[91merror\u{1b}[0m\u{1b}[90m TS2322: \u{1b}[0mType 'number' is not assignable to type 'string'.\n".to_string(),
            panic: "panic: runtime error: slice bounds out of range [:2147483648] with length 53"
                .to_string(),
        };
        assert_eq!(tsgo(&dir.0, &["-p", ".", "--pretty"]), want, "end {end}");
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:266 and scanner/scanner.go:2687
// on a source file with bytes that are not valid UTF-8. The port text holds
// each such byte as a marker unit, which is longer than the byte
// (`scanner_util::GO_STRING_MARKER`), and a diagnostic's ends are port
// offsets. The panic texts have Go's offsets and length: the wrapped
// `--pretty` end (`38 + 2147483610`, from Go's ends) and a `pos` of
// `2147483647`, which has no port offset `pos + 12` (the port kept it, not
// a wrapped -2147483637: `index out of range [-1]`). Texts from the pin N
// oracle.
#[test]
fn far_positions_in_a_file_with_raw_bytes_panic_as_go() {
    let pretty_line = "\u{1b}[96msrc/b.ts\u{1b}[0m:\u{1b}[93m1\u{1b}[0m:\u{1b}[93m39\u{1b}[0m - \u{1b}[91merror\u{1b}[0m\u{1b}[90m TS2322: \u{1b}[0mType 'number' is not assignable to type 'string'.\n";
    for (from, to, args, stdout, go_pos) in [
        (
            r#""end":39,"#,
            r#""end":2147483648,"#,
            &["-p", ".", "--pretty"][..],
            pretty_line,
            "2147483648",
        ),
        (
            r#""end":39,"#,
            r#""end":-2147483648,"#,
            &["-p", ".", "--pretty"][..],
            pretty_line,
            "2147483648",
        ),
        (
            r#""pos":38,"#,
            r#""pos":2147483647,"#,
            &["-p", "."][..],
            "",
            "2147483647",
        ),
    ] {
        let dir = TmpDir::new("build-info-raw-bytes");
        dir.write(
            "tsconfig.json",
            r#"{ "compilerOptions": { "outDir": "dist", "rootDir": "src", "incremental": true, "strict": true, "lib": ["es5"] }, "include": ["src"] }"#,
        );
        dir.write("src/a.ts", "export const a: number = 1;\n");
        std::fs::write(
            dir.0.join("src/b.ts"),
            b"import { a } from \"./a\"; export const b: string = a; // \xff\xfe\n",
        )
        .expect("write src/b.ts");
        let first = tsgo(&dir.0, &["-p", "."]);
        assert_eq!(first.code, Some(2), "first build: {first:?}");
        let build_info_path = dir.0.join("tsconfig.tsbuildinfo");
        let build_info = std::fs::read_to_string(&build_info_path).expect("build info");
        assert_eq!(
            build_info.matches(from).count(),
            1,
            "{from:?} in {build_info}"
        );
        dir.write("tsconfig.tsbuildinfo", &build_info.replace(from, to));
        let want = Run {
            code: Some(2),
            stdout: stdout.to_string(),
            panic: format!(
                "panic: runtime error: slice bounds out of range [:{go_pos}] with length 59"
            ),
        };
        assert_eq!(tsgo(&dir.0, args), want, "{to} {args:?}");
    }
}
