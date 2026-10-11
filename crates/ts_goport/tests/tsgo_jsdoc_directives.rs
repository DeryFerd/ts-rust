//! Issue #49: a `// @ts-ignore` or `// @ts-expect-error` inside a `JSDoc`
//! type expression. Go drops it and keeps the file's other directives
//! (parser/jsdoc.go:153-181: the `JSDoc` scan appends to a new slice). The
//! port wrote it over the earlier directives: after 2 of them the parse
//! panicked (exit 70), after 1 the wrong line was suppressed. JS files parse
//! every `JSDoc`, TS files only one with `@see` or `@link`. Each test runs
//! `tsgo -p` in a new scratch dir and expects the result of Go N prime
//! (tsgo-oracle-fed0bf24149f): no output and exit code 0. A passing test
//! deletes its dir.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// Writes `files` to a new scratch dir, runs `tsgo -p tsconfig.json` there
/// and returns the exit code, the output (stdout, then stderr) and the dir.
fn tsc(name: &str, files: &[(&str, &str)]) -> (Option<i32>, String, PathBuf) {
    let dir = std::env::temp_dir().join(format!(
        "tsgo_jsdoc_directives_{}_{name}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    for (file, text) in files {
        fs::write(dir.join(file), text).unwrap();
    }
    let out = Command::new(env!("CARGO_BIN_EXE_tsgo"))
        .args(["-p", "tsconfig.json"])
        .current_dir(&dir)
        .output()
        .unwrap();
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.code(), text, dir)
}

const TWO_DIRECTIVES_JS: &str = r#"// @ts-ignore
let a = 1; a();
// @ts-ignore
let c = 1; c();
/**
 * @typedef {{
 *   id: string, // @ts-ignore legacy field
 *   n: number
 * }} Row
 */
/** @type {Row} */
export const r = { id: "a", n: 1 };
"#;

/// Go's `out/a.js` for `TWO_DIRECTIVES_JS`.
const TWO_DIRECTIVES_GO_EMIT: &str = r#"// @ts-ignore
let a = 1;
a();
// @ts-ignore
let c = 1;
c();
/**
 * @typedef {{
 *   id: string, // @ts-ignore legacy field
 *   n: number
 * }} Row
 */
/** @type {Row} */
export const r = { id: "a", n: 1 };
"#;

/// The issue's repro 1: the parse panicked.
#[test]
fn js_directive_in_jsdoc_type_after_two_directives() {
    let (code, output, dir) = tsc(
        "two",
        &[
            (
                "tsconfig.json",
                r#"{ "compilerOptions": { "allowJs": true, "outDir": "out" }, "files": ["a.js"] }"#,
            ),
            ("a.js", TWO_DIRECTIVES_JS),
        ],
    );
    assert_eq!((code, output.as_str()), (Some(0), ""));
    let emitted = fs::read_to_string(dir.join("out/a.js")).unwrap();
    assert_eq!(emitted, TWO_DIRECTIVES_GO_EMIT);
    fs::remove_dir_all(&dir).unwrap();
}

/// The issue's repro 3 with `@ts-expect-error`: the `JSDoc` directive took
/// the place of the first one, so the error of line 2 was reported, and
/// the `JSDoc` directive got TS2578.
#[test]
fn js_expect_error_in_jsdoc_type_after_one_directive() {
    let (code, output, dir) = tsc(
        "one",
        &[
            (
                "tsconfig.json",
                r#"{ "compilerOptions": { "allowJs": true, "checkJs": true, "noEmit": true }, "files": ["a.js"] }"#,
            ),
            (
                "a.js",
                "// @ts-expect-error\nlet a = 1; a();\n/** @type {number // @ts-expect-error\n } */\nlet b = 2;\n",
            ),
        ],
    );
    assert_eq!((code, output.as_str()), (Some(0), ""));
    fs::remove_dir_all(&dir).unwrap();
}

/// The issue's repro 2: a TS file parses a `JSDoc` with `@see` at once
/// (Go jsdoc.go:62-72), and the parse panicked.
#[test]
fn ts_directive_in_jsdoc_with_see() {
    let (code, output, dir) = tsc(
        "see",
        &[
            (
                "tsconfig.json",
                r#"{"compilerOptions":{"strict":true,"noEmit":true},"files":["a.ts"]}"#,
            ),
            (
                "a.ts",
                concat!(
                    "// @ts-ignore\nlet a: number = \"x\";\n// @ts-ignore\nlet c: number = \"y\";\n",
                    "/**\n * See {@link f}.\n * @see f\n * @param x {number // @ts-ignore\n * }\n */\n",
                    "export function f(x: number) { return x; }\n",
                ),
            ),
        ],
    );
    assert_eq!((code, output.as_str()), (Some(0), ""));
    fs::remove_dir_all(&dir).unwrap();
}
