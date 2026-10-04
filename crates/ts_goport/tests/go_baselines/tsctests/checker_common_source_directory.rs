//! Port-only test of the TS6059 errors that a checker records on a
//! referenced project (Go `checker/checker.go:15547`
//! `redirect.CommonSourceDirectory()`).
//!
//! PORT: no Go counterpart (projfix1 skeptic case t11). With
//! `rewriteRelativeImportExtensions`, the checker of `a` reads the common
//! source directory of its reference `b`, and that first call appends
//! TS6059 to b's `Errors` (`tsoptions/parsedcommandline.go:181`). In a
//! cycle `b` builds after `a`, so it reports that error with the one of its
//! own program. The port's checker reads a thread-safe copy of `b`, and
//! the error was lost. The expected counts are Go N's.

use crate::support::child::run_command_in_child;
use crate::support::runner::TscInput;
use crate::support::test_sys::{TestSys, new_test_sys};

const PROJECT: &str = "/home/src/workspaces/project";

/// Runs `args` and gives the number of TS6059 errors in its output, and
/// the output.
fn ts6059_count(sys: &TestSys, args: &[&str]) -> (usize, String) {
    sys.clear_output();
    let args: Vec<String> = args.iter().map(|arg| (*arg).to_string()).collect();
    let result = run_command_in_child(sys, &args).unwrap_or_else(|err| panic!("tsgo: {err}"));
    assert!(result.unported.is_none(), "unported {:?}", result.unported);
    let output = sys.output_text();
    (output.matches("TS6059: ").count(), output)
}

#[test]
fn a_checker_records_ts6059_on_a_reference_like_go() {
    let file = |name: &str, text: &str| (format!("{PROJECT}/{name}"), text.into());
    let input = TscInput {
        files: [
            file(
                "a/tsconfig.json",
                r#"{"compilerOptions":{"composite":true,"rewriteRelativeImportExtensions":true,"module":"nodenext"},"references":[{"path":"../b","circular":true}]}"#,
            ),
            file("a/package.json", r#"{"type":"module"}"#),
            file(
                "a/x.ts",
                "import { y } from \"../b/src/y.ts\";\nexport const x = y;\n",
            ),
            // b/other.ts is outside rootDir, and b has no outDir.
            file(
                "b/tsconfig.json",
                r#"{"compilerOptions":{"composite":true,"rootDir":"src","module":"nodenext"},"references":[{"path":"../a","circular":true}]}"#,
            ),
            file("b/package.json", r#"{"type":"module"}"#),
            file("b/src/y.ts", "export const y = 1;\n"),
            file("b/other.ts", "export const o = 1;\n"),
        ]
        .into_iter()
        .collect(),
        ..Default::default()
    };
    let sys = new_test_sys(&input, false);
    let (count, output) = ts6059_count(&sys, &["-p", "b"]);
    assert_eq!(count, 0, "{output}");
    // a builds first and finds no b/src/y.d.ts (TS6305): its checker does
    // not read b's directory.
    let (count, output) = ts6059_count(&sys, &["-b", "-v", "b"]);
    assert_eq!(count, 1, "{output}");
    // Now a's checker reads it: b reports the error of its program and the
    // one the checker recorded on its config.
    let (count, output) = ts6059_count(&sys, &["-b", "-v", "b"]);
    assert_eq!(count, 2, "{output}");
}
