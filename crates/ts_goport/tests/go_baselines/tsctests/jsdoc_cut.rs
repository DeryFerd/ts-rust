//! Port-only test of the JSDoc text cut of `parse_js_doc_comment` (Go
//! `parser/jsdoc.go:163 parseJSDocComment`).
//!
//! PORT: no Go counterpart (optapifuzz1 A). An unterminated JSDoc comment
//! runs to the end of the file, and Go cuts its text 2 bytes before the end.
//! When those 2 bytes split a char, Go keeps the bytes of the char before
//! the cut and its scanner reads each one as RuneError. The port panicked on
//! that cut and `tsc` exited 70. A JS file parses its JSDoc at once. Each
//! expected output is Go N's.

use ts_goport::execute::tsc::ExitStatus;

use crate::support::child::run_command_in_child;
use crate::support::runner::TscInput;
use crate::support::test_sys::new_test_sys;

const PROJECT: &str = "/home/src/workspaces/project";

#[test]
fn jsdoc_cut_inside_a_char_at_the_end_of_a_js_file() {
    let cases = [
        // The last char has 4 bytes: Go keeps 2.
        ("/** x 😀", "a.js(1,9): error TS1010: '*/' expected.\n"),
        // A 2-byte char and 1 ASCII byte: Go keeps 1 byte of the char.
        ("/** Cafés", "a.js(1,10): error TS1010: '*/' expected.\n"),
        // A tag with a comment that runs to the end of the file.
        (
            "function g(p) { p.x; }\n/** @param {G} p *=>/\nfunction h() {}\né中😀",
            "a.js(4,5): error TS1010: '*/' expected.\n",
        ),
    ];
    for (text, want) in cases {
        let input = TscInput {
            files: [
                (format!("{PROJECT}/a.js"), text.into()),
                (
                    format!("{PROJECT}/tsconfig.json"),
                    r#"{"compilerOptions":{"allowJs":true,"checkJs":true,"noEmit":true},"files":["a.js"]}"#
                        .into(),
                ),
            ]
            .into_iter()
            .collect(),
            ..Default::default()
        };
        let sys = new_test_sys(&input, false);
        let args = ["-p", "tsconfig.json", "--pretty", "false"].map(String::from);
        let result = run_command_in_child(&sys, &args).unwrap_or_else(|err| panic!("tsgo: {err}"));
        assert!(result.unported.is_none(), "unported {:?}", result.unported);
        // The test system adds the list of files after the diagnostics.
        let output = sys.output_text();
        let diagnostics = output.split("!!! List files start").next();
        assert_eq!(diagnostics, Some(want), "{text}");
        assert_eq!(
            result.status,
            ExitStatus::DiagnosticsPresentOutputsGenerated,
            "{text}"
        );
    }
}
