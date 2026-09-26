//! Port of internal/format/format_test.go.
//!
//! PORT: Go `t.Parallel()` is dropped (cargo runs tests in parallel). A Go
//! table test is one `#[test]` with a loop that names the case in every
//! assert message. Go `t.Context()` is `gostd::context::background()`.

use crate::format::prelude::*;

use crate::format::api_test::apply_bulk_edits;
use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};
use crate::frontend::tspath::Path;

// Go: format/format_test.go:15 TestFormatNoTrailingSpace
#[test]
fn test_format_no_trailing_space() {
    struct TestCase {
        name: &'static str,
        text: &'static str,
    }

    let test_cases = [
        TestCase {
            name: "simple statement without trailing newline",
            text: "1;",
        },
        TestCase {
            name: "function call without trailing newline",
            text: "console.log('hello');",
        },
        TestCase {
            name: "if block on single line",
            text: "if (true) { }",
        },
        TestCase {
            name: "class declaration",
            text: "class A {\n    // Class Contents Go Here\n}",
        },
        TestCase {
            name: "class declaration with trailing newline",
            text: "class A {\n    // Class Contents Go Here\n}\n",
        },
        TestCase {
            name: "empty block",
            text: "if (true) {}",
        },
        TestCase {
            name: "module declaration",
            text: "module M { }",
        },
        TestCase {
            name: "enum declaration",
            text: "enum E { A, B }",
        },
    ];

    for tc in &test_cases {
        let ctx = with_format_code_settings(
            &gostd::context::background(),
            &lsutil::FormatCodeSettings {
                editor_settings: lsutil::EditorSettings {
                    tab_size: 4,
                    indent_size: 4,
                    new_line_character: "\n".to_string(),
                    convert_tabs_to_spaces: Tristate::True,
                    indent_style: lsutil::IndentStyle::SMART,
                    trim_trailing_whitespace: Tristate::True,
                    ..Default::default()
                },
                ..Default::default()
            },
            "\n",
        );
        let source_file = parse_source_file(
            &SourceFileParseOptions {
                file_name: "/test.ts".to_string(),
                path: Path("/test.ts".to_string()),
                ..Default::default()
            },
            tc.text,
            ScriptKind::TS,
        )
        .root;
        let edits = format_document(&ctx, source_file);
        let new_text = apply_bulk_edits(tc.text, &edits);
        // Formatting should not add trailing whitespace at end of file
        for (i, line) in new_text.split('\n').enumerate() {
            let trimmed = line.trim_end_matches([' ', '\t']);
            assert_eq!(
                line,
                trimmed,
                "{}: Formatter should not add trailing whitespace on line {}",
                tc.name,
                i + 1
            );
        }
    }
}
