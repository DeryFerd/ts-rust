//! Port of internal/format/comment_test.go.
//!
//! PORT: Go `t.Parallel()` is dropped (cargo runs tests in parallel). A Go
//! `t.Run` subtest is one `#[test]` named `<test>_<subtest>`. Go
//! `t.Context()` is `gostd::context::background()`. gotest.tools
//! `assert.Check` records a failure and continues; `assert!` stops at the
//! first failure. Only the failure report differs.

use crate::format::prelude::*;

use crate::format::api_test::apply_bulk_edits;
use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};
use crate::frontend::tspath::Path;

// Go: format/comment_test.go:15 TestCommentFormatting, "format comment issue reproduction"
#[test]
fn test_comment_formatting_format_comment_issue_reproduction() {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 4,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::True,
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            insert_space_before_type_annotation: Tristate::True,
            ..Default::default()
        },
        "\n",
    );

    // Original code that causes the bug
    let original_text = "class C {\n    /**\n     *\n    */\n    async x() {}\n}";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    // Apply formatting once
    let edits = format_document(&ctx, source_file);
    // PORT: the parser takes `&'static str`, so the formatted text is leaked.
    let first_formatted: &'static str = apply_bulk_edits(original_text, &edits).leak();

    // Check that the asterisk is not corrupted
    assert!(
        !first_formatted.contains("*/\n   /"),
        "should not corrupt */ to /"
    );
    assert!(first_formatted.contains("*/"), "should preserve */ token");
    assert!(
        first_formatted.contains("async"),
        "should preserve async keyword"
    );

    // Apply formatting a second time to test stability
    let source_file2 = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        first_formatted,
        ScriptKind::TS,
    )
    .root;

    let edits2 = format_document(&ctx, source_file2);
    let second_formatted = apply_bulk_edits(first_formatted, &edits2);

    // Check that second formatting doesn't introduce corruption
    assert!(
        !second_formatted.contains(" sync x()"),
        "should not corrupt async to sync"
    );
    assert!(
        second_formatted.contains("async"),
        "should preserve async keyword on second pass"
    );
}

// Go: format/comment_test.go:15 TestCommentFormatting, "format JSDoc with tab indentation"
#[test]
fn test_comment_formatting_format_js_doc_with_tab_indentation() {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::False, // Use tabs
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            insert_space_before_type_annotation: Tristate::True,
            ..Default::default()
        },
        "\n",
    );

    // Original code with tab indentation (tabs represented as \t)
    let original_text = "class Foo {\n\t/**\n\t * @param {string} argument - This is a param description.\n\t */\n\texample(argument) {\nconsole.log(argument);\n\t}\n}";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    // Apply formatting
    let edits = format_document(&ctx, source_file);
    let formatted = apply_bulk_edits(original_text, &edits);

    // Check that tabs come before spaces (not spaces before tabs)
    // The comment lines should have format: tab followed by space and asterisk
    // NOT: space followed by tab and asterisk
    assert!(
        !formatted.contains(" \t*"),
        "should not have space before tab before asterisk"
    );
    assert!(
        formatted.contains("\t *"),
        "should have tab before space before asterisk"
    );

    // Verify console.log is properly indented with tabs
    assert!(
        formatted.contains("\t\tconsole.log"),
        "console.log should be indented with two tabs"
    );
}

// Go: format/comment_test.go:15 TestCommentFormatting, "format comment inside multi-line argument list"
#[test]
fn test_comment_formatting_format_comment_inside_multi_line_argument_list() {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::False, // Use tabs
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            insert_space_before_type_annotation: Tristate::True,
            ..Default::default()
        },
        "\n",
    );

    // Original code with proper indentation
    let original_text = "console.log(\n\t\"a\",\n\t// the second arg\n\t\"b\"\n);";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    // Apply formatting
    let edits = format_document(&ctx, source_file);
    let formatted = apply_bulk_edits(original_text, &edits);

    // The comment should remain indented with a tab
    assert!(
        formatted.contains("\t// the second arg"),
        "comment should be indented with tab"
    );
    // The comment should not lose its indentation
    assert!(
        !formatted.contains("\n// the second arg"),
        "comment should not lose indentation"
    );
}

// Go: format/comment_test.go:15 TestCommentFormatting, "format comment in chained method calls"
#[test]
fn test_comment_formatting_format_comment_in_chained_method_calls() {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::False, // Use tabs
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            insert_space_before_type_annotation: Tristate::True,
            ..Default::default()
        },
        "\n",
    );

    // Original code with proper indentation
    let original_text = "foo\n\t.bar()\n\t// A second call\n\t.baz();";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    // Apply formatting
    let edits = format_document(&ctx, source_file);
    let formatted = apply_bulk_edits(original_text, &edits);

    // The comment should remain indented
    assert!(
        formatted.contains("\t// A second call") || formatted.contains("   // A second call"),
        "comment should be indented"
    );
    // The comment should not lose its indentation
    assert!(
        !formatted.contains("\n// A second call"),
        "comment should not lose indentation"
    );
}

// Go: format/comment_test.go:15 TestCommentFormatting, "format chained method call with comment (issue #1928)"
// Regression test for issue #1928 - panic when formatting chained method call with comment
#[test]
fn test_comment_formatting_format_chained_method_call_with_comment_issue_1928() {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::False, // Use tabs
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            insert_space_before_type_annotation: Tristate::True,
            ..Default::default()
        },
        "\n",
    );

    // This code previously caused a panic with "strings: negative Repeat count"
    // because tokenIndentation was -1 and was being used directly for indentation
    let original_text = "foo\n\t.bar()\n\t// A second call\n\t.baz();";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    // Apply formatting - should not panic
    let edits = format_document(&ctx, source_file);
    let formatted = apply_bulk_edits(original_text, &edits);

    // Verify the comment maintains proper indentation and doesn't lose it
    assert!(
        formatted.contains("\t// A second call") || formatted.contains("   // A second call"),
        "comment should be indented"
    );
    assert!(
        !formatted.contains("\n// A second call"),
        "comment should not be at column 0"
    );
}

// Go: format/comment_test.go:15 TestCommentFormatting, "multiline comment inside block that opens on first line (issue #2649)"
#[test]
fn test_comment_formatting_multiline_comment_inside_block_that_opens_on_first_line_issue_2649() {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::False,
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            ..Default::default()
        },
        "\n",
    );

    let original_text = "document.addEventListener('DOMContentLoaded', () => {\n    /** @type {NodeListOf<HTMLSpanElement>} */\n    const elements = document.querySelectorAll('.test')\n});";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.js".to_string(),
            path: Path("/test.js".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::JS,
    )
    .root;

    let edits = format_document(&ctx, source_file);
    let formatted = apply_bulk_edits(original_text, &edits);
    assert!(!formatted.is_empty(), "formatted text should not be empty");
}

// Go: format/comment_test.go:15 TestCommentFormatting, "single-line comment inside block that opens on first line (issue #2649)"
#[test]
fn test_comment_formatting_single_line_comment_inside_block_that_opens_on_first_line_issue_2649() {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::False,
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            ..Default::default()
        },
        "\n",
    );

    let original_text = "document.addEventListener('DOMContentLoaded', () => {\n    // a comment\n    const x = 1\n});";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    let edits = format_document(&ctx, source_file);
    let formatted = apply_bulk_edits(original_text, &edits);
    assert!(!formatted.is_empty(), "formatted text should not be empty");
}

// Go: format/comment_test.go:265 TestFormatSelectionPreservesComments, "format selection should not delete block comment when selection ends inside comment"
#[test]
fn test_format_selection_preserves_comments_format_selection_should_not_delete_block_comment_when_selection_ends_inside_comment()
 {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::True,
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            ..Default::default()
        },
        "\n",
    );

    // Reproduce: const test/* comment */=5;
    // When selecting a range that ends inside the comment (before */), format selection should not delete the comment.
    let original_text = "const test/* comment */=5;";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    // Select a range that starts at the beginning of the line and ends inside the block comment.
    // This covers `const test/* comment`, stopping before the closing `*/`.
    // PORT: Go `strings.Index` returns -1 when absent.
    let comment_start = original_text.find("/*").map_or(-1, |i| i as i32);
    let selection_end = comment_start + "/* comment".len() as i32; // ends inside the comment, before the closing `*/`

    let edits = format_selection(&ctx, source_file, 0, selection_end);
    let formatted = apply_bulk_edits(original_text, &edits);

    // The entire statement should be preserved unchanged
    assert_eq!(
        formatted, original_text,
        "format selection should not delete the block comment or alter the statement"
    );
}

// Go: format/comment_test.go:265 TestFormatSelectionPreservesComments, "format selection should not delete block comment when selection starts inside comment"
#[test]
fn test_format_selection_preserves_comments_format_selection_should_not_delete_block_comment_when_selection_starts_inside_comment()
 {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::True,
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            ..Default::default()
        },
        "\n",
    );

    let original_text = "const test/* comment */=5;";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    // Select from inside the comment to the end
    // PORT: Go `strings.Index` returns -1 when absent.
    let comment_start = original_text.find("/*").map_or(-1, |i| i as i32);
    let selection_start = comment_start + 3; // inside the comment

    let edits = format_selection(
        &ctx,
        source_file,
        selection_start,
        original_text.len() as i32,
    );
    let formatted = apply_bulk_edits(original_text, &edits);

    // The entire statement should be preserved unchanged
    assert_eq!(
        formatted, original_text,
        "format selection should not delete the block comment or alter the statement"
    );
}

// Go: format/comment_test.go:265 TestFormatSelectionPreservesComments, "full document format should preserve block comment and add spaces"
#[test]
fn test_format_selection_preserves_comments_full_document_format_should_preserve_block_comment_and_add_spaces()
 {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::True,
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            insert_space_before_and_after_binary_operators: Tristate::True,
            ..Default::default()
        },
        "\n",
    );

    let original_text = "const test/* comment */=5;";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    let edits = format_document(&ctx, source_file);
    let formatted = apply_bulk_edits(original_text, &edits);

    // Full document format should preserve the comment and add spaces around `=`
    assert_eq!(
        "const test/* comment */ = 5;", formatted,
        "full format should preserve the block comment and add spaces"
    );
}

// Go: format/comment_test.go:365 TestSliceBoundsPanic, "format code with trailing semicolon should not panic"
#[test]
fn test_slice_bounds_panic_format_code_with_trailing_semicolon_should_not_panic() {
    let ctx = with_format_code_settings(
        &gostd::context::background(),
        &lsutil::FormatCodeSettings {
            editor_settings: lsutil::EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 4,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: Tristate::True,
                indent_style: lsutil::IndentStyle::SMART,
                trim_trailing_whitespace: Tristate::True,
            },
            insert_space_before_type_annotation: Tristate::True,
            ..Default::default()
        },
        "\n",
    );

    // Code from the issue that causes slice bounds panic
    let original_text = "const _enableDisposeWithListenerWarning = false\n\t// || Boolean(\"TRUE\") // causes a linter warning so that it cannot be pushed\n\t;\n";

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        original_text,
        ScriptKind::TS,
    )
    .root;

    // This should not panic
    let edits = format_document(&ctx, source_file);
    let formatted = apply_bulk_edits(original_text, &edits);

    // Basic sanity checks
    assert!(!formatted.is_empty(), "formatted text should not be empty");
    assert!(
        formatted.contains("_enableDisposeWithListenerWarning"),
        "should preserve variable name"
    );
}
