//! Port of internal/format/api_test.go.
//!
//! PORT: Go `t.Parallel()` is dropped (cargo runs tests in parallel). A Go
//! `t.Run` subtest is one `#[test]` named `<test>_<subtest>`. Go
//! `t.Context()` is `gostd::context::background()`. The Go file is the
//! external test package `format_test`; the port reaches the same items
//! through the format prelude. `BenchmarkFormat` is not ported (no
//! benchmarks in this crate).

use crate::format::prelude::*;

use crate::frontend::core_textchange::TextChange;
use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};
use crate::frontend::tspath::Path;

// Go: format/api_test.go:19 applyBulkEdits
// Used by the other format test files, as in the Go test package.
pub(super) fn apply_bulk_edits(text: &str, edits: &[TextChange]) -> String {
    // PORT: Go `strings.Builder` over byte slices of `text`; the text is
    // built as bytes.
    let bytes = text.as_bytes();
    let mut b: Vec<u8> = Vec::with_capacity(text.len());
    let mut last_end: i32 = 0;
    for e in edits {
        let start = e.text_range.pos();
        if start != last_end {
            b.extend_from_slice(&bytes[last_end as usize..e.text_range.pos() as usize]);
        }
        b.extend_from_slice(e.new_text.as_bytes());

        last_end = e.text_range.end();
    }
    b.extend_from_slice(&bytes[last_end as usize..]);

    // PORT: Go keeps any bytes; a Rust `String` must be valid UTF-8.
    String::from_utf8(b).expect("edits split a UTF-8 character")
}

// Go: repo/paths.go TestDataPath
// PORT: Go finds the repo root (`tsc/`) from the test source path. The port
// reads the pinned Go checkout: `TS_GO_REPO` (set by goport-tests.sh), or
// the default checkout path that `pin.py exec` binds.
fn test_data_path() -> std::path::PathBuf {
    let repo = match std::env::var_os("TS_GO_REPO") {
        Some(repo) if !repo.is_empty() => std::path::PathBuf::from(repo),
        _ => std::path::Path::new(&std::env::var("HOME").unwrap_or_default())
            .join(".explore/repos/microsoft__typescript-go"),
    };
    repo.join("testdata")
}

// Go: format/api_test.go:37 TestFormat, "format checker.ts"
#[test]
fn test_format_format_checker_ts() {
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
    let file_path = test_data_path().join("fixtures/compiler/checker.ts");
    let file_content = std::fs::read(&file_path);
    if let Err(err) = &file_content {
        panic!("expected no error, got {err}");
    }
    // PORT: Go `string(fileContent)` keeps any bytes; checker.ts is UTF-8.
    // The parser takes `&'static str`, so the text is leaked.
    let text: &'static str = String::from_utf8(file_content.unwrap())
        .expect("checker.ts is not UTF-8")
        .leak();
    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/checker.ts".to_string(),
            path: Path("/checker.ts".to_string()),
            ..Default::default()
        },
        text,
        ScriptKind::TS,
    )
    .root;
    let edits = format_document(&ctx, source_file);
    let new_text = apply_bulk_edits(text, &edits);
    assert!(!new_text.is_empty());
    assert!(text != new_text);
}

// Go: format/api_test.go:67 BenchmarkFormat
// PORT: not ported (benchmark).
