//! Port of internal/format/indent_getindentation_test.go.
//!
//! PORT: Go `t.Parallel()` is dropped (cargo runs tests in parallel). Go
//! `t.Logf` is `println!` (cargo shows it for a failed test).

use crate::format::prelude::*;

use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};
use crate::frontend::tspath::Path;

// Go: format/indent_getindentation_test.go:13 TestGetIndentationForNamedImportsPosition
#[test]
fn test_get_indentation_for_named_imports_position() {
    let text = "import {\n    type SomeInterface,\n} from \"./exports.js\";";
    // Position 9: \n
    // Position 10: first space of "    type SomeInterface"

    let source_file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            path: Path("/test.ts".to_string()),
            ..Default::default()
        },
        text,
        ScriptKind::TS,
    )
    .root;

    let options = lsutil::get_default_format_code_settings();

    // The line that contains "    type SomeInterface" starts at position 9 (the \n).
    // The getAdjustedStartPosition with LeadingTriviaOptionNone returns line start.
    // Let's test at position 9 (start of line containing the specifier)
    let line_start = get_line_start_position_for_position(14, source_file); // 14 is somewhere in "    type"

    let indent = get_indentation(line_start, source_file, &options, true);
    println!(
        "lineStart={}, text[lineStart:]={}",
        line_start,
        gostd::strconv::quote(&text[line_start as usize..(line_start + 10) as usize])
    );
    println!("GetIndentation at lineStart {line_start} = {indent}");

    if indent != 4 {
        panic!("Expected indentation 4, got {indent}");
    }
}
