//! Port of internal/testutil/emittestutil/emittestutil.go.

use super::parsetestutil::{check_diagnostics_message, parse_type_script};
use ts_goport::ast::{is_synthetic_node, source_file_language_variant, with_synthetic_source_file};
use ts_goport::prelude::*;

/// Go `file.LanguageVariant` of a parsed or factory SourceFile.
fn language_variant(file: Node) -> LanguageVariant {
    if is_synthetic_node(file) {
        return with_synthetic_source_file(file, |d| d.language_variant);
    }
    source_file_language_variant(file)
}

// Go: testutil/emittestutil/emittestutil.go:15 CheckEmit
/// Checks that pretty-printing the given file matches the expected output.
pub(crate) fn check_emit(
    emit_context: Option<Rc<EmitContext>>,
    file: Node,
    expected: &str,
) -> Result<(), String> {
    let mut printer = new_printer(
        PrinterOptions {
            new_line: NewLineKind::LF,
            ..Default::default()
        },
        PrintHandlers::default(),
        emit_context,
    );
    let text = printer.emit_source_file_exported(file);
    let actual = text.strip_suffix('\n').unwrap_or(&text);
    if expected != actual {
        return Err(format!(
            "assertion failed: expected != actual\n  expected: {expected:?}\n  actual:   {actual:?}"
        ));
    }
    let file2 = parse_type_script(&text, language_variant(file) == LanguageVariant::JSX);
    check_diagnostics_message(file2, "error on reparse: ")
}
