//! Go `scanner` entry points for the language service
//! (`scanner/scanner.go:2519-2527` `GetScannerForSourceFile`,
//! `scanner/scanner.go:2738-2740` `GetECMAPositionOfLineAndByteOffset`).
//!
//! PORT: ls, astnav and format scan with the literal Go scanner
//! (`frontend::scanner::Scanner`), not `RsScanner`, because they need Go
//! token boundaries and `ReScanJsxToken`. The crate-level
//! `scanner_util::get_scanner_for_source_file` (which returns `RsScanner`)
//! stays as it is for the compiler.

use crate::frontend::prelude::*;
use crate::frontend::scanner::{Scanner, new_scanner};
use std::borrow::Cow;

// Go: scanner/scanner.go:2519 GetScannerForSourceFile
pub fn get_scanner_for_source_file(source_file: Node, pos: i32) -> Scanner {
    let mut s = new_scanner();
    s.text = Cow::Borrowed(source_file_text(source_file));
    s.scanner_state.pos = pos;
    s.end = s.text.len() as i32;
    s.language_variant = source_file_language_variant(source_file);
    s.scan();
    s
}

// Go: scanner/scanner.go:2738 GetECMAPositionOfLineAndByteOffset
/// GetECMAPositionOfLineAndByteOffset converts a 0-based line number and byte offset
/// from line start back to an absolute byte position in the source text.
/// Uses ECMAScript line separators.
// PORT: Go `ast.SourceFileLike` is the source file `Node`.
pub fn get_ecma_position_of_line_and_byte_offset(
    source_file: Node,
    line: i32,
    byte_offset: i32,
) -> i32 {
    compute_position_of_line_and_byte_offset(get_ecma_line_starts(source_file), line, byte_offset)
}
