//! Port of internal/lsp/lsproto/util.go.

use crate::lsp::lsproto::prelude::*;

// Go: util.go:9 ComparePositions
// Implements a cmp.Compare like function for two Position
// ComparePositions(pos, other) == cmp.Compare(pos, other)
pub fn compare_positions(pos: Position, other: Position) -> i32 {
    let line_comp = pos.line.cmp(&other.line) as i32;
    if line_comp != 0 {
        return line_comp;
    }
    pos.character.cmp(&other.character) as i32
}

// Go: util.go:20 CompareRanges
// Implements a cmp.Compare like function for two Range
// CompareRanges(lsRange, other) == cmp.Compare(lsRange, other)
//
//	Range.Start is compared before Range.End
pub fn compare_ranges(ls_range: Range, other: Range) -> i32 {
    let start_comp = compare_positions(ls_range.start, other.start);
    if start_comp != 0 {
        return start_comp;
    }
    compare_positions(ls_range.end, other.end)
}

impl StringOrMarkupContent {
    // Go: util.go:29 AsString
    // AsString returns the plain text of a StringOrMarkupContent, reading the
    // MarkupContent value when the message is not a plain string.
    pub fn as_string(&self) -> String {
        if let Some(s) = &self.string {
            return s.clone();
        }
        if let Some(m) = &self.markup_content {
            return m.value.clone();
        }
        String::new()
    }
}
