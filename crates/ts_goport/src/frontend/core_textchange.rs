//! Port of Go `core/textchange.go`.

use crate::frontend::prelude::*;
use crate::scanner_util::{go_byte_offset, go_string_bytes, go_string_from_bytes};
use std::borrow::Cow;

// Go: core/textchange.go:5 TextChange
// PORT: Go embeds `core.TextRange`; here it is the field `text_range`. The
// promoted `Pos` and `End` are methods below.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TextChange {
    pub text_range: TextRange,
    pub new_text: String,
}

impl TextChange {
    /// Go promoted `TextRange.Pos`.
    #[must_use]
    pub fn pos(&self) -> i32 {
        self.text_range.pos()
    }

    /// Go promoted `TextRange.End`.
    #[must_use]
    pub fn end(&self) -> i32 {
        self.text_range.end()
    }

    // Go: core/textchange.go:10 ApplyTo
    // PORT: same bytes as `apply_bulk_edits` with the one edit: Go
    // `text[:pos] + new + text[end:]`.
    #[must_use]
    pub fn apply_to(&self, text: &str) -> String {
        apply_bulk_edits(text, std::slice::from_ref(self))
    }
}

// Go: core/textchange.go:14 ApplyBulkEdits
// PORT: Go slices and joins the bytes of Go strings. Here `text` and each
// new text are port forms and the edit positions are port offsets (see
// `scanner_util::GO_STRING_MARKER`). The join is made from their Go bytes,
// at the Go offsets of the positions (`go_byte_offset`), and the result is
// the port form of the joined bytes (`go_string_from_bytes`), as a file read
// gives it. So a position inside a char keeps the cut bytes, as Go does
// (Go then reports TS1490 for such source text), and never panics.
#[must_use]
pub fn apply_bulk_edits(text: &str, edits: &[TextChange]) -> String {
    let go_text = go_string_bytes(text);
    // Text without a marker has port offsets equal to Go offsets.
    let has_marker = matches!(go_text, Cow::Owned(_));
    let go_offset = |pos: i32| -> usize {
        if has_marker {
            go_byte_offset(text, pos) as usize
        } else {
            pos as usize
        }
    };
    let mut b: Vec<u8> = Vec::with_capacity(go_text.len());
    let mut last_end = 0usize;
    for e in edits {
        let start = go_offset(e.text_range.pos());
        if start != last_end {
            b.extend_from_slice(&go_text[last_end..start]);
        }
        b.extend_from_slice(&go_string_bytes(&e.new_text));

        last_end = go_offset(e.text_range.end());
    }
    b.extend_from_slice(&go_text[last_end..]);

    go_string_from_bytes(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scanner_util::go_string_from_bytes;

    fn change(pos: i32, end: i32, new_text: &str) -> TextChange {
        TextChange {
            text_range: TextRange::new(pos, end),
            new_text: new_text.to_string(),
        }
    }

    // An edit inside a char keeps the cut bytes as Go does: the LSP
    // didChange of utf8cut `repro_lsp.py --only didchange-split` inserts "x"
    // at byte 1 of "é" (Go `core/textchange.go:10`), which panicked before.
    // Edits at port offsets in or after marker units use Go offsets.
    #[test]
    fn apply_to_joins_go_bytes() {
        let text = "const \u{e9} = 1;\n";
        assert_eq!(
            change(7, 7, "x").apply_to(text),
            go_string_from_bytes(b"const \xC3x\xA9 = 1;\n".to_vec())
        );
        // A cut char that the new text completes is valid again.
        assert_eq!(change(7, 7, "").apply_to(text), text);
        // Port form: an invalid byte (7 port bytes) and a real U+FDD0 (6).
        let text = go_string_from_bytes(b"a\xACb\xEF\xB7\x90c".to_vec());
        let cases: [(i32, i32, &str, &[u8]); 5] = [
            // After the invalid byte unit (port 1..8).
            (8, 8, "x", b"a\xACxb\xEF\xB7\x90c"),
            // 1 byte into the U+FDD0 unit (port 9..15): Go offset 4.
            (10, 10, "x", b"a\xACb\xEFx\xB7\x90c"),
            // 3 bytes into the invalid byte unit is past its 1 Go byte.
            (4, 4, "x", b"a\xACxb\xEF\xB7\x90c"),
            // Replace the U+FDD0 unit.
            (9, 15, "\u{FDD0}", b"a\xACb\xEF\xB7\x90c"),
            (0, 16, "", b""),
        ];
        for (pos, end, new_text, go) in cases {
            assert_eq!(
                change(pos, end, new_text).apply_to(&text),
                go_string_from_bytes(go.to_vec()),
                "[{pos}:{end}] {new_text:?}"
            );
        }
        assert_eq!(
            apply_bulk_edits(&text, &[change(1, 8, "y"), change(10, 10, "x")]),
            go_string_from_bytes(b"ayb\xEFx\xB7\x90c".to_vec())
        );
    }
}
