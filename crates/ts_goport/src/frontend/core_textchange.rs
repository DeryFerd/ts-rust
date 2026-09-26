//! Port of Go `core/textchange.go`.

use crate::frontend::prelude::*;

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
    #[must_use]
    pub fn apply_to(&self, text: &str) -> String {
        // PORT: Go slices the string by byte. The pieces are joined as bytes, so
        // a position inside a character works when the join is valid UTF-8.
        let bytes = text.as_bytes();
        let mut b: Vec<u8> = Vec::with_capacity(text.len() + self.new_text.len());
        b.extend_from_slice(&bytes[..self.pos() as usize]);
        b.extend_from_slice(self.new_text.as_bytes());
        b.extend_from_slice(&bytes[self.end() as usize..]);
        string_from_go_bytes(b)
    }
}

// Go: core/textchange.go:14 ApplyBulkEdits
#[must_use]
pub fn apply_bulk_edits(text: &str, edits: &[TextChange]) -> String {
    // PORT: Go `strings.Builder`; the text is built as bytes (see `apply_to`).
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

    string_from_go_bytes(b)
}

/// Go string conversion of the joined bytes.
// PORT: Go keeps any bytes. A Rust `String` must be valid UTF-8, so a join
// that splits a character (a position inside a character that the new text
// does not complete) panics here, where Go returns invalid UTF-8.
fn string_from_go_bytes(b: Vec<u8>) -> String {
    String::from_utf8(b).expect("text change splits a UTF-8 character")
}
