//! Port of Go `api/encoder/stringtable.go`.
//!
//! PORT: Go `int` byte lengths and offsets in this file are `usize` (they
//! index byte buffers). Go string slices and comparisons work on bytes, so
//! the port compares bytes and never slices a `&str`.

use crate::api::encoder::prelude::*;

// Go: api/encoder/stringtable.go:9 stringTable
pub struct StringTable {
    pub file_text: &'static str,
    // PORT: Go `*strings.Builder`.
    pub other_strings: String,
    // offsets are pos/end pairs
    pub offsets: Vec<u32>,
}

// Go: api/encoder/stringtable.go:16 newStringTable
pub fn new_string_table(file_text: &'static str, string_count: usize) -> StringTable {
    let builder = String::new();
    StringTable {
        file_text,
        other_strings: builder,
        offsets: Vec::with_capacity(string_count * 2),
    }
}

impl StringTable {
    // Go: api/encoder/stringtable.go:25 (*stringTable).add
    pub fn add(&mut self, text: &str, kind: SyntaxKind, pos: i32, end: i32) -> u32 {
        let index = self.offsets.len() as u32;
        if kind == SyntaxKind::SourceFile {
            self.offsets.push(pos as u32);
            self.offsets.push(end as u32);
            return index;
        }
        let length = text.len() as i64;
        let mut end = end as i64;
        // PORT: Go compares `int` values; i64 keeps a negative `end` below the
        // text length as Go does.
        if end - pos as i64 > 0 && end <= self.file_text.len() as i64 {
            // pos includes leading trivia, but we can usually infer the actual start of the
            // string from the kind and end
            let mut end_offset: i64 = 0;
            if kind == SyntaxKind::StringLiteral
                || kind == SyntaxKind::TemplateTail
                || kind == SyntaxKind::NoSubstitutionTemplateLiteral
            {
                end_offset = 1;
            }
            end -= end_offset;
            let start = end - length;
            // PORT: Go `t.fileText[start:end]` panics when `start` is negative;
            // the `usize` conversion makes the Rust slice panic too.
            let file_slice = &self.file_text.as_bytes()[start as usize..end as usize];
            if file_slice == text.as_bytes() {
                self.offsets.push(start as u32);
                self.offsets.push(end as u32);
                return index;
            }
        }
        // no exact match, so we need to add it to the string table
        let offset = self.file_text.len() + self.other_strings.len();
        self.other_strings.push_str(text);
        self.offsets.push(offset as u32);
        self.offsets.push((offset + length as usize) as u32);
        index
    }

    // Go: api/encoder/stringtable.go:54 (*stringTable).encode
    pub fn encode(&self) -> Vec<u8> {
        let mut result = Vec::with_capacity(self.encoded_length());
        append_uint32s(&mut result, &self.offsets);
        result.extend_from_slice(self.file_text.as_bytes());
        result.extend_from_slice(self.other_strings.as_bytes());
        result
    }

    // Go: api/encoder/stringtable.go:62 (*stringTable).stringLength
    pub fn string_length(&self) -> usize {
        self.file_text.len() + self.other_strings.len()
    }

    // Go: api/encoder/stringtable.go:66 (*stringTable).encodedLength
    pub fn encoded_length(&self) -> usize {
        self.offsets.len() * 4 + self.file_text.len() + self.other_strings.len()
    }
}
