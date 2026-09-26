//! Go `printer/singlelinestringwriter.go`: the `EmitTextWriter` that writes a
//! line break as one space.

use crate::prelude::*;

/// Go `printer.singleLineStringWriter`.
// Go: printer/singlelinestringwriter.go:29 singleLineStringWriter
#[derive(Clone, Debug, Default)]
pub struct SingleLineStringWriter {
    builder: String,
    last_written: String,
}

// Go: printer/singlelinestringwriter.go:21 GetSingleLineStringWriter
// PORT: Go takes a writer from a `sync.Pool` and returns a release function
// that puts it back. There is no pool here: this returns a new cleared writer
// that the caller owns, and nothing needs to be released.
#[must_use]
pub fn get_single_line_string_writer() -> SingleLineStringWriter {
    let mut w = SingleLineStringWriter::default();
    w.clear();
    w
}

impl EmitTextWriter for SingleLineStringWriter {
    // Go: printer/singlelinestringwriter.go:34 Clear
    fn clear(&mut self) {
        self.last_written = String::new();
        self.builder.clear();
    }

    // Go: printer/singlelinestringwriter.go:39 DecreaseIndent
    fn decrease_indent(&mut self) {
        // Do Nothing
    }

    // Go: printer/singlelinestringwriter.go:43 GetColumn
    fn get_column(&self) -> i32 {
        0
    }

    // Go: printer/singlelinestringwriter.go:47 GetIndent
    fn get_indent(&self) -> i32 {
        0
    }

    // Go: printer/singlelinestringwriter.go:51 GetLine
    fn get_line(&self) -> i32 {
        0
    }

    // Go: printer/singlelinestringwriter.go:55 String
    fn string(&self) -> String {
        self.builder.clone()
    }

    // Go: printer/singlelinestringwriter.go:59 GetTextPos
    fn get_text_pos(&self) -> i32 {
        self.builder.len() as i32
    }

    // Go: printer/singlelinestringwriter.go:63 HasTrailingComment
    fn has_trailing_comment(&self) -> bool {
        false
    }

    // Go: printer/singlelinestringwriter.go:67 HasTrailingWhitespace
    fn has_trailing_whitespace(&self) -> bool {
        if self.builder.is_empty() {
            return false;
        }
        // PORT: Go `utf8.DecodeLastRuneInString` returns `RuneError` for an
        // empty string; `None` stands for that case.
        match self.last_written.chars().next_back() {
            None | Some(char::REPLACEMENT_CHARACTER) => false,
            Some(ch) => is_white_space_like(ch),
        }
    }

    // Go: printer/singlelinestringwriter.go:78 IncreaseIndent
    fn increase_indent(&mut self) {
        // Do Nothing
    }

    // Go: printer/singlelinestringwriter.go:82 IsAtStartOfLine
    fn is_at_start_of_line(&self) -> bool {
        false
    }

    // Go: printer/singlelinestringwriter.go:86 RawWrite
    fn raw_write(&mut self, s: &str) {
        self.last_written = s.to_string();
        self.builder.push_str(s);
    }

    // Go: printer/singlelinestringwriter.go:91 Write
    fn write(&mut self, s: &str) {
        self.last_written = s.to_string();
        self.builder.push_str(s);
    }

    // Go: printer/singlelinestringwriter.go:96 WriteComment
    fn write_comment(&mut self, text: &str) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    // Go: printer/singlelinestringwriter.go:101 WriteKeyword
    fn write_keyword(&mut self, text: &str) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    // Go: printer/singlelinestringwriter.go:106 WriteLine
    fn write_line(&mut self) {
        self.last_written = " ".to_string();
        self.builder.push(' ');
    }

    // Go: printer/singlelinestringwriter.go:111 WriteLineForce
    fn write_line_force(&mut self, force: bool) {
        self.last_written = " ".to_string();
        self.builder.push(' ');
    }

    // Go: printer/singlelinestringwriter.go:116 WriteLiteral
    fn write_literal(&mut self, s: &str) {
        self.last_written = s.to_string();
        self.builder.push_str(s);
    }

    // Go: printer/singlelinestringwriter.go:121 WriteOperator
    fn write_operator(&mut self, text: &str) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    // Go: printer/singlelinestringwriter.go:126 WriteParameter
    fn write_parameter(&mut self, text: &str) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    // Go: printer/singlelinestringwriter.go:131 WriteProperty
    fn write_property(&mut self, text: &str) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    // Go: printer/singlelinestringwriter.go:136 WritePunctuation
    fn write_punctuation(&mut self, text: &str) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    // Go: printer/singlelinestringwriter.go:141 WriteSpace
    fn write_space(&mut self, text: &str) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    // Go: printer/singlelinestringwriter.go:146 WriteStringLiteral
    fn write_string_literal(&mut self, text: &str) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    // Go: printer/singlelinestringwriter.go:151 WriteSymbol
    fn write_symbol(&mut self, text: &str, symbol: SymbolId) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }

    // Go: printer/singlelinestringwriter.go:156 WriteTrailingSemicolon
    fn write_trailing_semicolon(&mut self, text: &str) {
        self.last_written = text.to_string();
        self.builder.push_str(text);
    }
}
