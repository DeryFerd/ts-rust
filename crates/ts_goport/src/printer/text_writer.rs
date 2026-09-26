//! Go `printer/textwriter.go`: the multi-line `EmitTextWriter`.

use crate::prelude::*;

/// Go `printer.textWriter`.
// Go: printer/textwriter.go:14 textWriter
#[derive(Clone, Debug, Default)]
pub struct TextWriter {
    new_line: String,
    indent_size: i32,
    builder: String,
    last_written: String,
    indent: i32,
    line_start: bool,
    line_count: i32,
    line_pos: i32,
    has_trailing_comment_state: bool,
}

impl TextWriter {
    // Go: printer/textwriter.go:30 Grow
    pub fn grow(&mut self, n: i32) {
        // Go `strings.Builder.Grow` panics on a negative count.
        self.builder
            .reserve(usize::try_from(n).expect("strings.Builder.Grow: negative count"));
    }

    // Go: printer/textwriter.go:97 updateLineCountAndPosFor
    fn update_line_count_and_pos_for(&mut self, s: &str) {
        // PORT: Go iterates `core.ComputeECMALineStartsSeq(s)`; the Vec from
        // `compute_ecma_line_starts` yields the same values in the same order.
        let line_starts = compute_ecma_line_starts(s);
        let count = line_starts.len() as i32;
        let last_line_start = line_starts.last().copied().unwrap_or(0);

        if count > 1 {
            self.line_count += count - 1;
            let cur_len = self.builder.len() as i32;
            self.line_pos = cur_len - s.len() as i32 + last_line_start;
            self.line_start = (self.line_pos - cur_len) == 0;
            return;
        }
        self.line_start = false;
    }

    // Go: printer/textwriter.go:131 writeText
    fn write_text(&mut self, s: &str) {
        if !s.is_empty() {
            if self.line_start {
                self.builder
                    .push_str(&get_indent_string(self.indent, self.indent_size));
                self.line_start = false;
            }
            self.builder.push_str(s);
            self.last_written = s.to_string();
            self.update_line_count_and_pos_for(s);
        }
    }

    // Go: printer/textwriter.go:161 writeLineRaw
    fn write_line_raw(&mut self) {
        self.builder.push_str(&self.new_line);
        self.last_written = self.new_line.clone();
        self.line_count += 1;
        self.line_pos = self.builder.len() as i32;
        self.line_start = true;
        self.has_trailing_comment_state = false;
    }
}

impl EmitTextWriter for TextWriter {
    // Go: printer/textwriter.go:26 Clear
    fn clear(&mut self) {
        *self = TextWriter {
            new_line: std::mem::take(&mut self.new_line),
            indent_size: self.indent_size,
            line_start: true,
            ..TextWriter::default()
        };
    }

    // Go: printer/textwriter.go:34 DecreaseIndent
    fn decrease_indent(&mut self) {
        self.indent -= 1;
    }

    // Go: printer/textwriter.go:40 GetColumn
    // GetColumn returns the column position measured in UTF-16 code units
    // for source map compatibility.
    fn get_column(&self) -> i32 {
        if self.line_start {
            return self.indent * self.indent_size;
        }
        // Count UTF-16 code units from the last line start.
        // For ASCII-only output (the common case), this equals the byte count.
        utf16_len(&self.builder[self.line_pos as usize..])
    }

    // Go: printer/textwriter.go:49 GetIndent
    fn get_indent(&self) -> i32 {
        self.indent
    }

    // Go: printer/textwriter.go:53 GetLine
    fn get_line(&self) -> i32 {
        self.line_count
    }

    // Go: printer/textwriter.go:57 String
    fn string(&self) -> String {
        self.builder.clone()
    }

    // Go: printer/textwriter.go:61 GetTextPos
    fn get_text_pos(&self) -> i32 {
        self.builder.len() as i32
    }

    // Go: printer/textwriter.go:65 HasTrailingComment
    fn has_trailing_comment(&self) -> bool {
        self.has_trailing_comment_state
    }

    // Go: printer/textwriter.go:69 HasTrailingWhitespace
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

    // Go: printer/textwriter.go:80 IncreaseIndent
    fn increase_indent(&mut self) {
        self.indent += 1;
    }

    // Go: printer/textwriter.go:84 IsAtStartOfLine
    fn is_at_start_of_line(&self) -> bool {
        self.line_start
    }

    // Go: printer/textwriter.go:88 RawWrite
    fn raw_write(&mut self, s: &str) {
        if !s.is_empty() {
            self.builder.push_str(s);
            self.last_written = s.to_string();
            self.has_trailing_comment_state = false;
        }
        self.update_line_count_and_pos_for(s);
    }

    // Go: printer/textwriter.go:143 Write
    fn write(&mut self, s: &str) {
        if !s.is_empty() {
            self.has_trailing_comment_state = false;
        }
        self.write_text(s);
    }

    // Go: printer/textwriter.go:150 WriteComment
    fn write_comment(&mut self, text: &str) {
        if !text.is_empty() {
            self.has_trailing_comment_state = true;
        }
        self.write_text(text);
    }

    // Go: printer/textwriter.go:157 WriteKeyword
    fn write_keyword(&mut self, text: &str) {
        self.write(text);
    }

    // Go: printer/textwriter.go:170 WriteLine
    fn write_line(&mut self) {
        if !self.line_start {
            self.write_line_raw();
        }
    }

    // Go: printer/textwriter.go:176 WriteLineForce
    fn write_line_force(&mut self, force: bool) {
        if !self.line_start || force {
            self.write_line_raw();
        }
    }

    // Go: printer/textwriter.go:182 WriteLiteral
    fn write_literal(&mut self, s: &str) {
        self.write(s);
    }

    // Go: printer/textwriter.go:186 WriteOperator
    fn write_operator(&mut self, text: &str) {
        self.write(text);
    }

    // Go: printer/textwriter.go:190 WriteParameter
    fn write_parameter(&mut self, text: &str) {
        self.write(text);
    }

    // Go: printer/textwriter.go:194 WriteProperty
    fn write_property(&mut self, text: &str) {
        self.write(text);
    }

    // Go: printer/textwriter.go:198 WritePunctuation
    fn write_punctuation(&mut self, text: &str) {
        self.write(text);
    }

    // Go: printer/textwriter.go:202 WriteSpace
    fn write_space(&mut self, text: &str) {
        self.write(text);
    }

    // Go: printer/textwriter.go:206 WriteStringLiteral
    fn write_string_literal(&mut self, text: &str) {
        self.write(text);
    }

    // Go: printer/textwriter.go:210 WriteSymbol
    fn write_symbol(&mut self, text: &str, symbol: SymbolId) {
        self.write(text);
    }

    // Go: printer/textwriter.go:214 WriteTrailingSemicolon
    fn write_trailing_semicolon(&mut self, text: &str) {
        self.write(text);
    }
}

const DEFAULT_INDENT_SIZE: i32 = 4;

// Go: printer/textwriter.go:119 GetDefaultIndentSize
// GetDefaultIndentSize returns the default indent size (4 spaces) used when no specific indent size is configured.
#[must_use]
pub fn get_default_indent_size() -> i32 {
    DEFAULT_INDENT_SIZE
}

// Go: printer/textwriter.go:123 getIndentString
pub fn get_indent_string(indent: i32, indent_size: i32) -> String {
    if indent == 0 {
        return String::new();
    }
    // TODO: This is cached in tsc - should it be cached here?
    // Go `strings.Repeat` panics on a negative count.
    " ".repeat(usize::try_from(indent * indent_size).expect("strings: negative Repeat count"))
}

// Go: printer/textwriter.go:218 NewTextWriter
// PORT: Go returns the `EmitTextWriter` interface; this returns the concrete
// writer, which callers use as `&mut dyn EmitTextWriter`.
#[must_use]
pub fn new_text_writer(new_line: &str, indent_size: i32) -> TextWriter {
    let indent_size = if indent_size <= 0 { 4 } else { indent_size };
    let mut w = TextWriter::default();
    w.new_line = new_line.to_string();
    w.indent_size = indent_size;
    w.clear();
    w
}
