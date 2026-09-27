//! Go `printer/textwriter.go`: the multi-line `EmitTextWriter`.

use crate::prelude::*;

/// Go `printer.textWriter`.
// Go: printer/textwriter.go:14 textWriter
#[derive(Clone, Debug, Default)]
pub struct TextWriter {
    new_line: String,
    indent_size: i32,
    builder: String,
    // PORT: Go keeps `lastWritten string`; its only reader is
    // `HasTrailingWhitespace`, which decodes the last rune. This keeps that
    // rune (`None` for ""), so a write does not copy the text.
    last_char: Option<char>,
    indent: i32,
    line_start: bool,
    line_count: i32,
    line_pos: i32,
    has_trailing_comment_state: bool,
    // PORT: not in Go. True when `builder[line_pos..]` has a byte >= 0x80.
    // When false, `get_column` is the byte count with no scan.
    line_non_ascii: bool,
}

impl TextWriter {
    // Go: printer/textwriter.go:97 updateLineCountAndPosFor
    // `s` is the text that the caller just pushed to `builder`.
    fn update_line_count_and_pos_for(&mut self, s: &str) {
        // PORT: Go counts the values of `core.ComputeECMALineStartsSeq(s)`
        // and keeps the last one. `scan_line_breaks` gives the same count
        // (minus 1) and last value in one scan with no Vec.
        let (breaks, last_line_start) = scan_line_breaks(s);

        if breaks > 0 {
            self.line_count += breaks;
            let cur_len = self.builder.len() as i32;
            self.line_pos = cur_len - s.len() as i32 + last_line_start;
            self.line_start = (self.line_pos - cur_len) == 0;
            // The text after `line_pos` is now the last line of `s`.
            self.line_non_ascii = !s.as_bytes()[last_line_start as usize..].is_ascii();
            return;
        }
        self.line_non_ascii = self.line_non_ascii || !s.is_ascii();
        self.line_start = false;
    }

    // Go: printer/textwriter.go:131 writeText
    fn write_text(&mut self, s: &str) {
        if !s.is_empty() {
            if self.line_start {
                self.push_indent();
                self.line_start = false;
            }
            self.builder.push_str(s);
            self.last_char = s.chars().next_back();
            self.update_line_count_and_pos_for(s);
        }
    }

    // PORT: Go `w.builder.WriteString(getIndentString(w.indent, w.indentSize))`.
    // This pushes the same spaces from a static string, with no allocation.
    fn push_indent(&mut self) {
        // 64 spaces.
        const SPACES: &str = "                                                                ";
        // Go `strings.Repeat` panics on a negative count.
        let mut n = usize::try_from(self.indent * self.indent_size)
            .expect("strings: negative Repeat count");
        while n > 0 {
            let k = n.min(SPACES.len());
            self.builder.push_str(&SPACES[..k]);
            n -= k;
        }
    }

    // Go: printer/textwriter.go:161 writeLineRaw
    fn write_line_raw(&mut self) {
        self.builder.push_str(&self.new_line);
        self.last_char = self.new_line.chars().next_back();
        self.line_count += 1;
        self.line_pos = self.builder.len() as i32;
        self.line_non_ascii = false;
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

    // Go: printer/textwriter.go:30 Grow
    fn grow(&mut self, n: i32) {
        // Go `strings.Builder.Grow` panics on a negative count.
        self.builder
            .reserve(usize::try_from(n).expect("strings.Builder.Grow: negative count"));
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
        // PORT: `line_non_ascii` says if the line has a byte >= 0x80, so the
        // ASCII case needs no scan. The Go-string marker is not ASCII.
        if !self.line_non_ascii {
            let column = self.builder.len() as i32 - self.line_pos;
            debug_assert_eq!(column, utf16_len(&self.builder[self.line_pos as usize..]));
            return column;
        }
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

    // PORT: not in Go (see the trait). Moves the text out instead of a copy.
    fn take_string(&mut self) -> String {
        let text = std::mem::take(&mut self.builder);
        self.clear();
        text
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
        match self.last_char {
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
            self.last_char = s.chars().next_back();
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
// PORT: `TextWriter` writes its indent with `push_indent`; other callers use this.
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

// PORT: not a Go function. Go code in package printer writes the struct
// literal `textWriter{newLine: newLine, indentSize: indentSize}` (for example
// `NewChangeTrackerWriter`). The fields are private to this file, so this
// builds that literal. Unlike `new_text_writer`, it keeps an indent size of 0
// and does not call `clear`.
#[must_use]
pub(crate) fn new_text_writer_literal(new_line: &str, indent_size: i32) -> TextWriter {
    TextWriter {
        new_line: new_line.to_string(),
        indent_size,
        ..TextWriter::default()
    }
}

/// PORT: not a Go function. Counts the ECMAScript line breaks in `s` and
/// finds the start of its last line (0 when there is no break). It uses the
/// rules of `compute_ecma_line_starts` (`\n`, `\r`, `\r\n` as one break,
/// U+2028, U+2029): the count is that Vec's length minus 1 and the start is
/// its last value.
fn scan_line_breaks(s: &str) -> (i32, i32) {
    let bytes = s.as_bytes();
    let mut breaks = 0;
    let mut line_start = 0usize;
    // U+2028 is E2 80 A8 and U+2029 is E2 80 A9. 0xE2 is never a UTF-8
    // continuation byte, so each hit starts a char.
    for i in memchr::memchr3_iter(b'\n', b'\r', 0xE2, bytes) {
        if i < line_start {
            // The `\n` of a `\r\n` pair, which the `\r` already counted.
            continue;
        }
        let next = match bytes[i] {
            b'\n' => i + 1,
            b'\r' if bytes.get(i + 1) == Some(&b'\n') => i + 2,
            b'\r' => i + 1,
            _ if bytes.get(i + 1) == Some(&0x80)
                && matches!(bytes.get(i + 2), Some(0xA8 | 0xA9)) =>
            {
                i + 3
            }
            _ => continue,
        };
        breaks += 1;
        line_start = next;
    }
    (breaks, line_start as i32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scan_line_breaks_matches_compute_ecma_line_starts() {
        for s in [
            "",
            "abc",
            "a\r\nb",
            "a\rb",
            "a\r",
            "\r\n\r\n",
            "\n\r",
            "a\u{2028}b\u{2029}c",
            "\u{2028}",
            "caf\u{e9} \u{2020}\u{2030}\u{20ac}\u{1f600}",
            "x\r\ny\rz\u{2029}\u{e9}\n\u{2028}end\r\n",
        ] {
            let starts = compute_ecma_line_starts(s);
            let expected = (starts.len() as i32 - 1, *starts.last().unwrap());
            assert_eq!(scan_line_breaks(s), expected, "{s:?}");
        }
    }
}
