//! Port of `scanner/scanner.go` lines 1237 to 2226: JSX and JSDoc scans,
//! identifiers, escapes, numbers and strings. Unit U2. The `Scanner` struct,
//! its state and the low-level character helpers (`char`, `char_at`,
//! `char_and_size`, `scan_ascii_while`, `error`, `error_at`, `scan`) are in
//! `scanner_p1.rs` (unit U1).
//!
//! Runes follow scanner_p1.rs: Go `rune` is `i32`, and `rune_to_char` maps
//! one to a `char` for the `stringutil` predicates. The token value is set
//! through `set_token_value` (interned `&'static str`, see scanner_p1.rs).

use crate::frontend::prelude::*;

use super::scanner_p1::{
    intern_token_value, rune_to_char, rune_to_string, utf8_decode_last_rune_in_string, utf8_decode_rune_in_string,
    EscapeSequenceScanningFlags, Scanner, RUNE_SELF,
};

/// Go `strconv.ParseInt(s, base, bitSize)` with the error ignored, as the
/// scanner does. The input holds only digits of `base`.
// PORT: on overflow Go returns the largest value for `bit_size` (and an
// error the scanner drops). This keeps that value. An empty or invalid input
// returns 0, as Go does.
fn go_parse_int(s: &str, base: u32, bit_size: u32) -> i64 {
    let max: i64 = if bit_size >= 64 { i64::MAX } else { (1i64 << (bit_size - 1)) - 1 };
    if s.is_empty() {
        return 0;
    }
    let mut value: i64 = 0;
    for c in s.chars() {
        let Some(digit) = c.to_digit(base) else {
            return 0;
        };
        value = match value.checked_mul(base as i64).and_then(|v| v.checked_add(digit as i64)) {
            Some(v) if v <= max => v,
            _ => return max,
        };
    }
    value
}

/// Go `jsnum.FromString(text).String()`.
fn js_number_string(text: &str) -> String {
    ts_jsnum::Number::from_string(text).to_string()
}

impl Scanner {
    // Go: scanner/scanner.go:1237 ReScanJsxToken
    pub fn re_scan_jsx_token(&mut self, allow_multiline_jsx_text: bool) -> SyntaxKind {
        self.scanner_state.pos = self.scanner_state.full_start_pos;
        self.scanner_state.token_start = self.scanner_state.full_start_pos;
        self.scanner_state.token = self.scan_jsx_token_ex(allow_multiline_jsx_text);
        self.scanner_state.token
    }

    // Go: scanner/scanner.go:1244 ReScanHashToken
    pub fn re_scan_hash_token(&mut self) -> SyntaxKind {
        if self.scanner_state.token == SyntaxKind::PrivateIdentifier {
            self.scanner_state.pos = self.scanner_state.token_start + 1;
            self.scanner_state.token = SyntaxKind::HashToken;
        }
        self.scanner_state.token
    }

    // Go: scanner/scanner.go:1252 ReScanQuestionToken
    pub fn re_scan_question_token(&mut self) -> SyntaxKind {
        if self.scanner_state.token != SyntaxKind::QuestionQuestionToken {
            panic!("'reScanQuestionToken' should only be called on a '??'");
        }
        self.scanner_state.pos = self.scanner_state.token_start + 1;
        self.scanner_state.token = SyntaxKind::QuestionToken;
        self.scanner_state.token
    }

    // Go: scanner/scanner.go:1261 ScanJsxToken
    pub fn scan_jsx_token(&mut self) -> SyntaxKind {
        self.scan_jsx_token_ex(true /*allowMultilineJsxText*/)
    }

    // Go: scanner/scanner.go:1265 ScanJsxTokenEx
    pub fn scan_jsx_token_ex(&mut self, allow_multiline_jsx_text: bool) -> SyntaxKind {
        self.scanner_state.full_start_pos = self.scanner_state.pos;
        self.scanner_state.token_start = self.scanner_state.pos;
        let ch = self.char();
        if ch < 0 {
            self.scanner_state.token = SyntaxKind::EndOfFile;
        } else if ch == '<' as i32 {
            if self.char_at(1) == '/' as i32 {
                self.scanner_state.pos += 2;
                self.scanner_state.token = SyntaxKind::LessThanSlashToken;
            } else {
                self.scanner_state.pos += 1;
                self.scanner_state.token = SyntaxKind::LessThanToken;
            }
        } else if ch == '{' as i32 {
            self.scanner_state.pos += 1;
            self.scanner_state.token = SyntaxKind::OpenBraceToken;
        } else {
            // First non-whitespace character on this line.
            let mut first_non_whitespace: i32 = 0;
            // These initial values are special because the first line is:
            // firstNonWhitespace = 0 to indicate that we want leading whitespace
            loop {
                let (ch, size) = self.char_and_size();
                let ch = rune_to_char(ch);
                if size == 0 || ch == '{' {
                    break;
                }
                if ch == '<' {
                    if is_conflict_marker_trivia(&self.text, self.scanner_state.pos as usize) {
                        self.scanner_state.pos = self.scan_conflict_marker_trivia_at_pos();
                        self.scanner_state.token = SyntaxKind::ConflictMarkerTrivia;
                        return self.scanner_state.token;
                    }
                    break;
                }
                if ch == '>' {
                    self.error_at(diag::Unexpected_token_Did_you_mean_or_gt, self.scanner_state.pos, 1, Vec::new());
                } else if ch == '}' {
                    self.error_at(diag::Unexpected_token_Did_you_mean_or_rbrace, self.scanner_state.pos, 1, Vec::new());
                }
                // FirstNonWhitespace is 0, then we only see whitespaces so far. If we see a linebreak, we want to ignore that whitespaces.
                // i.e (- : whitespace)
                //      <div>----
                //      </div> becomes <div></div>
                //
                //      <div>----</div> becomes <div>----</div>
                if is_line_break(ch) && first_non_whitespace == 0 {
                    first_non_whitespace = -1;
                } else if !allow_multiline_jsx_text && is_line_break(ch) && first_non_whitespace > 0 {
                    // Stop JsxText on each line during formatting. This allows the formatter to
                    // indent each line correctly.
                    break;
                } else if !is_white_space_like(ch) {
                    first_non_whitespace = self.scanner_state.pos;
                }
                self.scanner_state.pos += size;
            }
            self.scanner_state.token_value =
                intern_token_value(&self.text[self.scanner_state.full_start_pos as usize..self.scanner_state.pos as usize]);
            self.scanner_state.token = SyntaxKind::JsxText;
            if first_non_whitespace == -1 {
                self.scanner_state.token = SyntaxKind::JsxTextAllWhiteSpaces;
            }
        }
        self.scanner_state.token
    }

    // Go: scanner/scanner.go:1333 ScanJsxIdentifier
    // Scans a JSX identifier; these differ from normal identifiers in that they allow dashes
    pub fn scan_jsx_identifier(&mut self) -> SyntaxKind {
        // PORT: Go `tokenIsIdentifierOrKeyword` from scanner/utilities.go is
        // private there; this uses the same pub function from the prelude
        // (checker/utilities_p1.rs).
        if token_is_identifier_or_keyword(self.scanner_state.token) {
            // An identifier or keyword has already been parsed - check for a `-` or a single instance of `:` and then append it and
            // everything after it to the token
            // Do note that this means that `scanJsxIdentifier` effectively _mutates_ the visible token without advancing to a new token
            // Any caller should be expecting this behavior and should only read the pos or token value after calling it.
            loop {
                let ch = self.char();
                if ch < 0 {
                    break;
                }
                if ch == '-' as i32 {
                    let value = format!("{}-", self.scanner_state.token_value);
                    self.set_token_value(&value);
                    self.scanner_state.pos += 1;
                    continue;
                }
                let old_pos = self.scanner_state.pos;
                let parts = self.scan_identifier_parts(); // reuse `scanIdentifierParts` so unicode escapes are handled
                let value = format!("{}{}", self.scanner_state.token_value, parts);
                self.set_token_value(&value);
                if self.scanner_state.pos == old_pos {
                    break;
                }
            }
            self.scanner_state.token = get_identifier_token(self.scanner_state.token_value);
        }
        self.scanner_state.token
    }

    // Go: scanner/scanner.go:1360 ScanJsxAttributeValue
    pub fn scan_jsx_attribute_value(&mut self) -> SyntaxKind {
        self.scanner_state.full_start_pos = self.scanner_state.pos;
        // Skip whitespace between '=' and the value so tokenStart lands on the
        // opening quote, not on trivia.
        let (mut ch, mut size) = self.char_and_size();
        while size > 0 && is_white_space_like(rune_to_char(ch)) {
            self.scanner_state.pos += size;
            (ch, size) = self.char_and_size();
        }
        self.scanner_state.token_start = self.scanner_state.pos;
        let c = self.char();
        if c == '"' as i32 || c == '\'' as i32 {
            let value = self.scan_string(true /*jsxAttributeString*/);
            self.set_token_value(&value);
            self.scanner_state.token = SyntaxKind::StringLiteral;
            self.scanner_state.token
        } else {
            // If this scans anything other than `{`, it's a parse error.
            self.scan()
        }
    }

    // Go: scanner/scanner.go:1379 ReScanJsxAttributeValue
    pub fn re_scan_jsx_attribute_value(&mut self) -> SyntaxKind {
        self.scanner_state.pos = self.scanner_state.full_start_pos;
        self.scanner_state.token_start = self.scanner_state.full_start_pos;
        self.scan_jsx_attribute_value()
    }

    // Go: scanner/scanner.go:1386 ScanJSDocCommentTextToken
    /** In addition to the usual JSDoc ast.Kinds, can also return ast.KindJSDocCommentTextToken */
    pub fn scan_js_doc_comment_text_token(&mut self, in_backticks: bool) -> SyntaxKind {
        self.scanner_state.full_start_pos = self.scanner_state.pos;
        self.scanner_state.token_flags = TokenFlags::NONE;
        if self.scanner_state.pos >= self.text.len() as i32 {
            self.scanner_state.token = SyntaxKind::EndOfFile;
            return self.scanner_state.token;
        }
        self.scanner_state.token_start = self.scanner_state.pos;
        let (mut ch, mut size) = self.char_and_size();
        while self.scanner_state.pos < self.text.len() as i32 && !is_line_break(rune_to_char(ch)) && ch != '`' as i32 {
            if !in_backticks {
                if ch == '{' as i32 {
                    break;
                } else if ch == '@' as i32 && self.scanner_state.pos >= 0 {
                    // @ doesn't start a new tag inside ``, and elsewhere, only after whitespace and before identifier
                    let (previous, _) = utf8_decode_last_rune_in_string(&self.text, self.scanner_state.pos as usize);
                    if is_white_space_single_line(rune_to_char(previous)) {
                        let (next, _) = utf8_decode_rune_in_string(&self.text, (self.scanner_state.pos + size) as usize);
                        if is_identifier_start(rune_to_char(next)) {
                            break;
                        }
                    }
                }
            }
            self.scanner_state.pos += size;
            (ch, size) = self.char_and_size();
        }
        if self.scanner_state.pos == self.scanner_state.token_start {
            return self.scan_js_doc_token();
        }
        self.scanner_state.token_value =
            intern_token_value(&self.text[self.scanner_state.token_start as usize..self.scanner_state.pos as usize]);
        self.scanner_state.token = SyntaxKind::JsDocCommentTextToken;
        self.scanner_state.token
    }

    // Go: scanner/scanner.go:1422 CanFollowJSDocAt
    // Peek at the character at the current scanner position (expected to be right after '@')
    // and return true if a JSDoc tag can follow. Identifier starts indicate a tag name.
    // Whitespace, newlines, and EOF are also accepted to support incomplete tags for code completion.
    pub fn can_follow_js_doc_at(&self) -> bool {
        if self.scanner_state.pos >= self.text.len() as i32 {
            return true;
        }
        let (ch, _) = utf8_decode_rune_in_string(&self.text, self.scanner_state.pos as usize);
        let ch = rune_to_char(ch);
        is_identifier_start(ch) || is_white_space_single_line(ch) || is_line_break(ch)
    }

    // Go: scanner/scanner.go:1430 ScanJSDocToken
    pub fn scan_js_doc_token(&mut self) -> SyntaxKind {
        self.scanner_state.full_start_pos = self.scanner_state.pos;
        self.scanner_state.token_flags = TokenFlags::NONE;
        if self.scanner_state.pos >= self.text.len() as i32 {
            self.scanner_state.token = SyntaxKind::EndOfFile;
            return self.scanner_state.token;
        }

        self.scanner_state.token_start = self.scanner_state.pos;
        let (ch, size) = self.char_and_size();
        let ch = rune_to_char(ch);
        self.scanner_state.pos += size;
        match ch {
            '\t' | '\u{000B}' | '\u{000C}' | ' ' => {
                let (mut ch2, mut size2) = self.char_and_size();
                while size2 > 0 && is_white_space_single_line(rune_to_char(ch2)) {
                    self.scanner_state.pos += size2;
                    (ch2, size2) = self.char_and_size();
                }
                self.scanner_state.token = SyntaxKind::WhitespaceTrivia;
                return self.scanner_state.token;
            }
            '@' => {
                self.scanner_state.token = SyntaxKind::AtToken;
                return self.scanner_state.token;
            }
            '\r' | '\n' => {
                if ch == '\r' && self.char() == '\n' as i32 {
                    self.scanner_state.pos += 1;
                }
                // Go: `case '\r'` falls through to `case '\n'`.
                self.scanner_state.token_flags |= TokenFlags::PRECEDING_LINE_BREAK;
                self.scanner_state.token = SyntaxKind::NewLineTrivia;
                return self.scanner_state.token;
            }
            '*' => {
                self.scanner_state.token = SyntaxKind::AsteriskToken;
                return self.scanner_state.token;
            }
            '{' => {
                self.scanner_state.token = SyntaxKind::OpenBraceToken;
                return self.scanner_state.token;
            }
            '}' => {
                self.scanner_state.token = SyntaxKind::CloseBraceToken;
                return self.scanner_state.token;
            }
            '[' => {
                self.scanner_state.token = SyntaxKind::OpenBracketToken;
                return self.scanner_state.token;
            }
            ']' => {
                self.scanner_state.token = SyntaxKind::CloseBracketToken;
                return self.scanner_state.token;
            }
            '(' => {
                self.scanner_state.token = SyntaxKind::OpenParenToken;
                return self.scanner_state.token;
            }
            ')' => {
                self.scanner_state.token = SyntaxKind::CloseParenToken;
                return self.scanner_state.token;
            }
            '<' => {
                self.scanner_state.token = SyntaxKind::LessThanToken;
                return self.scanner_state.token;
            }
            '>' => {
                self.scanner_state.token = SyntaxKind::GreaterThanToken;
                return self.scanner_state.token;
            }
            '=' => {
                self.scanner_state.token = SyntaxKind::EqualsToken;
                return self.scanner_state.token;
            }
            ',' => {
                self.scanner_state.token = SyntaxKind::CommaToken;
                return self.scanner_state.token;
            }
            '.' => {
                self.scanner_state.token = SyntaxKind::DotToken;
                return self.scanner_state.token;
            }
            '`' => {
                self.scanner_state.token = SyntaxKind::BacktickToken;
                return self.scanner_state.token;
            }
            '#' => {
                self.scanner_state.token = SyntaxKind::HashToken;
                return self.scanner_state.token;
            }
            '\\' => {
                self.scanner_state.pos -= 1;
                let cp = self.peek_unicode_escape();
                if cp >= 0 && is_identifier_start(rune_to_char(cp)) {
                    let escaped = self.scan_unicode_escape(true);
                    let parts = self.scan_identifier_parts();
                    let value = rune_to_string(escaped) + &parts;
                    self.set_token_value(&value);
                    self.scanner_state.token = get_identifier_token(self.scanner_state.token_value);
                } else {
                    self.scanner_state.pos += 1;
                    self.scanner_state.token = SyntaxKind::Unknown;
                }
                return self.scanner_state.token;
            }
            _ => {}
        }

        if is_identifier_start(ch) {
            // PORT: Go `char` holds the rune (i32 here); `rune_to_char` feeds the predicate.
            let mut char_ = ch as i32;
            loop {
                if self.scanner_state.pos >= self.text.len() as i32 {
                    break;
                }
                let size;
                (char_, size) = self.char_and_size();
                if !is_identifier_part(rune_to_char(char_)) && char_ != '-' as i32 {
                    break;
                }
                self.scanner_state.pos += size;
            }
            let mut value = self.text[self.scanner_state.token_start as usize..self.scanner_state.pos as usize].to_string();
            if char_ == '\\' as i32 {
                let parts = self.scan_identifier_parts();
                value.push_str(&parts);
            }
            self.set_token_value(&value);
            self.scanner_state.token = get_identifier_token(self.scanner_state.token_value);
            self.scanner_state.token
        } else {
            self.scanner_state.token = SyntaxKind::Unknown;
            self.scanner_state.token
        }
    }

    // Go: scanner/scanner.go:1539 scanIdentifier
    pub(crate) fn scan_identifier(&mut self, prefix_length: i32) -> bool {
        let start = self.scanner_state.pos;
        self.scanner_state.pos += prefix_length;
        let ch = self.char();
        // Fast path for simple ASCII identifiers
        if is_ascii_letter(rune_to_char(ch)) || ch == '_' as i32 || ch == '$' as i32 {
            self.scanner_state.pos += 1;
            self.scan_ascii_while(|b: u8| {
                b.is_ascii_lowercase() || b.is_ascii_uppercase() || b.is_ascii_digit() || b == b'_' || b == b'$'
            });
            let ch = self.char();
            if ch < RUNE_SELF && ch != '\\' as i32 {
                self.scanner_state.token_value = intern_token_value(&self.text[start as usize..self.scanner_state.pos as usize]);
                return true;
            }
            self.scanner_state.pos = start + prefix_length;
        }
        let (mut ch, mut size) = self.char_and_size();
        if is_identifier_start(rune_to_char(ch)) {
            loop {
                self.scanner_state.pos += size;
                (ch, size) = self.char_and_size();
                if !is_identifier_part(rune_to_char(ch)) {
                    break;
                }
            }
            let mut value = self.text[start as usize..self.scanner_state.pos as usize].to_string();
            if ch == '\\' as i32 {
                let parts = self.scan_identifier_parts();
                value.push_str(&parts);
            }
            self.set_token_value(&value);
            return true;
        }
        false
    }

    // Go: scanner/scanner.go:1574 scanIdentifierParts
    pub(crate) fn scan_identifier_parts(&mut self) -> String {
        let mut sb = String::new();
        let mut start = self.scanner_state.pos;
        loop {
            let (ch, size) = self.char_and_size();
            if is_identifier_part(rune_to_char(ch)) {
                self.scanner_state.pos += size;
                continue;
            }
            if ch == '\\' as i32 {
                let escaped = self.peek_unicode_escape();
                if escaped >= 0 && is_identifier_part(rune_to_char(escaped)) {
                    sb.push_str(&self.text[start as usize..self.scanner_state.pos as usize]);
                    let r = self.scan_unicode_escape(true);
                    sb.push_str(&rune_to_string(r));
                    start = self.scanner_state.pos;
                    continue;
                }
            }
            break;
        }
        sb.push_str(&self.text[start as usize..self.scanner_state.pos as usize]);
        sb
    }

    // Go: scanner/scanner.go:1598 scanString
    pub(crate) fn scan_string(&mut self, jsx_attribute_string: bool) -> String {
        let quote = self.char();
        if quote == '\'' as i32 {
            self.scanner_state.token_flags |= TokenFlags::SINGLE_QUOTE;
        }
        self.scanner_state.pos += 1;
        // Fast path for simple strings without escape sequences.
        let str_len: i32 = self.text.as_bytes()[self.scanner_state.pos as usize..]
            .iter()
            .position(|&b| b as i32 == quote)
            .map_or(-1, |i| i as i32);
        if str_len == 0 {
            self.scanner_state.pos += 1;
            return String::new();
        }
        if str_len > 0 {
            let str = &self.text[self.scanner_state.pos as usize..(self.scanner_state.pos + str_len) as usize];
            if jsx_attribute_string || !str.contains('\\') && !str.contains('\r') && !str.contains('\n') {
                self.scanner_state.pos += str_len + 1;
                return str.to_string();
            }
        }
        let mut sb = String::new();
        let mut start = self.scanner_state.pos;
        loop {
            let ch = self.char();
            if ch < 0 {
                sb.push_str(&self.text[start as usize..self.scanner_state.pos as usize]);
                self.scanner_state.token_flags |= TokenFlags::UNTERMINATED;
                self.error(diag::Unterminated_string_literal);
                break;
            }
            if ch == quote {
                sb.push_str(&self.text[start as usize..self.scanner_state.pos as usize]);
                self.scanner_state.pos += 1;
                break;
            }
            if ch == '\\' as i32 && !jsx_attribute_string {
                sb.push_str(&self.text[start as usize..self.scanner_state.pos as usize]);
                let escaped = self.scan_escape_sequence(
                    EscapeSequenceScanningFlags::STRING | EscapeSequenceScanningFlags::REPORT_ERRORS,
                );
                sb.push_str(&escaped);
                start = self.scanner_state.pos;
                continue;
            }
            if (ch == '\n' as i32 || ch == '\r' as i32) && !jsx_attribute_string {
                sb.push_str(&self.text[start as usize..self.scanner_state.pos as usize]);
                self.scanner_state.token_flags |= TokenFlags::UNTERMINATED;
                self.error(diag::Unterminated_string_literal);
                break;
            }
            self.scanner_state.pos += 1;
        }
        sb
    }

    // Go: scanner/scanner.go:1650 scanTemplateAndSetTokenValue
    pub(crate) fn scan_template_and_set_token_value(&mut self, should_emit_invalid_escape_error: bool) -> SyntaxKind {
        let started_with_backtick = self.char() == '`' as i32;
        self.scanner_state.pos += 1;
        let mut start = self.scanner_state.pos;
        let mut parts: Vec<String> = Vec::with_capacity(4);
        let token;
        loop {
            self.scan_ascii_while(|b: u8| b != b'`' && b != b'$' && b != b'\\' && b != b'\r');
            let ch = self.char();
            if ch < 0 || ch == '`' as i32 {
                parts.push(self.text[start as usize..self.scanner_state.pos as usize].to_string());
                if ch == '`' as i32 {
                    self.scanner_state.pos += 1;
                } else {
                    self.scanner_state.token_flags |= TokenFlags::UNTERMINATED;
                    self.error(diag::Unterminated_template_literal);
                }
                token = if started_with_backtick {
                    SyntaxKind::NoSubstitutionTemplateLiteral
                } else {
                    SyntaxKind::TemplateTail
                };
                break;
            }
            if ch == '$' as i32 && self.char_at(1) == '{' as i32 {
                parts.push(self.text[start as usize..self.scanner_state.pos as usize].to_string());
                self.scanner_state.pos += 2;
                token = if started_with_backtick { SyntaxKind::TemplateHead } else { SyntaxKind::TemplateMiddle };
                break;
            }
            if ch == '\\' as i32 {
                parts.push(self.text[start as usize..self.scanner_state.pos as usize].to_string());
                let flags = EscapeSequenceScanningFlags::STRING
                    | if should_emit_invalid_escape_error {
                        EscapeSequenceScanningFlags::REPORT_ERRORS
                    } else {
                        EscapeSequenceScanningFlags::default()
                    };
                parts.push(self.scan_escape_sequence(flags));
                start = self.scanner_state.pos;
                continue;
            }
            // Speculated ECMAScript 6 Spec 11.8.6.1:
            // <CR><LF> and <CR> LineTerminatorSequences are normalized to <LF> for Template Values
            if ch == '\r' as i32 {
                parts.push(self.text[start as usize..self.scanner_state.pos as usize].to_string());
                self.scanner_state.pos += 1;
                if self.char() == '\n' as i32 {
                    self.scanner_state.pos += 1;
                }
                parts.push("\n".to_string());
                start = self.scanner_state.pos;
                continue;
            }
            self.scanner_state.pos += 1;
        }
        self.set_token_value(&parts.join(""));
        token
    }

    // Go: scanner/scanner.go:1702 scanEscapeSequence
    // PORT: Go returns strings that can hold a CESU-8 lone surrogate
    // (`EncodeJSStringRune`). A Rust `String` cannot; `encode_js_string_rune`
    // writes U+FFFD instead (see its PORT note in scanner_util.rs).
    pub(crate) fn scan_escape_sequence(&mut self, flags: EscapeSequenceScanningFlags) -> String {
        let start = self.scanner_state.pos;
        self.scanner_state.pos += 1;
        let ch = self.char();
        if ch < 0 {
            self.error(diag::Unexpected_end_of_text);
            return String::new();
        }
        self.scanner_state.pos += 1;
        // PORT: the Go `switch` with `fallthrough` from '0' to '1'..'3' to
        // '4'..'7' becomes one arm with the same checks in order.
        let c = rune_to_char(ch);
        match c {
            '0'..='7' => {
                // Although '0' preceding any digit is treated as LegacyOctalEscapeSequence,
                // '\08' should separately be interpreted as '\0' + '8'.
                if c == '0' && !is_digit(rune_to_char(self.char())) {
                    return "\x00".to_string();
                }
                // '\01', '\011'
                if c <= '3' {
                    // '\1', '\17', '\177'
                    if is_octal_digit(rune_to_char(self.char())) {
                        self.scanner_state.pos += 1;
                    }
                    // '\17', '\177'
                }
                // '\4', '\47' but not '\477'
                if is_octal_digit(rune_to_char(self.char())) {
                    self.scanner_state.pos += 1;
                }
                // '\47'
                self.scanner_state.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                if flags.intersects(EscapeSequenceScanningFlags::REPORT_INVALID_ESCAPE_ERRORS) {
                    let code = go_parse_int(&self.text[(start + 1) as usize..self.scanner_state.pos as usize], 8, 32);
                    if flags.intersects(EscapeSequenceScanningFlags::REGULAR_EXPRESSION)
                        && !flags.intersects(EscapeSequenceScanningFlags::ATOM_ESCAPE)
                        && c != '0'
                    {
                        self.error_at(diag::Octal_escape_sequences_and_backreferences_are_not_allowed_in_a_character_class_If_this_was_intended_as_an_escape_sequence_use_the_syntax_0_instead, start, self.scanner_state.pos - start, args![format!("\\x{:02x}", code)]);
                    } else {
                        self.error_at(
                            diag::Octal_escape_sequences_are_not_allowed_Use_the_syntax_0,
                            start,
                            self.scanner_state.pos - start,
                            args![format!("\\x{:02x}", code)],
                        );
                    }
                    return rune_to_string(code as i32);
                }
                self.text[start as usize..self.scanner_state.pos as usize].to_string()
            }
            '8' | '9' => {
                // the invalid '\8' and '\9'
                self.scanner_state.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                if flags.intersects(EscapeSequenceScanningFlags::REPORT_INVALID_ESCAPE_ERRORS) {
                    if flags.intersects(EscapeSequenceScanningFlags::REGULAR_EXPRESSION)
                        && !flags.intersects(EscapeSequenceScanningFlags::ATOM_ESCAPE)
                    {
                        self.error_at(
                            diag::Decimal_escape_sequences_and_backreferences_are_not_allowed_in_a_character_class,
                            start,
                            self.scanner_state.pos - start,
                            Vec::new(),
                        );
                    } else {
                        self.error_at(
                            diag::Escape_sequence_0_is_not_allowed,
                            start,
                            self.scanner_state.pos - start,
                            args![&self.text[start as usize..self.scanner_state.pos as usize]],
                        );
                    }
                    return c.to_string();
                }
                self.text[start as usize..self.scanner_state.pos as usize].to_string()
            }
            'b' => "\u{0008}".to_string(),
            't' => "\t".to_string(),
            'n' => "\n".to_string(),
            'v' => "\u{000B}".to_string(),
            'f' => "\u{000C}".to_string(),
            'r' => "\r".to_string(),
            '\'' => "'".to_string(),
            '"' => "\"".to_string(),
            'u' => {
                // '\uDDDD' and '\u{DDDDDD}'
                let extended = self.char() == '{' as i32;
                self.scanner_state.pos -= 2;
                let code_point =
                    self.scan_unicode_escape(flags.intersects(EscapeSequenceScanningFlags::REPORT_INVALID_ESCAPE_ERRORS));
                if extended {
                    if !flags.intersects(EscapeSequenceScanningFlags::ALLOW_EXTENDED_UNICODE_ESCAPE) {
                        self.scanner_state.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                        if flags.intersects(EscapeSequenceScanningFlags::REPORT_INVALID_ESCAPE_ERRORS) {
                            self.error_at(diag::Unicode_escape_sequences_are_only_available_when_the_Unicode_u_flag_or_the_Unicode_Sets_v_flag_is_set, start, self.scanner_state.pos - start, Vec::new());
                        }
                    }
                    if code_point < 0 {
                        return self.text[start as usize..self.scanner_state.pos as usize].to_string();
                    }
                    // In string literals, a high surrogate \u{...} followed by a low
                    // surrogate escape forms a single code point, exactly as adjacent
                    // UTF-16 code units would in a JavaScript string.
                    if !flags.intersects(EscapeSequenceScanningFlags::REGULAR_EXPRESSION)
                        && is_high_surrogate(code_point as u32)
                    {
                        if let Some(combined) = self.scan_low_surrogate_escape(code_point) {
                            return rune_to_string(combined);
                        }
                    }
                    return encode_js_string_rune(code_point as u32);
                }
                if code_point < 0 {
                    return self.text[start as usize..self.scanner_state.pos as usize].to_string();
                } else if is_high_surrogate(code_point as u32) {
                    if !flags.intersects(EscapeSequenceScanningFlags::REGULAR_EXPRESSION) {
                        // Combine \uHigh followed by any low surrogate escape (\uLow or
                        // \u{Low}) into a single code point in string literals, matching
                        // how adjacent UTF-16 code units pair in a JavaScript string.
                        if let Some(combined) = self.scan_low_surrogate_escape(code_point) {
                            return rune_to_string(combined);
                        }
                    } else if flags.intersects(EscapeSequenceScanningFlags::ANY_UNICODE_MODE)
                        && self.char() == '\\' as i32
                        && self.char_at(1) == 'u' as i32
                        && self.char_at(2) != '{' as i32
                    {
                        // In regex AnyUnicodeMode, combine \uHigh\uLow so scanClassRanges
                        // can compare the pair numerically. In non-unicode regex mode they
                        // are separate atoms, and extended \u{...} escapes never combine.
                        let saved_pos = self.scanner_state.pos;
                        let next_code_point = self
                            .scan_unicode_escape(flags.intersects(EscapeSequenceScanningFlags::REPORT_INVALID_ESCAPE_ERRORS));
                        if next_code_point >= 0 && is_low_surrogate(next_code_point as u32) {
                            return rune_to_string(
                                surrogate_pair_to_code_point(code_point as u32, next_code_point as u32) as i32,
                            );
                        }
                        self.scanner_state.pos = saved_pos;
                    }
                }
                // Lone surrogate: encode as CESU-8 so it survives losslessly. In a
                // non-unicode regex this also lets scanClassRanges compare it numerically.
                encode_js_string_rune(code_point as u32)
            }
            'x' => {
                // '\xDD'
                while self.scanner_state.pos < start + 4 {
                    if !is_hex_digit(rune_to_char(self.char())) {
                        self.scanner_state.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                        if flags.intersects(EscapeSequenceScanningFlags::REPORT_INVALID_ESCAPE_ERRORS) {
                            self.error(diag::Hexadecimal_digit_expected);
                        }
                        return self.text[start as usize..self.scanner_state.pos as usize].to_string();
                    }
                    self.scanner_state.pos += 1;
                }
                self.scanner_state.token_flags |= TokenFlags::HEX_ESCAPE;
                let escaped_value = go_parse_int(&self.text[(start + 2) as usize..self.scanner_state.pos as usize], 16, 32);
                rune_to_string(escaped_value as i32)
            }
            '\r' | '\n' => {
                // when encountering a LineContinuation (i.e. a backslash and a line terminator sequence),
                // the line terminator is interpreted to be "the empty code unit sequence".
                if c == '\r' && self.char() == '\n' as i32 {
                    self.scanner_state.pos += 1;
                }
                // Go: `case '\r'` falls through to `case '\n'`.
                String::new()
            }
            _ => {
                // ch was read as a single byte; for multi-byte UTF-8 characters,
                // we need to decode the full rune and advance past all its bytes.
                let mut c = c;
                if ch >= RUNE_SELF {
                    self.scanner_state.pos -= 1; // back up past the single-byte advance
                    let (r, size) = utf8_decode_rune_in_string(&self.text, self.scanner_state.pos as usize);
                    c = rune_to_char(r);
                    self.scanner_state.pos += size;
                    self.contains_non_ascii = true;
                }
                // LineContinuation: a backslash followed by a line terminator is "the empty code unit sequence".
                if c == '\u{2028}' || c == '\u{2029}' {
                    return String::new();
                }
                if flags.intersects(EscapeSequenceScanningFlags::ANY_UNICODE_MODE)
                    || flags.intersects(EscapeSequenceScanningFlags::REGULAR_EXPRESSION)
                        && !flags.intersects(EscapeSequenceScanningFlags::ANNEX_B)
                        && is_identifier_part(c)
                {
                    self.error_at(
                        diag::This_character_cannot_be_escaped_in_a_regular_expression,
                        start,
                        self.scanner_state.pos - start,
                        Vec::new(),
                    );
                }
                c.to_string()
            }
        }
    }

    // Go: scanner/scanner.go:1868 scanUnicodeEscape
    // Known to be at \u
    pub(crate) fn scan_unicode_escape(&mut self, should_emit_invalid_escape_error: bool) -> i32 {
        self.scanner_state.pos += 2;
        let start = self.scanner_state.pos;
        let extended = self.char() == '{' as i32;
        let hex_digits;
        if extended {
            self.scanner_state.pos += 1;
            hex_digits = self.scan_hex_digits(1, true, false);
        } else {
            self.scanner_state.token_flags |= TokenFlags::UNICODE_ESCAPE;
            hex_digits = self.scan_hex_digits(4, false, false);
        }
        if hex_digits.is_empty() {
            self.scanner_state.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
            if should_emit_invalid_escape_error {
                self.error(diag::Hexadecimal_digit_expected);
            }
            return -1;
        }
        let hex_value = go_parse_int(&hex_digits, 16, 32);
        if extended {
            let mut is_invalid_extended_escape = false;
            if hex_value > 0x10FFFF {
                if should_emit_invalid_escape_error {
                    self.error_at(
                        diag::An_extended_Unicode_escape_value_must_be_between_0x0_and_0x10FFFF_inclusive,
                        start + 1,
                        self.scanner_state.pos - start - 1,
                        Vec::new(),
                    );
                }
                is_invalid_extended_escape = true;
            }
            if self.scanner_state.pos >= self.end {
                if should_emit_invalid_escape_error {
                    self.error(diag::Unexpected_end_of_text);
                }
                is_invalid_extended_escape = true;
            } else if self.char() == '}' as i32 {
                self.scanner_state.pos += 1;
            } else {
                if should_emit_invalid_escape_error {
                    self.error(diag::Unterminated_Unicode_escape_sequence);
                }
                is_invalid_extended_escape = true;
            }
            if is_invalid_extended_escape {
                self.scanner_state.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                return -1;
            }
            self.scanner_state.token_flags |= TokenFlags::EXTENDED_UNICODE_ESCAPE;
        }
        hex_value as i32
    }

    // Go: scanner/scanner.go:1925 scanLowSurrogateEscape
    // scanLowSurrogateEscape attempts to consume a low-surrogate Unicode escape
    // (either '\uLow' or '\u{Low}') immediately following an already-scanned high
    // surrogate and combine them into a single supplementary code point. This
    // mirrors how adjacent UTF-16 code units form a surrogate pair in a JavaScript
    // string, regardless of which escape syntax produced each half. On success it
    // returns the combined code point and true; otherwise it restores the scanner
    // position and returns false.
    // PORT: `(rune, bool)` returns `Option<i32>`.
    pub(crate) fn scan_low_surrogate_escape(&mut self, high: i32) -> Option<i32> {
        if self.char() != '\\' as i32 || self.char_at(1) != 'u' as i32 {
            return None;
        }
        let saved_pos = self.scanner_state.pos;
        let saved_token_flags = self.scanner_state.token_flags;
        // Speculatively scan the escape with diagnostics suppressed: if it isn't a
        // low surrogate we rewind below, and the caller re-scans the same escape and
        // reports any error then, so reporting here would duplicate diagnostics.
        let low = self.scan_unicode_escape(false);
        if low >= 0 && is_low_surrogate(low as u32) {
            return Some(surrogate_pair_to_code_point(high as u32, low as u32) as i32);
        }
        self.scanner_state.pos = saved_pos;
        self.scanner_state.token_flags = saved_token_flags;
        None
    }

    // Go: scanner/scanner.go:1945 peekUnicodeEscape
    // Current character is known to be a backslash. Check for Unicode escape of the form '\uXXXX'
    // or '\u{XXXXXX}' and return code point value if valid Unicode escape is found. Otherwise return -1.
    pub(crate) fn peek_unicode_escape(&mut self) -> i32 {
        if self.char_at(1) == 'u' as i32 {
            let save_pos = self.scanner_state.pos;
            let save_token_flags = self.scanner_state.token_flags;
            let code_point = self.scan_unicode_escape(false);
            self.scanner_state.pos = save_pos;
            self.scanner_state.token_flags = save_token_flags;
            return code_point;
        }
        -1
    }

    // Go: scanner/scanner.go:1957 scanNumber
    pub(crate) fn scan_number(&mut self) -> SyntaxKind {
        let mut start = self.scanner_state.pos;
        let fixed_part;
        if self.char() == '0' as i32 {
            self.scanner_state.pos += 1;
            if self.char() == '_' as i32 {
                self.scanner_state.token_flags |= TokenFlags::CONTAINS_SEPARATOR | TokenFlags::CONTAINS_INVALID_SEPARATOR;
                self.error_at(diag::Numeric_separators_are_not_allowed_here, self.scanner_state.pos, 1, Vec::new());
                self.scanner_state.pos = start;
                fixed_part = self.scan_number_fragment();
            } else {
                let (digits, is_octal) = self.scan_digits();
                if digits.is_empty() {
                    fixed_part = "0".to_string();
                } else if !is_octal {
                    self.scanner_state.token_flags |= TokenFlags::CONTAINS_LEADING_ZERO;
                    fixed_part = digits;
                } else {
                    let val = go_parse_int(&digits, 8, 64);
                    self.set_token_value(&val.to_string());
                    self.scanner_state.token_flags |= TokenFlags::OCTAL;
                    let with_minus = self.scanner_state.token == SyntaxKind::MinusToken;
                    let literal = format!("{}0o{:o}", if with_minus { "-" } else { "" }, val);
                    if with_minus {
                        start -= 1;
                    }
                    self.error_at(
                        diag::Octal_literals_are_not_allowed_Use_the_syntax_0,
                        start,
                        self.scanner_state.pos - start,
                        args![literal],
                    );
                    return SyntaxKind::NumericLiteral;
                }
            }
        } else {
            fixed_part = self.scan_number_fragment();
        }
        let fixed_part_end = self.scanner_state.pos;
        let mut fractional_part = String::new();
        let mut exponent_preamble = String::new();
        let mut exponent_part = String::new();
        if self.char() == '.' as i32 {
            self.scanner_state.pos += 1;
            fractional_part = self.scan_number_fragment();
        }
        let mut end = self.scanner_state.pos;
        if self.char() == 'E' as i32 || self.char() == 'e' as i32 {
            self.scanner_state.pos += 1;
            self.scanner_state.token_flags |= TokenFlags::SCIENTIFIC;
            if self.char() == '+' as i32 || self.char() == '-' as i32 {
                self.scanner_state.pos += 1;
            }
            let start_numeric_part = self.scanner_state.pos;
            exponent_part = self.scan_number_fragment();
            if exponent_part.is_empty() {
                self.error(diag::Digit_expected);
            } else {
                exponent_preamble = self.text[end as usize..start_numeric_part as usize].to_string();
                end = self.scanner_state.pos;
            }
        }
        if self.scanner_state.token_flags.intersects(TokenFlags::CONTAINS_SEPARATOR) {
            let mut value = fixed_part;
            if !fractional_part.is_empty() {
                value.push('.');
                value.push_str(&fractional_part);
            }
            if !exponent_part.is_empty() {
                value.push_str(&exponent_preamble);
                value.push_str(&exponent_part);
            }
            self.set_token_value(&value);
        } else {
            self.scanner_state.token_value = intern_token_value(&self.text[start as usize..end as usize]);
        }
        if self.scanner_state.token_flags.intersects(TokenFlags::CONTAINS_LEADING_ZERO) {
            self.error_at(diag::Decimals_with_leading_zeros_are_not_allowed, start, self.scanner_state.pos - start, Vec::new());
            self.set_token_value(&js_number_string(self.scanner_state.token_value));
            return SyntaxKind::NumericLiteral;
        }
        let result;
        if fixed_part_end == self.scanner_state.pos {
            result = self.scan_big_int_suffix();
        } else {
            self.set_token_value(&js_number_string(self.scanner_state.token_value));
            result = SyntaxKind::NumericLiteral;
        }
        let (ch, _) = self.char_and_size();
        if is_identifier_start(rune_to_char(ch)) {
            let id_start = self.scanner_state.pos;
            let id = self.scan_identifier_parts();
            if result != SyntaxKind::BigIntLiteral && id.len() == 1 && self.text.as_bytes()[id_start as usize] == b'n' {
                if self.scanner_state.token_flags.intersects(TokenFlags::SCIENTIFIC) {
                    self.error_at(
                        diag::A_bigint_literal_cannot_use_exponential_notation,
                        start,
                        self.scanner_state.pos - start,
                        Vec::new(),
                    );
                    return result;
                }
                if fixed_part_end < id_start {
                    self.error_at(diag::A_bigint_literal_must_be_an_integer, start, self.scanner_state.pos - start, Vec::new());
                    return result;
                }
            }
            self.error_at(
                diag::An_identifier_or_keyword_cannot_immediately_follow_a_numeric_literal,
                id_start,
                self.scanner_state.pos - id_start,
                Vec::new(),
            );
            self.scanner_state.pos = id_start;
        }
        result
    }

    // Go: scanner/scanner.go:2057 scanNumberFragment
    pub(crate) fn scan_number_fragment(&mut self) -> String {
        let mut start = self.scanner_state.pos;
        let mut allow_separator = false;
        let mut is_previous_token_separator = false;
        let mut result = String::new();
        loop {
            let before = self.scanner_state.pos;
            self.scan_ascii_while(|b: u8| b.is_ascii_digit());
            if self.scanner_state.pos > before {
                allow_separator = true;
                is_previous_token_separator = false;
            }
            let ch = self.char();
            if ch == '_' as i32 {
                self.scanner_state.token_flags |= TokenFlags::CONTAINS_SEPARATOR;
                if allow_separator {
                    allow_separator = false;
                    is_previous_token_separator = true;
                    result.push_str(&self.text[start as usize..self.scanner_state.pos as usize]);
                } else {
                    self.scanner_state.token_flags |= TokenFlags::CONTAINS_INVALID_SEPARATOR;
                    if is_previous_token_separator {
                        self.error_at(
                            diag::Multiple_consecutive_numeric_separators_are_not_permitted,
                            self.scanner_state.pos,
                            1,
                            Vec::new(),
                        );
                    } else {
                        self.error_at(diag::Numeric_separators_are_not_allowed_here, self.scanner_state.pos, 1, Vec::new());
                    }
                }
                self.scanner_state.pos += 1;
                start = self.scanner_state.pos;
                continue;
            }
            break;
        }
        if is_previous_token_separator {
            self.scanner_state.token_flags |= TokenFlags::CONTAINS_INVALID_SEPARATOR;
            self.error_at(diag::Numeric_separators_are_not_allowed_here, self.scanner_state.pos - 1, 1, Vec::new());
        }
        if result.is_empty() {
            return self.text[start as usize..self.scanner_state.pos as usize].to_string();
        }
        result.push_str(&self.text[start as usize..self.scanner_state.pos as usize]);
        result
    }

    // Go: scanner/scanner.go:2103 scanDigits
    // PORT: returns an owned `String`; the source text is a `Cow` that the
    // caller cannot borrow while it mutates the scanner.
    pub(crate) fn scan_digits(&mut self) -> (String, bool) {
        let start = self.scanner_state.pos;
        let mut is_octal = true;
        while is_digit(rune_to_char(self.char())) {
            if !is_octal_digit(rune_to_char(self.char())) {
                is_octal = false;
            }
            self.scanner_state.pos += 1;
        }
        (self.text[start as usize..self.scanner_state.pos as usize].to_string(), is_octal)
    }

    // Go: scanner/scanner.go:2115 scanHexDigits
    pub(crate) fn scan_hex_digits(
        &mut self,
        min_count: i32,
        scan_as_many_as_possible: bool,
        can_have_separators: bool,
    ) -> String {
        let mut digit_count = 0;
        let start = self.scanner_state.pos;
        let mut allow_separator = false;
        let mut is_previous_token_separator = false;
        while digit_count < min_count || scan_as_many_as_possible {
            let ch = self.char();
            if is_hex_digit(rune_to_char(ch)) {
                allow_separator = can_have_separators;
                is_previous_token_separator = false;
                digit_count += 1;
            } else if can_have_separators && ch == '_' as i32 {
                self.scanner_state.token_flags |= TokenFlags::CONTAINS_SEPARATOR;
                if allow_separator {
                    allow_separator = false;
                    is_previous_token_separator = true;
                } else if is_previous_token_separator {
                    self.error_at(
                        diag::Multiple_consecutive_numeric_separators_are_not_permitted,
                        self.scanner_state.pos,
                        1,
                        Vec::new(),
                    );
                } else {
                    self.error_at(diag::Numeric_separators_are_not_allowed_here, self.scanner_state.pos, 1, Vec::new());
                }
            } else {
                break;
            }
            self.scanner_state.pos += 1;
        }
        if is_previous_token_separator {
            self.error_at(diag::Numeric_separators_are_not_allowed_here, self.scanner_state.pos - 1, 1, Vec::new());
        }
        if digit_count < min_count {
            return String::new();
        }
        let original = self.text[start as usize..self.scanner_state.pos as usize].to_string();
        // PORT: Go allocates `hexDigitCache` on first use; the Rust map is
        // always allocated.
        if let Some(cached) = self.hex_digit_cache.get(&original) {
            cached.clone()
        } else {
            let mut digits = original.clone();
            if self.scanner_state.token_flags.intersects(TokenFlags::CONTAINS_SEPARATOR) {
                digits = digits.replace('_', "");
            }
            digits = digits.to_ascii_lowercase(); // standardize hex literals to lowercase
            self.hex_digit_cache.insert(original, digits.clone());
            digits
        }
    }

    // Go: scanner/scanner.go:2164 scanBinaryOrOctalDigits
    pub(crate) fn scan_binary_or_octal_digits(&mut self, base: i32) -> String {
        let mut sb = String::new();
        let mut allow_separator = false;
        let mut is_previous_token_separator = false;
        loop {
            let ch = self.char();
            if is_digit(rune_to_char(ch)) && ch - ('0' as i32) < base {
                sb.push(rune_to_char(ch));
                allow_separator = true;
                is_previous_token_separator = false;
            } else if ch == '_' as i32 {
                self.scanner_state.token_flags |= TokenFlags::CONTAINS_SEPARATOR;
                if allow_separator {
                    allow_separator = false;
                    is_previous_token_separator = true;
                } else if is_previous_token_separator {
                    self.error_at(
                        diag::Multiple_consecutive_numeric_separators_are_not_permitted,
                        self.scanner_state.pos,
                        1,
                        Vec::new(),
                    );
                } else {
                    self.error_at(diag::Numeric_separators_are_not_allowed_here, self.scanner_state.pos, 1, Vec::new());
                }
            } else {
                break;
            }
            self.scanner_state.pos += 1;
        }
        if is_previous_token_separator {
            self.error_at(diag::Numeric_separators_are_not_allowed_here, self.scanner_state.pos - 1, 1, Vec::new());
        }
        sb
    }

    // Go: scanner/scanner.go:2195 scanBigIntSuffix
    pub(crate) fn scan_big_int_suffix(&mut self) -> SyntaxKind {
        if self.char() == 'n' as i32 {
            let mut value = format!("{}n", self.scanner_state.token_value);
            if self.scanner_state.token_flags.intersects(TokenFlags::BINARY_OR_OCTAL_SPECIFIER) {
                // PORT: `ts_jsnum::parse_pseudo_big_int` strips the trailing
                // `n` that Go `ParsePseudoBigInt` also ignores.
                value = ts_jsnum::parse_pseudo_big_int(&value) + "n";
            }
            self.set_token_value(&value);
            self.scanner_state.pos += 1;
            return SyntaxKind::BigIntLiteral;
        }
        // PORT: Go allocates `numberCache` on first use; the Rust map is
        // always allocated.
        if let Some(cached) = self.number_cache.get(self.scanner_state.token_value) {
            self.scanner_state.token_value = intern_token_value(cached);
        } else {
            let token_value = js_number_string(self.scanner_state.token_value);
            // Go: `if tokenValue == s.tokenValue { tokenValue = s.tokenValue }`
            // only shares the string memory; the value is the same.
            self.number_cache.insert(self.scanner_state.token_value.to_string(), token_value.clone());
            self.set_token_value(&token_value);
        }
        SyntaxKind::NumericLiteral
    }

    // Go: scanner/scanner.go:2220 scanInvalidCharacter
    pub(crate) fn scan_invalid_character(&mut self) {
        let (_, size) = self.char_and_size();
        self.error_at(diag::Invalid_character, self.scanner_state.pos, size, Vec::new());
        self.scanner_state.pos += size;
        self.scanner_state.token = SyntaxKind::Unknown;
    }
}
