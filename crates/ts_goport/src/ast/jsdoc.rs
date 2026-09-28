//! Port of Go `parser/jsdoc.go` and the parts of `parser/parser.go` that
//! parse JSDoc comments.
//!
//! Go parses the JSDoc of a TS file eagerly when the comment has `@see`,
//! `@link`, `@linkcode` or `@linkplain` (the scanner sets
//! `TokenFlagsPrecedingJSDocWithSeeOrLink`). The Rust parser does not build
//! these nodes, so `build_jsdoc_cache` parses them after the parse, into the
//! synthetic arena. The result is Go `SourceFile.jsdocCache`.
//!
//! Only the TS path is ported. JS files parse JSDoc lazily and reparse it;
//! that stays unported.

use crate::frontend::parser::should_consume_binary_operator;
use crate::prelude::*;
use ts_ast::NodeData as D;

// ──────────────────────────────────────────────────────────────────────
// Scanner
// ──────────────────────────────────────────────────────────────────────

/// Go `scanner.ScannerState`, for the fields the JSDoc parser uses.
#[derive(Clone)]
struct ScanState {
    pos: i32,
    full_start: i32,
    token_start: i32,
    token: SyntaxKind,
    value: String,
    flags: TokenFlags,
    skip_asterisks: i32,
}

/// Go `*scanner.Scanner` for one JSDoc comment.
// PORT: Go `Scan` is done by the Rust `ts_scanner::Scanner`, one token at a
// time from `pos`. The JSDoc scans (`ScanJSDocToken`,
// `ScanJSDocCommentTextToken`) and the rescans are ported here, because the
// Rust scanner keeps different state. Go `skipJSDocLeadingAsterisks` is done
// here too, so the inner scanner never skips asterisks.
struct Sc {
    /// Go `s.text`: the source text cut at the end of the comment body.
    text: &'static str,
    inner: ts_scanner::Scanner<'static>,
    st: ScanState,
}

/// ts_scanner token flags, by Go bit index (bits 0 to 18 match Go).
const RUST_TOKEN_FLAGS: [ts_scanner::TokenFlags; 19] = [
    ts_scanner::TokenFlags::PRECEDING_LINE_BREAK,
    ts_scanner::TokenFlags::PRECEDING_JSDOC_COMMENT,
    ts_scanner::TokenFlags::UNTERMINATED,
    ts_scanner::TokenFlags::EXTENDED_UNICODE_ESCAPE,
    ts_scanner::TokenFlags::SCIENTIFIC,
    ts_scanner::TokenFlags::OCTAL,
    ts_scanner::TokenFlags::HEX_SPECIFIER,
    ts_scanner::TokenFlags::BINARY_SPECIFIER,
    ts_scanner::TokenFlags::OCTAL_SPECIFIER,
    ts_scanner::TokenFlags::CONTAINS_SEPARATOR,
    ts_scanner::TokenFlags::UNICODE_ESCAPE,
    ts_scanner::TokenFlags::CONTAINS_INVALID_ESCAPE,
    ts_scanner::TokenFlags::HEX_ESCAPE,
    ts_scanner::TokenFlags::CONTAINS_LEADING_ZERO,
    ts_scanner::TokenFlags::CONTAINS_INVALID_SEPARATOR,
    ts_scanner::TokenFlags::PRECEDING_JSDOC_LEADING_ASTERISKS,
    ts_scanner::TokenFlags::SINGLE_QUOTE,
    ts_scanner::TokenFlags::PRECEDING_JSDOC_WITH_DEPRECATED,
    ts_scanner::TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK,
];

/// Go token flags from ts_scanner token flags.
fn go_token_flags(flags: ts_scanner::TokenFlags) -> TokenFlags {
    let mut bits = 0i32;
    for (i, f) in RUST_TOKEN_FLAGS.iter().enumerate() {
        if flags.contains(*f) {
            bits |= 1 << i;
        }
    }
    TokenFlags(bits)
}

/// A Go rune as a char. Go `string(r)` and `WriteRune(r)` write U+FFFD for
/// an invalid rune (negative, a surrogate or above U+10FFFF).
fn rune_to_char(r: i32) -> char {
    u32::try_from(r)
        .ok()
        .and_then(char::from_u32)
        .unwrap_or(char::REPLACEMENT_CHARACTER)
}

impl Sc {
    fn new(text: &'static str) -> Self {
        Sc {
            text,
            inner: ts_scanner::Scanner::new(text),
            st: ScanState {
                pos: 0,
                full_start: 0,
                token_start: 0,
                token: SyntaxKind::Unknown,
                value: String::new(),
                flags: TokenFlags::NONE,
                skip_asterisks: 0,
            },
        }
    }

    /// Go `s.charAndSize()`: the char at `pos` and its size, or (0, 0) at the end.
    fn char_and_size(&self) -> (char, i32) {
        match self
            .text
            .get(self.st.pos as usize..)
            .and_then(|s| s.chars().next())
        {
            Some(c) => (c, c.len_utf8() as i32),
            None => ('\0', 0),
        }
    }

    // Go: scanner.go:481 Scan
    // PORT: done by the Rust scanner; see `Sc`.
    fn scan(&mut self) -> SyntaxKind {
        self.inner.reset_pos(self.st.pos as usize);
        let mut t = self.inner.scan();
        let full_start = t.full_start.get() as i32;
        let mut flags = go_token_flags(t.flags);
        // Go: scanner.go:580 the `*` case with skipJSDocLeadingAsterisks
        while t.kind == SyntaxKind::AsteriskToken
            && self.st.skip_asterisks != 0
            && !flags.intersects(TokenFlags::PRECEDING_JS_DOC_LEADING_ASTERISKS)
            && flags.intersects(TokenFlags::PRECEDING_LINE_BREAK)
        {
            flags = flags | TokenFlags::PRECEDING_JS_DOC_LEADING_ASTERISKS;
            self.inner.reset_pos(t.range.end.get() as usize);
            t = self.inner.scan();
            flags = flags | go_token_flags(t.flags);
        }
        self.st.full_start = full_start;
        self.st.token_start = t.range.start.get() as i32;
        self.st.pos = t.range.end.get() as i32;
        self.st.flags = flags;
        self.st.token = t.kind;
        if let Some(v) = &t.value {
            self.st.value = crate::scanner_util::js_string_to_token_value(v);
        } else if token_is_identifier_or_keyword(t.kind) {
            self.st.value = t.text.to_string();
        }
        self.st.token
    }

    // Go: scanner.go:1386 ScanJSDocCommentTextToken
    fn scan_jsdoc_comment_text_token(&mut self, in_backticks: bool) -> SyntaxKind {
        self.st.full_start = self.st.pos;
        self.st.flags = TokenFlags::NONE;
        if self.st.pos as usize >= self.text.len() {
            self.st.token = SyntaxKind::EndOfFile;
            return self.st.token;
        }
        self.st.token_start = self.st.pos;
        loop {
            let (ch, size) = self.char_and_size();
            if !((self.st.pos as usize) < self.text.len() && !is_line_break(ch) && ch != '`') {
                break;
            }
            if !in_backticks {
                if ch == '{' {
                    break;
                } else if ch == '@' && self.st.pos >= 0 {
                    let previous = self.text[..self.st.pos as usize]
                        .chars()
                        .next_back()
                        .unwrap_or('\u{FFFD}');
                    if is_white_space_single_line(previous) {
                        let next = self.text[(self.st.pos + size) as usize..]
                            .chars()
                            .next()
                            .unwrap_or('\u{FFFD}');
                        if is_identifier_start(next) {
                            break;
                        }
                    }
                }
            }
            self.st.pos += size;
        }
        if self.st.pos == self.st.token_start {
            return self.scan_jsdoc_token();
        }
        self.st.value = self.text[self.st.token_start as usize..self.st.pos as usize].to_string();
        self.st.token = SyntaxKind::JsDocCommentTextToken;
        self.st.token
    }

    // Go: scanner.go:1422 CanFollowJSDocAt
    fn can_follow_jsdoc_at(&self) -> bool {
        if self.st.pos as usize >= self.text.len() {
            return true;
        }
        let ch = self.text[self.st.pos as usize..]
            .chars()
            .next()
            .unwrap_or('\u{FFFD}');
        is_identifier_start(ch) || is_white_space_single_line(ch) || is_line_break(ch)
    }

    // Go: scanner.go:1430 ScanJSDocToken
    fn scan_jsdoc_token(&mut self) -> SyntaxKind {
        self.st.full_start = self.st.pos;
        self.st.flags = TokenFlags::NONE;
        if self.st.pos as usize >= self.text.len() {
            self.st.token = SyntaxKind::EndOfFile;
            return self.st.token;
        }
        self.st.token_start = self.st.pos;
        let (ch, size) = self.char_and_size();
        self.st.pos += size;
        let token = match ch {
            '\t' | '\u{000B}' | '\u{000C}' | ' ' => {
                loop {
                    let (ch2, size2) = self.char_and_size();
                    if !(size2 > 0 && is_white_space_single_line(ch2)) {
                        break;
                    }
                    self.st.pos += size2;
                }
                SyntaxKind::WhitespaceTrivia
            }
            '@' => SyntaxKind::AtToken,
            '\r' | '\n' => {
                if ch == '\r' && self.char_and_size().0 == '\n' {
                    self.st.pos += 1;
                }
                self.st.flags = self.st.flags | TokenFlags::PRECEDING_LINE_BREAK;
                SyntaxKind::NewLineTrivia
            }
            '*' => SyntaxKind::AsteriskToken,
            '{' => SyntaxKind::OpenBraceToken,
            '}' => SyntaxKind::CloseBraceToken,
            '[' => SyntaxKind::OpenBracketToken,
            ']' => SyntaxKind::CloseBracketToken,
            '(' => SyntaxKind::OpenParenToken,
            ')' => SyntaxKind::CloseParenToken,
            '<' => SyntaxKind::LessThanToken,
            '>' => SyntaxKind::GreaterThanToken,
            '=' => SyntaxKind::EqualsToken,
            ',' => SyntaxKind::CommaToken,
            '.' => SyntaxKind::DotToken,
            '`' => SyntaxKind::BacktickToken,
            '#' => SyntaxKind::HashToken,
            '\\' => {
                self.st.pos -= 1;
                let cp = self.peek_unicode_escape();
                if cp >= 0 && is_identifier_start(rune_to_char(cp)) {
                    let escaped = rune_to_char(self.scan_unicode_escape(true));
                    let parts = self.scan_identifier_parts();
                    self.st.value = format!("{escaped}{parts}");
                    get_identifier_token(&self.st.value)
                } else {
                    self.st.pos += 1;
                    SyntaxKind::Unknown
                }
            }
            _ if is_identifier_start(ch) => {
                let mut c = ch;
                loop {
                    if self.st.pos as usize >= self.text.len() {
                        break;
                    }
                    let (c2, size2) = self.char_and_size();
                    c = c2;
                    if !is_identifier_part(c) && c != '-' {
                        break;
                    }
                    self.st.pos += size2;
                }
                self.st.value =
                    self.text[self.st.token_start as usize..self.st.pos as usize].to_string();
                if c == '\\' {
                    let parts = self.scan_identifier_parts();
                    self.st.value.push_str(&parts);
                }
                get_identifier_token(&self.st.value)
            }
            _ => SyntaxKind::Unknown,
        };
        self.st.token = token;
        token
    }

    // Go: scanner.go:421 error
    // PORT: see `error_at`.
    fn error(&mut self, message: &'static ts_diagnostics::Message) {
        self.error_at(message, self.st.pos, 0);
    }

    // Go: scanner.go:425 errorAt
    // PORT: Go calls the parser's `scanError`, which adds a parse error. This
    // scanner has no error callback, as the errors of the Rust scans in
    // `scan` are not reported either. The JSDoc scans below never reach it:
    // `scan_unicode_escape(true)` runs only after `peek_unicode_escape`
    // accepted the same escape, and `scan_hex_digits` is called without
    // separators.
    fn error_at(&mut self, _message: &'static ts_diagnostics::Message, _pos: i32, _length: i32) {}

    // Go: scanner.go:434 char
    // NOTE: even though this returns a rune, it only decodes the current byte.
    fn char(&self) -> i32 {
        match self.text.as_bytes().get(self.st.pos as usize) {
            Some(&b) => i32::from(b),
            None => -1,
        }
    }

    // Go: scanner.go:442 charAt
    // NOTE: this returns a rune, but only decodes the byte at the offset.
    fn char_at(&self, offset: i32) -> i32 {
        match self.text.as_bytes().get((self.st.pos + offset) as usize) {
            Some(&b) => i32::from(b),
            None => -1,
        }
    }

    // Go: scanner.go:1574 scanIdentifierParts
    fn scan_identifier_parts(&mut self) -> String {
        let mut sb = String::new();
        let mut start = self.st.pos;
        loop {
            let (ch, size) = self.char_and_size();
            if is_identifier_part(ch) {
                self.st.pos += size;
                continue;
            }
            if ch == '\\' {
                let escaped = self.peek_unicode_escape();
                if escaped >= 0 && is_identifier_part(rune_to_char(escaped)) {
                    sb.push_str(&self.text[start as usize..self.st.pos as usize]);
                    sb.push(rune_to_char(self.scan_unicode_escape(true)));
                    start = self.st.pos;
                    continue;
                }
            }
            break;
        }
        sb.push_str(&self.text[start as usize..self.st.pos as usize]);
        sb
    }

    // Go: scanner.go:1868 scanUnicodeEscape
    // Known to be at \u
    fn scan_unicode_escape(&mut self, should_emit_invalid_escape_error: bool) -> i32 {
        self.st.pos += 2;
        let start = self.st.pos;
        let extended = self.char() == '{' as i32;
        let hex_digits = if extended {
            self.st.pos += 1;
            self.scan_hex_digits(1, true, false)
        } else {
            self.st.flags = self.st.flags | TokenFlags::UNICODE_ESCAPE;
            self.scan_hex_digits(4, false, false)
        };
        if hex_digits.is_empty() {
            self.st.flags = self.st.flags | TokenFlags::CONTAINS_INVALID_ESCAPE;
            if should_emit_invalid_escape_error {
                self.error(diag::Hexadecimal_digit_expected);
            }
            return -1;
        }
        // Go: strconv.ParseInt(hexDigits, 16, 32). The digits are hex digits
        // and not empty, so the only error is out of range, where Go returns
        // the largest int32.
        let hex_value = i32::from_str_radix(&hex_digits, 16).unwrap_or(i32::MAX);
        if extended {
            let mut is_invalid_extended_escape = false;
            if hex_value > 0x10FFFF {
                if should_emit_invalid_escape_error {
                    self.error_at(
                        diag::An_extended_Unicode_escape_value_must_be_between_0x0_and_0x10FFFF_inclusive,
                        start + 1,
                        self.st.pos - start - 1,
                    );
                }
                is_invalid_extended_escape = true;
            }
            if self.st.pos as usize >= self.text.len() {
                if should_emit_invalid_escape_error {
                    self.error(diag::Unexpected_end_of_text);
                }
                is_invalid_extended_escape = true;
            } else if self.char() == '}' as i32 {
                self.st.pos += 1;
            } else {
                if should_emit_invalid_escape_error {
                    self.error(diag::Unterminated_Unicode_escape_sequence);
                }
                is_invalid_extended_escape = true;
            }
            if is_invalid_extended_escape {
                self.st.flags = self.st.flags | TokenFlags::CONTAINS_INVALID_ESCAPE;
                return -1;
            }
            self.st.flags = self.st.flags | TokenFlags::EXTENDED_UNICODE_ESCAPE;
        }
        hex_value
    }

    // Go: scanner.go:1945 peekUnicodeEscape
    // Current character is known to be a backslash. Check for Unicode escape of the form '\uXXXX'
    // or '\u{XXXXXX}' and return code point value if valid Unicode escape is found. Otherwise return -1.
    fn peek_unicode_escape(&mut self) -> i32 {
        if self.char_at(1) == 'u' as i32 {
            let save_pos = self.st.pos;
            let save_token_flags = self.st.flags;
            let code_point = self.scan_unicode_escape(false);
            self.st.pos = save_pos;
            self.st.flags = save_token_flags;
            return code_point;
        }
        -1
    }

    // Go: scanner.go:2115 scanHexDigits
    // PORT: Go memoizes the result in `hexDigitCache`. The cache only saves
    // work for these callers, which never pass separators, so it is not kept.
    fn scan_hex_digits(
        &mut self,
        min_count: i32,
        scan_as_many_as_possible: bool,
        can_have_separators: bool,
    ) -> String {
        let mut digit_count = 0;
        let start = self.st.pos;
        let mut allow_separator = false;
        let mut is_previous_token_separator = false;
        while digit_count < min_count || scan_as_many_as_possible {
            let ch = self.char();
            if ch >= 0 && is_hex_digit(char::from(ch as u8)) {
                allow_separator = can_have_separators;
                is_previous_token_separator = false;
                digit_count += 1;
            } else if can_have_separators && ch == '_' as i32 {
                self.st.flags = self.st.flags | TokenFlags::CONTAINS_SEPARATOR;
                if allow_separator {
                    allow_separator = false;
                    is_previous_token_separator = true;
                } else if is_previous_token_separator {
                    self.error_at(
                        diag::Multiple_consecutive_numeric_separators_are_not_permitted,
                        self.st.pos,
                        1,
                    );
                } else {
                    self.error_at(
                        diag::Numeric_separators_are_not_allowed_here,
                        self.st.pos,
                        1,
                    );
                }
            } else {
                break;
            }
            self.st.pos += 1;
        }
        if is_previous_token_separator {
            self.error_at(
                diag::Numeric_separators_are_not_allowed_here,
                self.st.pos - 1,
                1,
            );
        }
        if digit_count < min_count {
            return String::new();
        }
        let mut digits = self.text[start as usize..self.st.pos as usize].to_string();
        if self.st.flags.intersects(TokenFlags::CONTAINS_SEPARATOR) {
            digits = digits.replace('_', "");
        }
        digits.to_lowercase() // standardize hex literals to lowercase
    }

    // Go: scanner.go:1025 ReScanLessThanToken
    fn rescan_less_than_token(&mut self) -> SyntaxKind {
        if self.st.token == SyntaxKind::LessThanLessThanToken {
            self.st.pos = self.st.token_start + 1;
            self.st.token = SyntaxKind::LessThanToken;
        }
        self.st.token
    }

    // Go: scanner.go:1070 ReScanAsteriskEqualsToken
    fn rescan_asterisk_equals_token(&mut self) -> SyntaxKind {
        assert!(
            self.st.token == SyntaxKind::AsteriskEqualsToken,
            "'ReScanAsteriskEqualsToken' should only be called on a '*='"
        );
        self.st.pos = self.st.token_start + 1;
        self.st.token = SyntaxKind::EqualsToken;
        self.st.token
    }

    // Go: scanner.go:1244 ReScanHashToken
    fn rescan_hash_token(&mut self) -> SyntaxKind {
        if self.st.token == SyntaxKind::PrivateIdentifier {
            self.st.pos = self.st.token_start + 1;
            self.st.token = SyntaxKind::HashToken;
        }
        self.st.token
    }

    // Go: scanner.go:1252 ReScanQuestionToken
    fn rescan_question_token(&mut self) -> SyntaxKind {
        assert!(
            self.st.token == SyntaxKind::QuestionQuestionToken,
            "'reScanQuestionToken' should only be called on a '??'"
        );
        self.st.pos = self.st.token_start + 1;
        self.st.token = SyntaxKind::QuestionToken;
        self.st.token
    }

    /// Rescans the current token with a Rust scanner rescan.
    // PORT: the Rust rescans read the inner scanner's last token, so the
    // current token is scanned again from its start first. The rescan keeps
    // the token start and the preceding flags, as Go does.
    fn rescan_with(
        &mut self,
        f: impl FnOnce(&mut ts_scanner::Scanner<'static>) -> ts_scanner::Token<'static>,
    ) -> SyntaxKind {
        self.inner.reset_pos(self.st.token_start as usize);
        self.inner.scan();
        let t = f(&mut self.inner);
        self.st.pos = t.range.end.get() as i32;
        self.st.flags = self.st.flags | go_token_flags(t.flags);
        self.st.token = t.kind;
        if let Some(v) = &t.value {
            self.st.value = crate::scanner_util::js_string_to_token_value(v);
        }
        self.st.token
    }

    // Go: scanner.go:1079 ReScanSlashToken
    fn rescan_slash_token(&mut self) -> SyntaxKind {
        if self.st.token == SyntaxKind::SlashToken || self.st.token == SyntaxKind::SlashEqualsToken
        {
            return self.rescan_with(|s| s.rescan_slash_token());
        }
        self.st.token
    }

    // Go: scanner.go:1064 ReScanTemplateToken
    // PORT: the Rust scanner has no isTaggedTemplate input; it does not
    // report invalid escapes in either case.
    fn rescan_template_token(&mut self, _is_tagged_template: bool) -> SyntaxKind {
        self.rescan_with(|s| s.rescan_template_token())
    }

    // Go: scanner.go:293 ResetPos
    fn reset_pos(&mut self, pos: i32) {
        assert!(pos >= 0, "Cannot reset token state to negative position");
        self.st.pos = pos;
        self.st.full_start = pos;
        self.st.token_start = pos;
    }

    // Go: scanner.go:307 SetSkipJSDocLeadingAsterisks
    fn set_skip_jsdoc_leading_asterisks(&mut self, skip: bool) {
        self.st.skip_asterisks += if skip { 1 } else { -1 };
    }

    fn token_text(&self) -> &'static str {
        &self.text[self.st.token_start as usize..self.st.pos as usize]
    }

    fn has_flag(&self, f: TokenFlags) -> bool {
        self.st.flags.intersects(f)
    }
}

// ──────────────────────────────────────────────────────────────────────
// Comment ranges
// ──────────────────────────────────────────────────────────────────────

// Go: scanner.go:2827 iterateCommentRanges
/// The comment ranges (pos, end) at `pos`. Only the ranges are kept; the
/// JSDoc parser does not use the kind or the trailing newline.
fn iterate_comment_ranges(text: &str, mut pos: usize, trailing: bool) -> Vec<(i32, i32)> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut pending: Option<(usize, usize)> = None;
    let mut collecting = trailing;
    if pos == 0 {
        collecting = true;
        // Go: scanner.go:2488 isShebangTrivia, scanShebangTrivia
        if bytes.len() >= 2 && bytes[0] == b'#' && bytes[1] == b'!' {
            pos += 2;
            while let Some(c) = text[pos..].chars().next() {
                if is_line_break(c) {
                    break;
                }
                pos += c.len_utf8();
            }
        }
    }
    while pos < text.len() {
        let ch = text[pos..].chars().next().unwrap_or('\0');
        match ch {
            '\r' | '\n' => {
                if ch == '\r' && pos + 1 < text.len() && bytes[pos + 1] == b'\n' {
                    pos += 1;
                }
                pos += 1;
                if trailing {
                    break;
                }
                collecting = true;
                continue;
            }
            '\t' | '\u{000B}' | '\u{000C}' | ' ' => {
                pos += 1;
                continue;
            }
            '/' => {
                let next = if pos + 1 < text.len() {
                    bytes[pos + 1]
                } else {
                    0
                };
                if next == b'/' || next == b'*' {
                    let start = pos;
                    pos += 2;
                    if next == b'/' {
                        while let Some(c) = text[pos..].chars().next() {
                            if is_line_break(c) {
                                break;
                            }
                            pos += c.len_utf8();
                        }
                    } else if let Some(i) = text[pos..].find("*/") {
                        pos += i + 2;
                    } else {
                        pos = text.len();
                    }
                    if collecting {
                        if let Some(p) = pending {
                            out.push((p.0 as i32, p.1 as i32));
                        }
                        pending = Some((start, pos));
                    }
                    continue;
                }
                break;
            }
            _ => {
                if ch as u32 > 0x7F && is_white_space_like(ch) {
                    pos += ch.len_utf8();
                    continue;
                }
                break;
            }
        }
    }
    if let Some(p) = pending {
        out.push((p.0 as i32, p.1 as i32));
    }
    out
}

// Go: parser/utilities.go:28 GetJSDocCommentRanges
fn get_jsdoc_comment_ranges(node: Node, text: &str) -> Vec<(i32, i32)> {
    let pos = node.pos() as usize;
    let mut ranges = match node.kind() {
        SyntaxKind::Parameter
        | SyntaxKind::TypeParameter
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ArrowFunction
        | SyntaxKind::ParenthesizedExpression
        | SyntaxKind::VariableDeclaration
        | SyntaxKind::ExportSpecifier => {
            let mut r = iterate_comment_ranges(text, pos, true);
            r.extend(iterate_comment_ranges(text, pos, false));
            r
        }
        _ => iterate_comment_ranges(text, pos, false),
    };
    let b = text.as_bytes();
    ranges.retain(|&(s, e)| {
        let (su, len) = (s as usize, e - s);
        !(e > node.end() || len < 4 || b[su + 1] != b'*' || b[su + 2] != b'*' || b[su + 3] == b'/')
    });
    ranges
}

// Go: parser/utilities.go:54 isJSDocLikeText
fn is_jsdoc_like_text(text: &[u8]) -> bool {
    text.len() >= 4 && text[1] == b'*' && text[2] == b'*' && text[3] != b'/'
}

// Go: parser/parser.go:6413 isReservedWord
fn is_reserved_word(token: SyntaxKind) -> bool {
    (SyntaxKind::FIRST_RESERVED_WORD as u16..=SyntaxKind::LAST_RESERVED_WORD as u16)
        .contains(&(token as u16))
}

// ──────────────────────────────────────────────────────────────────────
// Parser core
// ──────────────────────────────────────────────────────────────────────

/// Go `jsdocState`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum JsdocState {
    BeginningOfLine,
    SawAsterisk,
    SavingComments,
    SavingBackticks,
}

/// Go `propertyLikeParse` bits.
const PROPERTY_LIKE_PARSE_PROPERTY: u8 = 1 << 0;
const PROPERTY_LIKE_PARSE_PARAMETER: u8 = 1 << 1;
const PROPERTY_LIKE_PARSE_CALLBACK_PARAMETER: u8 = 1 << 2;

/// Go `ParsingContext` values that the JSDoc parser uses.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ParsingContext {
    TypeMembers,
    Parameters,
    TypeParameters,
    TypeArguments,
    TupleElementTypes,
    ArgumentExpressions,
    ArrayLiteralMembers,
    BlockStatements,
    SwitchClauses,
    SwitchClauseStatements,
    ClassMembers,
    EnumMembers,
    ObjectLiteralMembers,
    ObjectBindingElements,
    ArrayBindingElements,
    ImportOrExportSpecifiers,
    ImportAttributes,
    HeritageClauseElement,
    HeritageClauses,
    VariableDeclarations,
}

/// Go `ParseFlags` values that the JSDoc parser uses.
const PARSE_FLAGS_NONE: u8 = 0;
const PARSE_FLAGS_YIELD: u8 = 1 << 0;
const PARSE_FLAGS_AWAIT: u8 = 1 << 1;
const PARSE_FLAGS_TYPE: u8 = 1 << 2;
const PARSE_FLAGS_IGNORE_MISSING_OPEN_BRACE: u8 = 1 << 4;

/// Go `ParserState`.
struct ParserState {
    scanner: ScanState,
    ctx: NodeFlags,
    diagnostics_len: usize,
    jsdoc_infos_len: usize,
    has_parse_error: bool,
}

/// Go `*Parser`, for one JSDoc comment.
// PORT: Go keeps one parser per file and saves and restores its state around
// each comment (parseJSDocComment). Here each comment gets a new parser with
// the host's context flags. Diagnostics are not kept; only their positions
// are, because Go compares the last position and counts them.
struct Parser {
    sc: Sc,
    /// Go `p.sourceText`: the whole file text. `sc.text` ends at the comment.
    source_text: &'static str,
    factory: NodeFactory,
    ctx: NodeFlags,
    has_parse_error: bool,
    token: SyntaxKind,
    diagnostics: Vec<i32>,
    /// Go `p.jsdocInfos`: the nested JSDoc that withJSDoc parsed.
    jsdoc_infos: Vec<(Node, Vec<Node>)>,
    /// Go `p.hasDeprecatedTag`.
    has_deprecated_tag: bool,
    /// Go `p.notParenthesizedArrow`.
    not_parenthesized_arrow: Vec<i32>,
    /// The lists that createMissingList made.
    // PORT: Go marks a missing list by its backing array. A Rust list is
    // copied into the node data, so the list is known by its address until
    // then, and a function or constructor type with a missing parameter list
    // is kept in `missing_parameter_hosts`.
    missing_lists: Vec<*const ()>,
    missing_parameter_hosts: Vec<Node>,
}

impl Parser {
    // Go: parser.go:321 parseErrorAt
    fn parse_error_at(&mut self, pos: i32, _end: i32) {
        self.parse_error_at_range(pos);
    }

    // Go: parser.go:325 parseErrorAtCurrentToken
    fn parse_error_at_current_token(&mut self) {
        self.parse_error_at_range(self.sc.st.token_start);
    }

    // Go: parser.go:329 parseErrorAtRange
    // PORT: only the position is kept; the message is dropped.
    fn parse_error_at_range(&mut self, pos: i32) {
        if self.diagnostics.last() != Some(&pos) {
            self.diagnostics.push(pos);
        }
        self.has_parse_error = true;
    }

    // Go: parser.go:351 mark
    fn mark(&self) -> ParserState {
        ParserState {
            scanner: self.sc.st.clone(),
            ctx: self.ctx,
            diagnostics_len: self.diagnostics.len(),
            jsdoc_infos_len: self.jsdoc_infos.len(),
            has_parse_error: self.has_parse_error,
        }
    }

    // Go: parser.go:364 rewind
    fn rewind(&mut self, state: ParserState) {
        self.sc.st = state.scanner;
        self.token = self.sc.st.token;
        self.ctx = state.ctx;
        self.diagnostics.truncate(state.diagnostics_len);
        self.jsdoc_infos.truncate(state.jsdoc_infos_len);
        self.has_parse_error = state.has_parse_error;
    }

    // Go: parser.go:376 lookAhead
    fn look_ahead(&mut self, f: impl FnOnce(&mut Self) -> bool) -> bool {
        let state = self.mark();
        let result = f(self);
        self.rewind(state);
        result
    }

    // Go: parser.go:383 nextToken
    fn next_token(&mut self) -> SyntaxKind {
        if is_keyword(self.token)
            && self
                .sc
                .has_flag(TokenFlags::UNICODE_ESCAPE | TokenFlags::EXTENDED_UNICODE_ESCAPE)
        {
            self.parse_error_at_current_token();
        }
        self.token = self.sc.scan();
        self.token
    }

    // Go: parser.go:393 nextTokenWithoutCheck
    fn next_token_without_check(&mut self) -> SyntaxKind {
        self.token = self.sc.scan();
        self.token
    }

    // Go: parser.go:398 nextTokenJSDoc
    fn next_token_jsdoc(&mut self) -> SyntaxKind {
        self.token = self.sc.scan_jsdoc_token();
        self.token
    }

    // Go: parser.go:403 nextJSDocCommentTextToken
    fn next_jsdoc_comment_text_token(&mut self, in_backticks: bool) -> SyntaxKind {
        self.token = self.sc.scan_jsdoc_comment_text_token(in_backticks);
        self.token
    }

    // Go: parser.go:408 nodePos
    fn node_pos(&self) -> i32 {
        self.sc.st.full_start
    }

    // Go: parser.go:412 hasPrecedingLineBreak
    fn has_preceding_line_break(&self) -> bool {
        self.sc.has_flag(TokenFlags::PRECEDING_LINE_BREAK)
    }

    // Go: parser.go:5925 finishNode
    fn finish_node(&mut self, node: Node, pos: i32) -> Node {
        let end = self.node_pos();
        self.finish_node_with_end(node, pos, end)
    }

    // Go: parser.go:5929 finishNodeWithEnd
    fn finish_node_with_end(&mut self, node: Node, pos: i32, end: i32) -> Node {
        set_node_loc(node, TextRange::new(pos, end));
        let mut flags = node.flags() | self.ctx;
        if self.has_parse_error {
            flags = flags | NodeFlags::THIS_NODE_HAS_ERROR;
            self.has_parse_error = false;
        }
        set_node_flags(node, flags);
        // Go: overrideParentInImmediateChildren
        node.for_each_child(|c| {
            set_node_parent(c, node);
            false
        });
        node
    }

    /// Go `p.newNodeList(loc, nodes)`.
    fn new_node_list(&self, loc: TextRange, nodes: &[Node]) -> NodeList {
        new_synthetic_node_list(nodes, loc)
    }

    /// Go `p.newModifierList(loc, nodes)`.
    fn new_modifier_list(&self, loc: TextRange, nodes: &[Node]) -> ModifierList {
        new_synthetic_modifier_list(nodes, loc)
    }

    // Go: parser.go:6373 setContextFlags
    fn set_context_flags(&mut self, flags: NodeFlags, value: bool) {
        if value {
            self.ctx = self.ctx | flags;
        } else {
            self.ctx = self.ctx.without(flags);
        }
    }

    fn in_yield_context(&self) -> bool {
        self.ctx.intersects(NodeFlags::YIELD_CONTEXT)
    }

    fn in_await_context(&self) -> bool {
        self.ctx.intersects(NodeFlags::AWAIT_CONTEXT)
    }

    fn in_disallow_conditional_types_context(&self) -> bool {
        self.ctx
            .intersects(NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT)
    }

    /// Go `doInContext(p, flags, value, f)`.
    fn do_in_context<T>(
        &mut self,
        flags: NodeFlags,
        value: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let save = self.ctx;
        self.set_context_flags(flags, value);
        let result = f(self);
        self.ctx = save;
        result
    }

    // ── Lists ──────────────────────────────────────────────────────────

    // Go: parser.go:647 parseList
    fn parse_list(
        &mut self,
        kind: ParsingContext,
        mut f: impl FnMut(&mut Self) -> Node,
    ) -> NodeList {
        let pos = self.node_pos();
        let mut list = Vec::new();
        while !self.is_list_terminator(kind) {
            if self.is_list_element(kind) {
                list.push(f(self));
                continue;
            }
            if self.abort_parsing_list_or_move_to_next_token(kind) {
                break;
            }
        }
        let end = self.node_pos();
        self.new_node_list(TextRange::new(pos, end), &list)
    }

    // Go: parser.go:654 parseDelimitedList
    fn parse_delimited_list(
        &mut self,
        kind: ParsingContext,
        mut f: impl FnMut(&mut Self) -> Node,
    ) -> NodeList {
        let pos = self.node_pos();
        let mut list = Vec::new();
        loop {
            if self.is_list_element(kind) {
                let start_pos = self.node_pos();
                let element = f(self);
                if element.is_nil() {
                    return NodeList::NIL;
                }
                list.push(element);
                if self.parse_optional(SyntaxKind::CommaToken) {
                    continue;
                }
                if self.is_list_terminator(kind) {
                    break;
                }
                self.parse_expected(SyntaxKind::CommaToken);
                if (kind == ParsingContext::ObjectLiteralMembers
                    || kind == ParsingContext::ImportAttributes)
                    && self.token == SyntaxKind::SemicolonToken
                    && !self.has_preceding_line_break()
                {
                    self.next_token();
                }
                if start_pos == self.node_pos() {
                    self.next_token();
                }
                continue;
            }
            if self.is_list_terminator(kind) {
                break;
            }
            if self.abort_parsing_list_or_move_to_next_token(kind) {
                break;
            }
        }
        let end = self.node_pos();
        self.new_node_list(TextRange::new(pos, end), &list)
    }

    // Go: parser.go:713 parseBracketedList
    fn parse_bracketed_list(
        &mut self,
        kind: ParsingContext,
        f: impl FnMut(&mut Self) -> Node,
        opening: SyntaxKind,
        closing: SyntaxKind,
    ) -> NodeList {
        if self.parse_expected(opening) {
            let result = self.parse_delimited_list(kind, f);
            self.parse_expected(closing);
            return result;
        }
        self.create_missing_list()
    }

    // Go: parser.go:726 createMissingList
    // PORT: see `Parser::missing_lists`.
    fn create_missing_list(&mut self) -> NodeList {
        let result = self.parse_empty_node_list();
        if let Some(l) = result.list_ptr() {
            self.missing_lists.push(l);
        }
        result
    }

    // Go: parser.go:118 isMissingNodeList
    fn is_missing_node_list(&self, list: NodeList) -> bool {
        list.list_ptr()
            .is_some_and(|l| self.missing_lists.contains(&l))
    }

    // Go: parser.go:733 abortParsingListOrMoveToNextToken
    // PORT: the JSDoc parser always has PCJSDocComment in parsingContexts,
    // and isListElement is true for it, so Go always reports the error and
    // aborts. That path is the only one ported.
    fn abort_parsing_list_or_move_to_next_token(&mut self, _kind: ParsingContext) -> bool {
        self.parse_error_at_current_token();
        true
    }

    // Go: parser.go:826 isListElement
    fn is_list_element(&mut self, kind: ParsingContext) -> bool {
        match kind {
            ParsingContext::TypeMembers => self.look_ahead(Self::scan_type_member_start),
            ParsingContext::TypeParameters => {
                self.token == SyntaxKind::InKeyword
                    || self.token == SyntaxKind::ConstKeyword
                    || self.is_identifier()
            }
            ParsingContext::Parameters => self.is_start_of_parameter(false),
            ParsingContext::TypeArguments | ParsingContext::TupleElementTypes => {
                self.token == SyntaxKind::CommaToken || self.is_start_of_type(false)
            }
            ParsingContext::ArrayLiteralMembers => {
                self.token == SyntaxKind::CommaToken
                    || self.token == SyntaxKind::DotToken
                    || self.token == SyntaxKind::DotDotDotToken
                    || self.is_start_of_expression()
            }
            ParsingContext::ArgumentExpressions => {
                self.token == SyntaxKind::DotDotDotToken || self.is_start_of_expression()
            }
            // PORT: inErrorRecovery is always false; the JSDoc parser never
            // calls isListElement in error recovery (see abort).
            ParsingContext::BlockStatements | ParsingContext::SwitchClauseStatements => {
                self.is_start_of_statement()
            }
            ParsingContext::SwitchClauses => {
                self.token == SyntaxKind::CaseKeyword || self.token == SyntaxKind::DefaultKeyword
            }
            // PORT: inErrorRecovery is always false (see above).
            ParsingContext::ClassMembers => {
                self.look_ahead(Self::scan_class_member_start)
                    || self.token == SyntaxKind::SemicolonToken
            }
            ParsingContext::EnumMembers => {
                self.token == SyntaxKind::OpenBracketToken || self.is_literal_property_name()
            }
            ParsingContext::ObjectLiteralMembers => match self.token {
                SyntaxKind::OpenBracketToken
                | SyntaxKind::AsteriskToken
                | SyntaxKind::DotDotDotToken
                | SyntaxKind::DotToken => true,
                _ => self.is_literal_property_name(),
            },
            ParsingContext::ObjectBindingElements => {
                self.token == SyntaxKind::OpenBracketToken
                    || self.token == SyntaxKind::DotDotDotToken
                    || self.is_literal_property_name()
            }
            ParsingContext::ImportAttributes => self.is_import_attribute_name(),
            ParsingContext::HeritageClauseElement => {
                if self.token == SyntaxKind::OpenBraceToken {
                    return self.is_valid_heritage_clause_object_literal();
                }
                self.is_start_of_left_hand_side_expression()
                    && !self.is_heritage_clause_extends_or_implements_keyword()
            }
            ParsingContext::VariableDeclarations => {
                self.is_binding_identifier_or_private_identifier_or_pattern()
            }
            ParsingContext::ArrayBindingElements => {
                self.token == SyntaxKind::CommaToken
                    || self.token == SyntaxKind::DotDotDotToken
                    || self.is_binding_identifier_or_private_identifier_or_pattern()
            }
            ParsingContext::HeritageClauses => self.is_heritage_clause(),
            ParsingContext::ImportOrExportSpecifiers => {
                if self.token == SyntaxKind::FromKeyword
                    && self.look_ahead(Self::next_token_is_token_string_literal)
                {
                    return false;
                }
                if self.token == SyntaxKind::StringLiteral {
                    return true;
                }
                token_is_identifier_or_keyword(self.token)
            }
        }
    }

    // Go: parser.go:918 isListTerminator
    fn is_list_terminator(&mut self, kind: ParsingContext) -> bool {
        if self.token == SyntaxKind::EndOfFile {
            return true;
        }
        match kind {
            ParsingContext::TypeMembers => self.token == SyntaxKind::CloseBraceToken,
            ParsingContext::TypeParameters => matches!(
                self.token,
                SyntaxKind::GreaterThanToken
                    | SyntaxKind::OpenParenToken
                    | SyntaxKind::OpenBraceToken
                    | SyntaxKind::ExtendsKeyword
                    | SyntaxKind::ImplementsKeyword
            ),
            ParsingContext::Parameters => {
                self.token == SyntaxKind::CloseParenToken
                    || self.token == SyntaxKind::CloseBracketToken
            }
            ParsingContext::TupleElementTypes | ParsingContext::ArrayLiteralMembers => {
                self.token == SyntaxKind::CloseBracketToken
            }
            ParsingContext::ArgumentExpressions => {
                self.token == SyntaxKind::CloseParenToken
                    || self.token == SyntaxKind::SemicolonToken
            }
            ParsingContext::TypeArguments => self.token != SyntaxKind::CommaToken,
            ParsingContext::BlockStatements
            | ParsingContext::SwitchClauses
            | ParsingContext::ClassMembers
            | ParsingContext::EnumMembers
            | ParsingContext::ObjectLiteralMembers
            | ParsingContext::ObjectBindingElements
            | ParsingContext::ImportOrExportSpecifiers
            | ParsingContext::ImportAttributes => self.token == SyntaxKind::CloseBraceToken,
            ParsingContext::SwitchClauseStatements => matches!(
                self.token,
                SyntaxKind::CloseBraceToken | SyntaxKind::CaseKeyword | SyntaxKind::DefaultKeyword
            ),
            ParsingContext::HeritageClauseElement => matches!(
                self.token,
                SyntaxKind::OpenBraceToken
                    | SyntaxKind::ExtendsKeyword
                    | SyntaxKind::ImplementsKeyword
            ),
            ParsingContext::VariableDeclarations => {
                self.can_parse_semicolon()
                    || matches!(
                        self.token,
                        SyntaxKind::InKeyword
                            | SyntaxKind::OfKeyword
                            | SyntaxKind::EqualsGreaterThanToken
                    )
            }
            ParsingContext::ArrayBindingElements => self.token == SyntaxKind::CloseBracketToken,
            ParsingContext::HeritageClauses => {
                self.token == SyntaxKind::OpenBraceToken
                    || self.token == SyntaxKind::CloseBraceToken
            }
        }
    }

    // ── Expect and optional ────────────────────────────────────────────

    // Go: parser.go:964 parseExpectedJSDoc
    fn parse_expected_jsdoc(&mut self, kind: SyntaxKind) -> bool {
        if self.token == kind {
            self.next_token_jsdoc();
            return true;
        }
        self.parse_error_at_current_token();
        false
    }

    // Go: jsdoc.go:1312 parseOptionalJsdoc
    fn parse_optional_jsdoc(&mut self, t: SyntaxKind) -> bool {
        if self.token == t {
            self.next_token_jsdoc();
            return true;
        }
        false
    }

    // Go: parser.go:991 parseOptional
    fn parse_optional(&mut self, t: SyntaxKind) -> bool {
        if self.token == t {
            self.next_token();
            return true;
        }
        false
    }

    // Go: parser.go:999 parseExpected
    // PORT: the diagnostic message is not kept, so the Go message choice
    // (and the lookAhead for `=>`-like cases it does not make) is skipped.
    fn parse_expected(&mut self, kind: SyntaxKind) -> bool {
        if self.token == kind {
            self.next_token();
            return true;
        }
        self.parse_error_at_current_token();
        false
    }

    // Go: parser.go:1023 parseTokenNode
    fn parse_token_node(&mut self) -> Node {
        let pos = self.node_pos();
        let kind = self.token;
        self.next_token();
        let n = self.factory.new_token(kind);
        self.finish_node(n, pos)
    }

    // Go: parser.go:1030 parseExpectedToken
    fn parse_expected_token(&mut self, kind: SyntaxKind) -> Node {
        let token = self.parse_optional_token(kind);
        if token.is_nil() {
            self.parse_error_at_current_token();
            let pos = self.node_pos();
            let n = self.factory.new_token(kind);
            return self.finish_node(n, pos);
        }
        token
    }

    // Go: parser.go:1039 parseOptionalToken
    fn parse_optional_token(&mut self, kind: SyntaxKind) -> Node {
        if self.token == kind {
            return self.parse_token_node();
        }
        Node::NIL
    }

    // Go: parser.go:1046 parseExpectedTokenJSDoc
    fn parse_expected_token_jsdoc(&mut self, kind: SyntaxKind) -> Node {
        let optional = self.parse_optional_token_jsdoc(kind);
        if optional.is_nil() {
            self.parse_error_at_current_token();
            let pos = self.node_pos();
            let n = self.factory.new_token(kind);
            return self.finish_node(n, pos);
        }
        optional
    }

    // Go: parser.go:1058 parseOptionalTokenJSDoc
    fn parse_optional_token_jsdoc(&mut self, kind: SyntaxKind) -> Node {
        if self.token == kind {
            return self.parse_token_node();
        }
        Node::NIL
    }

    // Go: parser.go:6037 canParseSemicolon
    fn can_parse_semicolon(&self) -> bool {
        self.token == SyntaxKind::SemicolonToken
            || self.token == SyntaxKind::CloseBraceToken
            || self.token == SyntaxKind::EndOfFile
            || self.has_preceding_line_break()
    }

    // Go: parser.go:6043 tryParseSemicolon
    fn try_parse_semicolon(&mut self) -> bool {
        if !self.can_parse_semicolon() {
            return false;
        }
        if self.token == SyntaxKind::SemicolonToken {
            self.next_token();
        }
        true
    }

    // Go: parser.go:6054 parseSemicolon
    fn parse_semicolon(&mut self) -> bool {
        self.try_parse_semicolon() || self.parse_expected(SyntaxKind::SemicolonToken)
    }

    // ── Identifiers ────────────────────────────────────────────────────

    // Go: parser.go:6273 isIdentifier
    fn is_identifier(&self) -> bool {
        if self.token == SyntaxKind::Identifier {
            return true;
        }
        if self.token == SyntaxKind::YieldKeyword && self.in_yield_context()
            || self.token == SyntaxKind::AwaitKeyword && self.in_await_context()
        {
            return false;
        }
        self.token as u16 > SyntaxKind::LAST_RESERVED_WORD as u16
    }

    // Go: parser.go:6287 isBindingIdentifier
    fn is_binding_identifier(&self) -> bool {
        self.token == SyntaxKind::Identifier
            || self.token as u16 > SyntaxKind::LAST_RESERVED_WORD as u16
    }

    // Go: parser.go:6058 isLiteralPropertyName
    fn is_literal_property_name(&self) -> bool {
        token_is_identifier_or_keyword(self.token)
            || self.token == SyntaxKind::StringLiteral
            || self.token == SyntaxKind::NumericLiteral
            || self.token == SyntaxKind::BigIntLiteral
    }

    // Go: parser.go:2973 newIdentifier
    fn new_identifier(&mut self, text: &str) -> Node {
        self.factory.new_identifier(text)
    }

    // Go: parser.go:2982 createMissingIdentifier
    fn create_missing_identifier(&mut self) -> Node {
        let pos = self.node_pos();
        let n = self.new_identifier("");
        self.finish_node(n, pos)
    }

    // Go: parser.go:5834 parseIdentifierName
    fn parse_identifier_name(&mut self) -> Node {
        self.create_identifier_with_diagnostic(token_is_identifier_or_keyword(self.token), true)
    }

    // Go: parser.go:5842 parseIdentifier
    fn parse_identifier(&mut self) -> Node {
        let is_id = self.is_identifier();
        self.create_identifier_with_diagnostic(is_id, false)
    }

    // Go: parser.go:5827 parseBindingIdentifierWithDiagnostic
    fn parse_binding_identifier(&mut self) -> Node {
        let is_id = self.is_binding_identifier();
        self.create_identifier_with_diagnostic(is_id, false)
    }

    // Go: parser.go:5854 createIdentifierWithDiagnostic
    // PORT: messages are not kept, so the diagnostic arguments are dropped.
    // `_name_only` is unused; it records which Go caller this is.
    fn create_identifier_with_diagnostic(&mut self, is_identifier: bool, _name_only: bool) -> Node {
        if is_identifier {
            let pos = if self
                .sc
                .has_flag(TokenFlags::PRECEDING_JS_DOC_LEADING_ASTERISKS)
            {
                self.sc.st.token_start
            } else {
                self.node_pos()
            };
            let text = self.sc.st.value.clone();
            self.next_token_without_check();
            let n = self.new_identifier(&text);
            return self.finish_node(n, pos);
        }
        if self.token == SyntaxKind::PrivateIdentifier {
            self.parse_error_at_current_token();
            return self.create_identifier_with_diagnostic(true, false);
        }
        // Go reports at the full start at the end of the file.
        if self.token == SyntaxKind::EndOfFile {
            let pos = self.node_pos();
            self.parse_error_at(pos, pos);
        } else {
            self.parse_error_at_current_token();
        }
        self.create_missing_identifier()
    }

    // Go: parser.go:2986 parsePrivateIdentifier
    fn parse_private_identifier(&mut self) -> Node {
        let pos = self.node_pos();
        let text = self.sc.st.value.clone();
        self.next_token();
        let n = self.factory.new_private_identifier(text);
        self.finish_node(n, pos)
    }
}
// ──────────────────────────────────────────────────────────────────────
// JSDoc node constructors (Go `NodeFactory.NewJSDoc*`)
// ──────────────────────────────────────────────────────────────────────

fn id(n: Node) -> ts_ast::NodeId {
    synthetic_child_id(n)
}

fn oid(n: Node) -> Option<ts_ast::NodeId> {
    synthetic_opt_child_id(n)
}

fn opt_list(l: NodeList) -> Option<ts_ast::NodeList> {
    synthetic_list_value(l)
}

fn strings(v: &[String]) -> Vec<String> {
    v.to_vec()
}

// Go: ast/ast_generated.go NewJSDocTypeExpression
fn new_jsdoc_type_expression(t: Node) -> Node {
    alloc_synthetic_node(
        SyntaxKind::JsDocTypeExpression,
        D::JsDocTypeExpression(Box::new(ts_ast::JsDocTypeExpressionData { type_: id(t) })),
    )
}

// Go: ast/ast_generated.go NewJSDocNameReference
fn new_jsdoc_name_reference(name: Node) -> Node {
    alloc_synthetic_node(
        SyntaxKind::JsDocNameReference,
        D::JsDocNameReference(Box::new(ts_ast::JsDocNameReferenceData { name: id(name) })),
    )
}

// Go: ast/ast_generated.go NewJSDocText
fn new_jsdoc_text(text: &[String]) -> Node {
    alloc_synthetic_node(
        SyntaxKind::JsDocText,
        D::JsDocText(Box::new(ts_ast::JsDocTextData {
            text: strings(text),
        })),
    )
}

// Go: ast/ast_generated.go NewJSDoc
fn new_jsdoc(comment: NodeList, tags: NodeList) -> Node {
    alloc_synthetic_node(
        SyntaxKind::JsDoc,
        D::JsDoc(Box::new(ts_ast::JsDocData {
            comment: synthetic_req_list_value(comment),
            tags: opt_list(tags),
        })),
    )
}

// Go: ast/ast_generated.go NewJSDocLink, NewJSDocLinkCode, NewJSDocLinkPlain
fn new_jsdoc_link(kind: &str, name: Node, text: Vec<String>) -> Node {
    match kind {
        "link" => alloc_synthetic_node(
            SyntaxKind::JsDocLink,
            D::JsDocLink(Box::new(ts_ast::JsDocLinkData {
                name: oid(name),
                text,
            })),
        ),
        "linkcode" => alloc_synthetic_node(
            SyntaxKind::JsDocLinkCode,
            D::JsDocLinkCode(Box::new(ts_ast::JsDocLinkCodeData {
                name: oid(name),
                text,
            })),
        ),
        _ => alloc_synthetic_node(
            SyntaxKind::JsDocLinkPlain,
            D::JsDocLinkPlain(Box::new(ts_ast::JsDocLinkPlainData {
                name: oid(name),
                text,
            })),
        ),
    }
}

/// The simple tags: Go `NewJSDoc{Unknown,Public,Private,Protected,Readonly,Override,Deprecated}Tag`.
fn new_jsdoc_simple_tag(kind: SyntaxKind, tag_name: Node, comment: NodeList) -> Node {
    let (tag_name, comment) = (id(tag_name), opt_list(comment));
    let data = match kind {
        SyntaxKind::JsDocUnknownTag => {
            D::JsDocUnknownTag(Box::new(ts_ast::JsDocUnknownTagData { comment, tag_name }))
        }
        SyntaxKind::JsDocPublicTag => {
            D::JsDocPublicTag(Box::new(ts_ast::JsDocPublicTagData { comment, tag_name }))
        }
        SyntaxKind::JsDocPrivateTag => {
            D::JsDocPrivateTag(Box::new(ts_ast::JsDocPrivateTagData { comment, tag_name }))
        }
        SyntaxKind::JsDocProtectedTag => {
            D::JsDocProtectedTag(Box::new(ts_ast::JsDocProtectedTagData {
                comment,
                tag_name,
            }))
        }
        SyntaxKind::JsDocReadonlyTag => {
            D::JsDocReadonlyTag(Box::new(ts_ast::JsDocReadonlyTagData { comment, tag_name }))
        }
        SyntaxKind::JsDocOverrideTag => {
            D::JsDocOverrideTag(Box::new(ts_ast::JsDocOverrideTagData { comment, tag_name }))
        }
        SyntaxKind::JsDocDeprecatedTag => {
            D::JsDocDeprecatedTag(Box::new(ts_ast::JsDocDeprecatedTagData {
                comment,
                tag_name,
            }))
        }
        _ => unreachable!("not a simple JSDoc tag"),
    };
    alloc_synthetic_node(kind, data)
}

// ──────────────────────────────────────────────────────────────────────
// jsdoc.go
// ──────────────────────────────────────────────────────────────────────

impl Parser {
    // Go: jsdoc.go:107 parseJSDocTypeExpression
    fn parse_jsdoc_type_expression(&mut self, may_omit_braces: bool) -> Node {
        let pos = self.node_pos();
        let has_brace = if may_omit_braces {
            self.parse_optional(SyntaxKind::OpenBraceToken)
        } else {
            self.parse_expected(SyntaxKind::OpenBraceToken)
        };
        let save = self.ctx;
        self.set_context_flags(NodeFlags::JS_DOC, true);
        let t = self.parse_jsdoc_type();
        self.ctx = save;
        if has_brace {
            self.parse_expected_jsdoc(SyntaxKind::CloseBraceToken);
        }
        let n = new_jsdoc_type_expression(t);
        self.finish_node(n, pos)
    }

    // Go: jsdoc.go:126 parseJSDocNameReference
    fn parse_jsdoc_name_reference(&mut self) -> Node {
        let pos = self.node_pos();
        let has_brace = self.parse_optional(SyntaxKind::OpenBraceToken);
        let entity_name = self.parse_jsdoc_link_name();
        if has_brace {
            self.parse_expected_jsdoc(SyntaxKind::CloseBraceToken);
        }
        let full_start = self.sc.st.full_start;
        self.sc.reset_pos(full_start);
        self.next_token_jsdoc();
        let n = new_jsdoc_name_reference(entity_name);
        self.finish_node(n, pos)
    }

    // Go: jsdoc.go:193 parseJSDocCommentWorker
    fn parse_jsdoc_comment_worker(
        &mut self,
        start: i32,
        end: i32,
        full_start: i32,
        mut indent: i32,
    ) -> Node {
        let mut tags: Vec<Node> = Vec::new();
        let mut tags_pos = -1;
        let mut tags_end = -1;
        let mut state = JsdocState::SawAsterisk;
        let mut backtick_count = 0;
        let mut in_fenced_code_block = false;
        let mut comment_parts: Vec<Node> = Vec::new();
        let mut comments: Vec<String> = Vec::new();
        let mut comments_pos = -1;
        let mut link_end = start;
        let mut margin = -1;
        let push_comment =
            |comments: &mut Vec<String>, margin: &mut i32, indent: &mut i32, text: &str| {
                if *margin == -1 {
                    *margin = *indent;
                }
                comments.push(text.to_string());
                *indent += text.len() as i32;
            };

        self.next_token_jsdoc();
        while self.parse_optional_jsdoc(SyntaxKind::WhitespaceTrivia) {}
        if self.parse_optional_jsdoc(SyntaxKind::NewLineTrivia) {
            state = JsdocState::BeginningOfLine;
            indent = 0;
        }
        loop {
            if self.token != SyntaxKind::BacktickToken && backtick_count > 0 {
                if backtick_count >= 3 {
                    in_fenced_code_block = !in_fenced_code_block;
                }
                backtick_count = 0;
            }
            match self.token {
                SyntaxKind::AtToken => {
                    if in_fenced_code_block || !self.sc.can_follow_jsdoc_at() {
                        state = if in_fenced_code_block {
                            JsdocState::SavingBackticks
                        } else {
                            JsdocState::SavingComments
                        };
                        push_comment(
                            &mut comments,
                            &mut margin,
                            &mut indent,
                            self.sc.token_text(),
                        );
                    } else {
                        remove_trailing_whitespace(&mut comments);
                        if comments_pos == -1 {
                            comments_pos = self.node_pos();
                        }
                        let tag = self.parse_tag(&tags, indent);
                        if tags_pos == -1 {
                            tags_pos = tag.pos();
                        }
                        tags.push(tag);
                        tags_end = tag.end();
                        state = JsdocState::BeginningOfLine;
                        margin = -1;
                    }
                }
                SyntaxKind::NewLineTrivia => {
                    comments.push(self.sc.token_text().to_string());
                    state = JsdocState::BeginningOfLine;
                    indent = 0;
                }
                SyntaxKind::AsteriskToken => {
                    let asterisk = self.sc.token_text();
                    if state == JsdocState::SawAsterisk {
                        state = JsdocState::SavingComments;
                        push_comment(&mut comments, &mut margin, &mut indent, asterisk);
                    } else {
                        assert!(
                            state == JsdocState::BeginningOfLine,
                            "state must be BeginningOfLine"
                        );
                        state = JsdocState::SawAsterisk;
                        indent += asterisk.len() as i32;
                    }
                }
                SyntaxKind::WhitespaceTrivia => {
                    assert!(
                        state != JsdocState::SavingComments && state != JsdocState::SavingBackticks,
                        "whitespace shouldn't come from the scanner while saving top-level comment text"
                    );
                    let whitespace = self.sc.token_text();
                    let len = whitespace.len() as i32;
                    if margin > -1 && indent + len > margin {
                        let mut existing_indent = margin - indent;
                        if existing_indent < 0 {
                            existing_indent += len;
                        }
                        if existing_indent < 0 {
                            existing_indent = 0;
                        }
                        comments.push(whitespace[existing_indent as usize..].to_string());
                    }
                    indent += len;
                }
                SyntaxKind::EndOfFile => break,
                SyntaxKind::JsDocCommentTextToken => {
                    if state != JsdocState::SavingBackticks {
                        state = if in_fenced_code_block {
                            JsdocState::SavingBackticks
                        } else {
                            JsdocState::SavingComments
                        };
                    }
                    let value = self.sc.st.value.clone();
                    push_comment(&mut comments, &mut margin, &mut indent, &value);
                }
                SyntaxKind::BacktickToken => {
                    backtick_count += 1;
                    state = if state == JsdocState::SavingBackticks {
                        JsdocState::SavingComments
                    } else {
                        JsdocState::SavingBackticks
                    };
                    push_comment(
                        &mut comments,
                        &mut margin,
                        &mut indent,
                        self.sc.token_text(),
                    );
                }
                _ => {
                    let mut fall_through = true;
                    if self.token == SyntaxKind::OpenBraceToken {
                        if in_fenced_code_block {
                            state = JsdocState::SavingBackticks;
                            push_comment(
                                &mut comments,
                                &mut margin,
                                &mut indent,
                                self.sc.token_text(),
                            );
                            fall_through = false;
                        } else {
                            state = JsdocState::SavingComments;
                            let comment_end = self.sc.st.full_start;
                            let link_start = self.sc.st.pos - 1;
                            let link = self.parse_jsdoc_link(link_start);
                            if !link.is_nil() {
                                if link_end == start {
                                    remove_leading_newlines(&mut comments);
                                }
                                let text = new_jsdoc_text(&comments);
                                let jsdoc_text =
                                    self.finish_node_with_end(text, link_end, comment_end);
                                comment_parts.push(jsdoc_text);
                                comment_parts.push(link);
                                comments.clear();
                                link_end = self.sc.st.pos;
                                fall_through = false;
                            }
                        }
                    }
                    if fall_through {
                        if state != JsdocState::SavingBackticks {
                            state = if in_fenced_code_block {
                                JsdocState::SavingBackticks
                            } else {
                                JsdocState::SavingComments
                            };
                        }
                        push_comment(
                            &mut comments,
                            &mut margin,
                            &mut indent,
                            self.sc.token_text(),
                        );
                    }
                }
            }
            if state == JsdocState::SavingComments || state == JsdocState::SavingBackticks {
                self.next_jsdoc_comment_text_token(state == JsdocState::SavingBackticks);
            } else {
                self.next_token_jsdoc();
            }
        }

        if comments_pos == -1 {
            comments_pos = self.sc.st.full_start;
        }
        if let Some(last) = comments.last_mut() {
            *last = last.trim_end_matches(char::is_whitespace).to_string();
            let text = new_jsdoc_text(&comments);
            let jsdoc_text = self.finish_node_with_end(text, link_end, comments_pos);
            comment_parts.push(jsdoc_text);
        }

        let tags_node_list = if tags_pos != -1 {
            self.new_node_list(TextRange::new(tags_pos, tags_end), &tags)
        } else {
            NodeList::NIL
        };
        let comment_list = self.new_node_list(TextRange::new(start, comments_pos), &comment_parts);
        let jsdoc_comment = new_jsdoc(comment_list, tags_node_list);
        self.finish_node_with_end(jsdoc_comment, full_start, end)
    }

    // Go: jsdoc.go:406 isNextNonwhitespaceTokenEndOfFile
    fn is_next_nonwhitespace_token_end_of_file(&mut self) -> bool {
        loop {
            self.next_token_jsdoc();
            if self.token == SyntaxKind::EndOfFile {
                return true;
            }
            if !(self.token == SyntaxKind::WhitespaceTrivia
                || self.token == SyntaxKind::NewLineTrivia)
            {
                return false;
            }
        }
    }

    // Go: jsdoc.go:419 skipWhitespace
    fn skip_whitespace(&mut self) {
        if (self.token == SyntaxKind::WhitespaceTrivia || self.token == SyntaxKind::NewLineTrivia)
            && self.look_ahead(Self::is_next_nonwhitespace_token_end_of_file)
        {
            return;
        }
        while self.token == SyntaxKind::WhitespaceTrivia || self.token == SyntaxKind::NewLineTrivia
        {
            self.next_token_jsdoc();
        }
    }

    // Go: jsdoc.go:431 skipWhitespaceOrAsterisk
    fn skip_whitespace_or_asterisk(&mut self) -> String {
        if (self.token == SyntaxKind::WhitespaceTrivia || self.token == SyntaxKind::NewLineTrivia)
            && self.look_ahead(Self::is_next_nonwhitespace_token_end_of_file)
        {
            return String::new();
        }
        let mut preceding_line_break = self.has_preceding_line_break();
        let mut seen_line_break = false;
        let mut indents: Vec<&'static str> = Vec::new();
        while (preceding_line_break && self.token == SyntaxKind::AsteriskToken)
            || self.token == SyntaxKind::WhitespaceTrivia
            || self.token == SyntaxKind::NewLineTrivia
        {
            indents.push(self.sc.token_text());
            if self.token == SyntaxKind::NewLineTrivia {
                preceding_line_break = true;
                seen_line_break = true;
                indents.clear();
            } else if self.token == SyntaxKind::AsteriskToken {
                preceding_line_break = false;
            }
            self.next_token_jsdoc();
        }
        if seen_line_break {
            indents.concat()
        } else {
            String::new()
        }
    }

    // Go: jsdoc.go:460 parseTag
    fn parse_tag(&mut self, tags: &[Node], margin: i32) -> Node {
        assert!(
            self.token == SyntaxKind::AtToken,
            "should be called only at the start of a tag"
        );
        let start = self.sc.st.token_start;
        self.next_token_jsdoc();

        let tag_name = self.parse_jsdoc_identifier_name(true);
        let indent_text = self.skip_whitespace_or_asterisk();

        let simple = |p: &mut Self, kind: SyntaxKind| {
            p.parse_simple_tag(start, kind, tag_name, margin, &indent_text)
        };
        match tag_name.text() {
            "implements" => self.parse_implements_tag(start, tag_name, margin, &indent_text),
            "augments" | "extends" => {
                self.parse_augments_tag(start, tag_name, margin, &indent_text)
            }
            "public" => simple(self, SyntaxKind::JsDocPublicTag),
            "private" => simple(self, SyntaxKind::JsDocPrivateTag),
            "protected" => simple(self, SyntaxKind::JsDocProtectedTag),
            "readonly" => simple(self, SyntaxKind::JsDocReadonlyTag),
            "override" => simple(self, SyntaxKind::JsDocOverrideTag),
            "deprecated" => {
                self.has_deprecated_tag = true;
                simple(self, SyntaxKind::JsDocDeprecatedTag)
            }
            "this" => self.parse_this_tag(start, tag_name, margin, &indent_text),
            "arg" | "argument" | "param" => self.parse_parameter_or_property_tag(
                start,
                tag_name,
                PROPERTY_LIKE_PARSE_PARAMETER,
                margin,
            ),
            "return" | "returns" => {
                self.parse_return_tag(tags, start, tag_name, margin, &indent_text)
            }
            "template" => self.parse_template_tag(start, tag_name, margin, &indent_text),
            "type" => self.parse_type_tag(tags, start, tag_name, margin, &indent_text),
            "typedef" => self.parse_typedef_tag(start, tag_name, margin, &indent_text),
            "callback" => self.parse_callback_tag(start, tag_name, margin, &indent_text),
            "overload" => self.parse_overload_tag(start, tag_name, margin, &indent_text),
            "satisfies" => self.parse_satisfies_tag(start, tag_name, margin, &indent_text),
            "see" => self.parse_see_tag(start, tag_name, margin, &indent_text),
            "exception" | "throws" => self.parse_throws_tag(start, tag_name, margin, &indent_text),
            "import" => self.parse_import_tag(start, tag_name, margin, &indent_text),
            _ => self.parse_unknown_tag(start, tag_name, margin, &indent_text),
        }
    }

    // Go: jsdoc.go:534 parseTrailingTagComments
    fn parse_trailing_tag_comments(
        &mut self,
        pos: i32,
        end: i32,
        mut margin: i32,
        indent_text: &str,
    ) -> NodeList {
        if indent_text.is_empty() {
            margin += end - pos;
        }
        let initial_margin = if (margin as usize) < indent_text.len() {
            indent_text[margin as usize..].to_string()
        } else {
            String::new()
        };
        self.parse_tag_comments(margin, Some(initial_margin))
    }

    // Go: jsdoc.go:546 parseTagComments
    fn parse_tag_comments(&mut self, mut indent: i32, initial_margin: Option<String>) -> NodeList {
        let comments_pos = self.node_pos();
        let mut comments: Vec<String> = Vec::new();
        let mut parts: Vec<Node> = Vec::new();
        let mut link_end = -1;
        let mut state = JsdocState::BeginningOfLine;
        let mut backtick_count = 0;
        let mut in_fenced_code_block = false;
        assert!(indent >= 0, "indent must be a natural number");
        let mut margin = -1;
        let push_comment =
            |comments: &mut Vec<String>, margin: &mut i32, indent: &mut i32, text: &str| {
                if *margin == -1 {
                    *margin = *indent;
                }
                comments.push(text.to_string());
                *indent += text.len() as i32;
            };

        if let Some(initial_margin) = initial_margin {
            if !initial_margin.is_empty() {
                push_comment(&mut comments, &mut margin, &mut indent, &initial_margin);
            }
            state = JsdocState::SawAsterisk;
        }
        let mut tok = self.token;
        loop {
            if tok != SyntaxKind::BacktickToken && backtick_count > 0 {
                if backtick_count >= 3 {
                    in_fenced_code_block = !in_fenced_code_block;
                }
                backtick_count = 0;
            }
            let saving = if in_fenced_code_block {
                JsdocState::SavingBackticks
            } else {
                JsdocState::SavingComments
            };
            match tok {
                SyntaxKind::NewLineTrivia => {
                    state = JsdocState::BeginningOfLine;
                    comments.push(self.sc.token_text().to_string());
                    indent = 0;
                }
                SyntaxKind::AtToken => {
                    if !in_fenced_code_block && self.sc.can_follow_jsdoc_at() {
                        let pos = self.sc.st.pos - 1;
                        self.sc.reset_pos(pos);
                        break;
                    }
                    state = saving;
                    push_comment(
                        &mut comments,
                        &mut margin,
                        &mut indent,
                        self.sc.token_text(),
                    );
                }
                SyntaxKind::EndOfFile => break,
                SyntaxKind::WhitespaceTrivia => {
                    assert!(
                        state != JsdocState::SavingComments && state != JsdocState::SavingBackticks,
                        "whitespace shouldn't come from the scanner while saving comment text"
                    );
                    let whitespace = self.sc.token_text();
                    let len = whitespace.len() as i32;
                    if margin > -1 && indent + len > margin {
                        comments.push(whitespace[(margin - indent).max(0) as usize..].to_string());
                        state = saving;
                    }
                    indent += len;
                }
                SyntaxKind::OpenBraceToken => {
                    if in_fenced_code_block {
                        state = JsdocState::SavingBackticks;
                        push_comment(
                            &mut comments,
                            &mut margin,
                            &mut indent,
                            self.sc.token_text(),
                        );
                    } else {
                        state = JsdocState::SavingComments;
                        let comment_end = self.sc.st.full_start;
                        let link_start = self.sc.st.pos - 1;
                        let link = self.parse_jsdoc_link(link_start);
                        if !link.is_nil() {
                            let comment_start = if link_end > -1 {
                                link_end
                            } else {
                                comments_pos
                            };
                            let t = new_jsdoc_text(&comments);
                            let text = self.finish_node_with_end(t, comment_start, comment_end);
                            parts.push(text);
                            parts.push(link);
                            comments.clear();
                            link_end = self.sc.st.pos;
                        } else {
                            push_comment(
                                &mut comments,
                                &mut margin,
                                &mut indent,
                                self.sc.token_text(),
                            );
                        }
                    }
                }
                SyntaxKind::BacktickToken => {
                    backtick_count += 1;
                    state = if state == JsdocState::SavingBackticks {
                        JsdocState::SavingComments
                    } else {
                        JsdocState::SavingBackticks
                    };
                    push_comment(
                        &mut comments,
                        &mut margin,
                        &mut indent,
                        self.sc.token_text(),
                    );
                }
                SyntaxKind::JsDocCommentTextToken => {
                    if state != JsdocState::SavingBackticks {
                        state = saving;
                    }
                    let value = self.sc.st.value.clone();
                    push_comment(&mut comments, &mut margin, &mut indent, &value);
                }
                SyntaxKind::AsteriskToken if state == JsdocState::BeginningOfLine => {
                    state = JsdocState::SawAsterisk;
                    indent += 1;
                }
                _ => {
                    if state != JsdocState::SavingBackticks {
                        state = saving;
                    }
                    push_comment(
                        &mut comments,
                        &mut margin,
                        &mut indent,
                        self.sc.token_text(),
                    );
                }
            }
            tok = if state == JsdocState::SavingComments || state == JsdocState::SavingBackticks {
                self.next_jsdoc_comment_text_token(state == JsdocState::SavingBackticks)
            } else {
                self.next_token_jsdoc()
            };
        }

        remove_leading_newlines(&mut comments);
        remove_trailing_whitespace(&mut comments);
        if !comments.is_empty() {
            let comment_start = if link_end > -1 {
                link_end
            } else {
                comments_pos
            };
            let t = new_jsdoc_text(&comments);
            let text = self.finish_node(t, comment_start);
            parts.push(text);
        }
        if !parts.is_empty() {
            return self.new_node_list(TextRange::new(comments_pos, self.sc.st.pos), &parts);
        }
        NodeList::NIL
    }

    // Go: jsdoc.go:713 parseJSDocLink
    fn parse_jsdoc_link(&mut self, start: i32) -> Node {
        let state = self.mark();
        let Some(link_type) = self.parse_jsdoc_link_prefix() else {
            self.rewind(state);
            return Node::NIL;
        };
        self.next_token_jsdoc();
        self.skip_whitespace();
        let name = self.parse_jsdoc_link_name();
        let mut text = Vec::new();
        while self.token != SyntaxKind::CloseBraceToken
            && self.token != SyntaxKind::NewLineTrivia
            && self.token != SyntaxKind::EndOfFile
        {
            text.push(self.sc.token_text().to_string());
            self.next_token_jsdoc();
        }
        let create = new_jsdoc_link(&link_type, name, text);
        let end = self.sc.st.pos;
        self.finish_node_with_end(create, start, end)
    }

    // Go: jsdoc.go:741 parseJSDocLinkName
    fn parse_jsdoc_link_name(&mut self) -> Node {
        if token_is_identifier_or_keyword(self.token) {
            let pos = self.node_pos();
            let mut name = self.parse_identifier_name();
            while self.parse_optional(SyntaxKind::DotToken) {
                let right = if self.token == SyntaxKind::PrivateIdentifier {
                    self.create_missing_identifier()
                } else {
                    self.parse_identifier_name()
                };
                let q = self.factory.new_qualified_name(name, right);
                name = self.finish_node(q, pos);
            }
            while self.token == SyntaxKind::PrivateIdentifier {
                self.sc.rescan_hash_token();
                self.next_token_jsdoc();
                let right = self.parse_identifier();
                let q = self.factory.new_qualified_name(name, right);
                name = self.finish_node(q, pos);
            }
            return name;
        }
        Node::NIL
    }

    // Go: jsdoc.go:764 parseJSDocLinkPrefix
    /// Returns the link kind when the token starts `{@link`, `{@linkcode` or `{@linkplain`.
    fn parse_jsdoc_link_prefix(&mut self) -> Option<String> {
        self.skip_whitespace_or_asterisk();
        if self.token == SyntaxKind::OpenBraceToken
            && self.next_token_jsdoc() == SyntaxKind::AtToken
            && token_is_identifier_or_keyword(self.next_token_jsdoc())
        {
            let kind = self.sc.st.value.clone();
            if is_jsdoc_link_tag(&kind) {
                return Some(kind);
            }
        }
        None
    }

    // Go: jsdoc.go:779 parseUnknownTag
    fn parse_unknown_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        indent: i32,
        indent_text: &str,
    ) -> Node {
        let pos = self.node_pos();
        let comment = self.parse_trailing_tag_comments(start, pos, indent, indent_text);
        let n = new_jsdoc_simple_tag(SyntaxKind::JsDocUnknownTag, tag_name, comment);
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:783 tryParseTypeExpression
    fn try_parse_type_expression(&mut self) -> Node {
        self.skip_whitespace_or_asterisk();
        if self.token == SyntaxKind::OpenBraceToken {
            return self.parse_jsdoc_type_expression(false);
        }
        Node::NIL
    }

    // Go: jsdoc.go:792 parseBracketNameInPropertyAndParamTag
    fn parse_bracket_name_in_property_and_param_tag(&mut self, target: u8) -> (Node, bool) {
        let is_bracketed = self.parse_optional_jsdoc(SyntaxKind::OpenBracketToken);
        if is_bracketed {
            self.skip_whitespace();
        }
        let is_backquoted = self.parse_optional_jsdoc(SyntaxKind::BacktickToken);
        let name = self.parse_jsdoc_entity_name(target != PROPERTY_LIKE_PARSE_PARAMETER);
        if is_backquoted {
            self.parse_expected_token_jsdoc(SyntaxKind::BacktickToken);
        }
        if is_bracketed {
            self.skip_whitespace();
            if !self.parse_optional_token(SyntaxKind::EqualsToken).is_nil() {
                self.parse_expression();
            }
            self.parse_expected(SyntaxKind::CloseBracketToken);
        }
        (name, is_bracketed)
    }

    // Go: jsdoc.go:832 parseParameterOrPropertyTag
    fn parse_parameter_or_property_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        target: u8,
        indent: i32,
    ) -> Node {
        let mut type_expression = self.try_parse_type_expression();
        let mut is_name_first = type_expression.is_nil();
        self.skip_whitespace_or_asterisk();

        let (name, is_bracketed) = self.parse_bracket_name_in_property_and_param_tag(target);
        let indent_text = self.skip_whitespace_or_asterisk();

        if is_name_first && self.look_ahead(|p| p.parse_jsdoc_link_prefix().is_none()) {
            type_expression = self.try_parse_type_expression();
        }

        let pos = self.node_pos();
        let comment = self.parse_trailing_tag_comments(start, pos, indent, &indent_text);

        let nested_type_literal =
            self.parse_nested_type_literal(type_expression, name, target, indent);
        if !nested_type_literal.is_nil() {
            type_expression = nested_type_literal;
            is_name_first = true;
        }
        let kind = if target == PROPERTY_LIKE_PARSE_PROPERTY {
            SyntaxKind::JsDocPropertyTag
        } else {
            SyntaxKind::JsDocParameterTag
        };
        let result = alloc_synthetic_node(
            kind,
            D::JsDocParameterOrPropertyTag(Box::new(ts_ast::JsDocParameterOrPropertyTagData {
                comment: opt_list(comment),
                is_bracketed,
                is_name_first,
                tag_name: id(tag_name),
                type_expression: oid(type_expression),
                name: id(name),
            })),
        );
        self.finish_node(result, start)
    }

    // Go: jsdoc.go:857 parseNestedTypeLiteral
    fn parse_nested_type_literal(
        &mut self,
        type_expression: Node,
        name: Node,
        target: u8,
        indent: i32,
    ) -> Node {
        if !type_expression.is_nil()
            && is_object_or_object_array_type_reference(type_expression.type_())
        {
            let pos = self.node_pos();
            let mut children: Vec<Node> = Vec::new();
            loop {
                let state = self.mark();
                let child = self.parse_child_parameter_or_property_tag(target, indent, name);
                if child.is_nil() {
                    self.rewind(state);
                    break;
                }
                match child.kind() {
                    SyntaxKind::JsDocParameterTag | SyntaxKind::JsDocPropertyTag => {
                        children.push(child)
                    }
                    SyntaxKind::JsDocTemplateTag => {
                        self.parse_error_at_range(child.tag_name().pos())
                    }
                    _ => {}
                }
            }
            if !children.is_empty() {
                let is_array = type_expression.type_().kind() == SyntaxKind::ArrayType;
                let lit = new_jsdoc_type_literal(Some(&children), is_array);
                let literal = self.finish_node(lit, pos);
                let te = new_jsdoc_type_expression(literal);
                return self.finish_node(te, pos);
            }
        }
        Node::NIL
    }

    // Go: jsdoc.go:883 parseReturnTag
    fn parse_return_tag(
        &mut self,
        previous_tags: &[Node],
        start: i32,
        tag_name: Node,
        indent: i32,
        indent_text: &str,
    ) -> Node {
        if previous_tags
            .iter()
            .any(|t| t.kind() == SyntaxKind::JsDocReturnTag)
        {
            let end = self.sc.st.token_start;
            self.parse_error_at(tag_name.pos(), end);
        }
        let type_expression = self.try_parse_type_expression();
        let pos = self.node_pos();
        let comment = self.parse_trailing_tag_comments(start, pos, indent, indent_text);
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocReturnTag,
            D::JsDocReturnTag(Box::new(ts_ast::JsDocReturnTagData {
                comment: opt_list(comment),
                tag_name: id(tag_name),
                type_expression: oid(type_expression),
            })),
        );
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:893 parseTypeTag
    fn parse_type_tag(
        &mut self,
        previous_tags: &[Node],
        start: i32,
        tag_name: Node,
        indent: i32,
        indent_text: &str,
    ) -> Node {
        if previous_tags
            .iter()
            .any(|t| t.kind() == SyntaxKind::JsDocTypeTag)
        {
            let end = self.sc.st.token_start;
            self.parse_error_at(tag_name.pos(), end);
        }
        let type_expression = self.parse_jsdoc_type_expression(true);
        let comments = if indent != -1 {
            let pos = self.node_pos();
            self.parse_trailing_tag_comments(start, pos, indent, indent_text)
        } else {
            NodeList::NIL
        };
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocTypeTag,
            D::JsDocTypeTag(Box::new(ts_ast::JsDocTypeTagData {
                comment: opt_list(comments),
                tag_name: id(tag_name),
                type_expression: id(type_expression),
            })),
        );
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:906 parseSeeTag
    fn parse_see_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        indent: i32,
        indent_text: &str,
    ) -> Node {
        let has_name_reference = self.is_identifier()
            && !self.sc.text[self.sc.st.pos as usize..].starts_with("://")
            || self.token == SyntaxKind::OpenBraceToken
                && self.look_ahead(Self::next_token_is_identifier_or_keyword);
        let name_expression = if has_name_reference {
            self.parse_jsdoc_name_reference()
        } else {
            Node::NIL
        };
        let pos = self.node_pos();
        let comments = self.parse_trailing_tag_comments(start, pos, indent, indent_text);
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocSeeTag,
            D::JsDocSeeTag(Box::new(ts_ast::JsDocSeeTagData {
                comment: opt_list(comments),
                name_expression: id(name_expression),
                tag_name: id(tag_name),
            })),
        );
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:917 parseImplementsTag
    fn parse_implements_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        margin: i32,
        indent_text: &str,
    ) -> Node {
        let class_name = self.parse_expression_with_type_arguments_for_augments();
        let pos = self.node_pos();
        let comment = self.parse_trailing_tag_comments(start, pos, margin, indent_text);
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocImplementsTag,
            D::JsDocImplementsTag(Box::new(ts_ast::JsDocImplementsTagData {
                class_name: id(class_name),
                comment: opt_list(comment),
                tag_name: id(tag_name),
            })),
        );
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:922 parseAugmentsTag
    fn parse_augments_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        margin: i32,
        indent_text: &str,
    ) -> Node {
        let class_name = self.parse_expression_with_type_arguments_for_augments();
        let pos = self.node_pos();
        let comment = self.parse_trailing_tag_comments(start, pos, margin, indent_text);
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocAugmentsTag,
            D::JsDocAugmentsTag(Box::new(ts_ast::JsDocAugmentsTagData {
                class_name: id(class_name),
                comment: opt_list(comment),
                tag_name: id(tag_name),
            })),
        );
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:927 parseSatisfiesTag
    fn parse_satisfies_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        margin: i32,
        indent_text: &str,
    ) -> Node {
        let type_expression = self.parse_jsdoc_type_expression(false);
        let pos = self.node_pos();
        let comments = self.parse_trailing_tag_comments(start, pos, margin, indent_text);
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocSatisfiesTag,
            D::JsDocSatisfiesTag(Box::new(ts_ast::JsDocSatisfiesTagData {
                comment: opt_list(comments),
                tag_name: id(tag_name),
                type_expression: id(type_expression),
            })),
        );
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:933 parseThrowsTag
    fn parse_throws_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        margin: i32,
        indent_text: &str,
    ) -> Node {
        let type_expression = self.try_parse_type_expression();
        let pos = self.node_pos();
        let comment = self.parse_trailing_tag_comments(start, pos, margin, indent_text);
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocThrowsTag,
            D::JsDocThrowsTag(Box::new(ts_ast::JsDocThrowsTagData {
                comment: opt_list(comment),
                tag_name: id(tag_name),
                type_expression: oid(type_expression),
            })),
        );
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:955 parseExpressionWithTypeArgumentsForAugments
    fn parse_expression_with_type_arguments_for_augments(&mut self) -> Node {
        let used_brace = self.parse_optional(SyntaxKind::OpenBraceToken);
        let pos = self.node_pos();
        let expression = self.parse_property_access_entity_name_expression();
        self.sc.set_skip_jsdoc_leading_asterisks(true);
        let type_arguments = self.parse_type_arguments();
        self.sc.set_skip_jsdoc_leading_asterisks(false);
        let e = self
            .factory
            .new_expression_with_type_arguments(expression, type_arguments);
        let node = self.finish_node(e, pos);
        if used_brace {
            self.skip_whitespace();
            self.parse_expected(SyntaxKind::CloseBraceToken);
        }
        node
    }

    // Go: jsdoc.go:970 parsePropertyAccessEntityNameExpression
    fn parse_property_access_entity_name_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let mut node = self.parse_jsdoc_identifier_name(true);
        while self.parse_optional(SyntaxKind::DotToken) {
            let name = self.parse_jsdoc_identifier_name(true);
            let e =
                self.factory
                    .new_property_access_expression(node, Node::NIL, name, NodeFlags::NONE);
            node = self.finish_node(e, pos);
        }
        node
    }

    // Go: jsdoc.go:980 parseSimpleTag
    fn parse_simple_tag(
        &mut self,
        start: i32,
        kind: SyntaxKind,
        tag_name: Node,
        margin: i32,
        indent_text: &str,
    ) -> Node {
        let pos = self.node_pos();
        let comment = self.parse_trailing_tag_comments(start, pos, margin, indent_text);
        let n = new_jsdoc_simple_tag(kind, tag_name, comment);
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:984 parseThisTag
    fn parse_this_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        margin: i32,
        indent_text: &str,
    ) -> Node {
        let type_expression = self.parse_jsdoc_type_expression(true);
        self.skip_whitespace();
        let pos = self.node_pos();
        let comment = self.parse_trailing_tag_comments(start, pos, margin, indent_text);
        let result = alloc_synthetic_node(
            SyntaxKind::JsDocThisTag,
            D::JsDocThisTag(Box::new(ts_ast::JsDocThisTagData {
                comment: opt_list(comment),
                tag_name: id(tag_name),
                type_expression: id(type_expression),
            })),
        );
        self.finish_node(result, start)
    }

    // Go: jsdoc.go:991 parseJSDocTypeNameWithNamespace
    fn parse_jsdoc_type_name_with_namespace(&mut self, nested: bool) -> Node {
        let start = self.sc.st.token_start;
        if !token_is_identifier_or_keyword(self.token) {
            return Node::NIL;
        }
        let type_name_or_namespace_name = self.parse_jsdoc_identifier_name(false);
        if self.parse_optional_jsdoc(SyntaxKind::DotToken) {
            let body = self.parse_jsdoc_type_name_with_namespace(true);
            let ns = self.factory.new_module_declaration(
                ModifierList::NIL,
                SyntaxKind::NamespaceKeyword,
                type_name_or_namespace_name,
                body,
            );
            if nested {
                set_node_flags(ns, ns.flags() | NodeFlags::NESTED_NAMESPACE);
            }
            return self.finish_node(ns, start);
        }
        if nested {
            set_node_flags(
                type_name_or_namespace_name,
                type_name_or_namespace_name.flags() | NodeFlags::IDENTIFIER_IS_IN_JS_DOC_NAMESPACE,
            );
        }
        type_name_or_namespace_name
    }

    // Go: jsdoc.go:1016 parseTypedefTag
    fn parse_typedef_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        indent: i32,
        indent_text: &str,
    ) -> Node {
        let mut type_expression = self.try_parse_type_expression();
        self.skip_whitespace_or_asterisk();
        let mut full_name = self.parse_jsdoc_type_name_with_namespace(false);
        if full_name.is_nil() {
            full_name = self.parse_jsdoc_identifier_name(true);
        }
        self.skip_whitespace();
        let mut comment = self.parse_tag_comments(indent, None);

        let mut end = -1;
        let mut has_children = false;
        if type_expression.is_nil()
            || is_object_or_object_array_type_reference(type_expression.type_())
        {
            let mut child_type_tag = Node::NIL;
            let mut jsdoc_property_tags: Vec<Node> = Vec::new();
            loop {
                let state = self.mark();
                let child = self.parse_child_property_tag(indent);
                if child.is_nil() {
                    self.rewind(state);
                    break;
                }
                has_children = true;
                match child.kind() {
                    SyntaxKind::JsDocTemplateTag => {
                        self.parse_error_at_range(child.tag_name().pos())
                    }
                    SyntaxKind::JsDocTypeTag => {
                        if child_type_tag.is_nil() {
                            child_type_tag = child;
                        } else {
                            self.parse_error_at_current_token();
                        }
                    }
                    _ => jsdoc_property_tags.push(child),
                }
            }
            if has_children {
                let is_array_type = !type_expression.is_nil()
                    && type_expression.type_().kind() == SyntaxKind::ArrayType;
                let jsdoc_type_literal =
                    new_jsdoc_type_literal(Some(&jsdoc_property_tags), is_array_type);
                if !child_type_tag.is_nil()
                    && !child_type_tag.type_expression().is_nil()
                    && !is_object_or_object_array_type_reference(
                        child_type_tag.type_expression().type_(),
                    )
                {
                    type_expression = child_type_tag.type_expression();
                } else {
                    let pos = jsdoc_property_tags.first().map_or(start, |t| t.pos());
                    type_expression = self.finish_node(jsdoc_type_literal, pos);
                }
                end = type_expression.end();
            }
        }

        if end == -1 {
            end = if has_children && !type_expression.is_nil() {
                type_expression.end()
            } else if !comment.is_nil() {
                self.node_pos()
            } else if !full_name.is_nil() {
                full_name.end()
            } else if !type_expression.is_nil() {
                type_expression.end()
            } else {
                tag_name.end()
            };
        }

        if comment.is_nil() {
            comment = self.parse_trailing_tag_comments(start, end, indent, indent_text);
        }

        let n = alloc_synthetic_node(
            SyntaxKind::JsDocTypedefTag,
            D::JsDocTypedefTag(Box::new(ts_ast::JsDocTypedefTagData {
                comment: opt_list(comment),
                tag_name: id(tag_name),
                type_expression: oid(type_expression),
                name: oid(full_name),
            })),
        );
        let typedef_tag = self.finish_node_with_end(n, start, end);
        if !type_expression.is_nil() {
            set_node_parent(type_expression, typedef_tag);
        }
        typedef_tag
    }

    // Go: jsdoc.go:1100 parseCallbackTagParameters
    fn parse_callback_tag_parameters(&mut self, indent: i32) -> NodeList {
        let mut parameters: Vec<Node> = Vec::new();
        let pos = self.node_pos();
        loop {
            let state = self.mark();
            let child = self.parse_child_parameter_or_property_tag(
                PROPERTY_LIKE_PARSE_CALLBACK_PARAMETER,
                indent,
                Node::NIL,
            );
            if child.is_nil() {
                self.rewind(state);
                break;
            }
            if child.kind() == SyntaxKind::JsDocTemplateTag {
                self.parse_error_at_range(child.tag_name().pos());
            } else {
                parameters.push(child);
            }
        }
        let end = self.node_pos();
        self.new_node_list(TextRange::new(pos, end), &parameters)
    }

    // Go: jsdoc.go:1120 parseJSDocSignature
    fn parse_jsdoc_signature(&mut self, start: i32, indent: i32) -> Node {
        let parameters = self.parse_callback_tag_parameters(indent);
        let mut return_tag = Node::NIL;
        let state = self.mark();
        if self.parse_optional_jsdoc(SyntaxKind::AtToken) {
            let tag = self.parse_tag(&[], indent);
            if tag.kind() == SyntaxKind::JsDocReturnTag {
                return_tag = tag;
            }
        }
        if return_tag.is_nil() {
            self.rewind(state);
        }
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocSignature,
            D::JsDocSignature(Box::new(ts_ast::JsDocSignatureData {
                full_signature: None,
                locals: Default::default(),
                next_container: None,
                parameters: synthetic_req_list_value(parameters),
                symbol: None,
                type_: oid(return_tag),
                type_parameters: None,
            })),
        );
        self.finish_node(n, start)
    }

    // Go: jsdoc.go:1136 parseCallbackTag
    fn parse_callback_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        indent: i32,
        indent_text: &str,
    ) -> Node {
        let mut full_name = self.parse_jsdoc_type_name_with_namespace(false);
        if full_name.is_nil() {
            full_name = self.parse_jsdoc_identifier_name(true);
        }
        self.skip_whitespace();
        let mut comment = self.parse_tag_comments(indent, None);
        let pos = self.node_pos();
        let type_expression = self.parse_jsdoc_signature(pos, indent);
        if comment.is_nil() {
            let pos = self.node_pos();
            comment = self.parse_trailing_tag_comments(start, pos, indent, indent_text);
        }
        let end = if !comment.is_nil() {
            self.node_pos()
        } else {
            type_expression.end()
        };
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocCallbackTag,
            D::JsDocCallbackTag(Box::new(ts_ast::JsDocCallbackTagData {
                comment: opt_list(comment),
                tag_name: id(tag_name),
                type_expression: id(type_expression),
                name: oid(full_name),
            })),
        );
        self.finish_node_with_end(n, start, end)
    }

    // Go: jsdoc.go:1156 parseOverloadTag
    fn parse_overload_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        indent: i32,
        indent_text: &str,
    ) -> Node {
        self.skip_whitespace();
        let mut comment = self.parse_tag_comments(indent, None);
        let type_expression = self.parse_jsdoc_signature(start, indent);
        if comment.is_nil() {
            let pos = self.node_pos();
            comment = self.parse_trailing_tag_comments(start, pos, indent, indent_text);
        }
        let end = if !comment.is_nil() {
            self.node_pos()
        } else {
            type_expression.end()
        };
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocOverloadTag,
            D::JsDocOverloadTag(Box::new(ts_ast::JsDocOverloadTagData {
                comment: opt_list(comment),
                tag_name: id(tag_name),
                type_expression: id(type_expression),
            })),
        );
        self.finish_node_with_end(n, start, end)
    }

    // Go: jsdoc.go:1184 parseChildPropertyTag
    fn parse_child_property_tag(&mut self, indent: i32) -> Node {
        self.parse_child_parameter_or_property_tag(PROPERTY_LIKE_PARSE_PROPERTY, indent, Node::NIL)
    }

    // Go: jsdoc.go:1188 parseChildParameterOrPropertyTag
    fn parse_child_parameter_or_property_tag(
        &mut self,
        target: u8,
        indent: i32,
        name: Node,
    ) -> Node {
        let mut can_parse_tag = true;
        let mut seen_asterisk = false;
        loop {
            match self.next_token_jsdoc() {
                SyntaxKind::AtToken => {
                    if can_parse_tag && self.sc.can_follow_jsdoc_at() {
                        let child = self.try_parse_child_tag(target, indent);
                        if !child.is_nil()
                            && !name.is_nil()
                            && (child.kind() == SyntaxKind::JsDocParameterTag
                                || child.kind() == SyntaxKind::JsDocPropertyTag)
                            && (child.name().kind() == SyntaxKind::Identifier
                                || !texts_equal(name, child.name().left()))
                        {
                            return Node::NIL;
                        }
                        return child;
                    }
                    seen_asterisk = false;
                }
                SyntaxKind::NewLineTrivia => {
                    can_parse_tag = true;
                    seen_asterisk = false;
                }
                SyntaxKind::AsteriskToken => {
                    if seen_asterisk {
                        can_parse_tag = false;
                    }
                    seen_asterisk = true;
                }
                SyntaxKind::Identifier => can_parse_tag = false,
                SyntaxKind::EndOfFile => return Node::NIL,
                _ => {}
            }
        }
    }

    // Go: jsdoc.go:1220 tryParseChildTag
    fn try_parse_child_tag(&mut self, target: u8, indent: i32) -> Node {
        assert!(
            self.token == SyntaxKind::AtToken,
            "should only be called when at @"
        );
        let start = self.sc.st.full_start;
        self.next_token_jsdoc();

        let tag_name = self.parse_jsdoc_identifier_name(true);
        let indent_text = self.skip_whitespace_or_asterisk();
        let t = match tag_name.text() {
            "type" => {
                if target == PROPERTY_LIKE_PARSE_PROPERTY {
                    return self.parse_type_tag(&[], start, tag_name, -1, "");
                }
                0
            }
            "prop" | "property" => PROPERTY_LIKE_PARSE_PROPERTY,
            "arg" | "argument" | "param" => {
                PROPERTY_LIKE_PARSE_PARAMETER | PROPERTY_LIKE_PARSE_CALLBACK_PARAMETER
            }
            "template" => return self.parse_template_tag(start, tag_name, indent, &indent_text),
            "this" => return self.parse_this_tag(start, tag_name, indent, &indent_text),
            _ => return Node::NIL,
        };
        if target & t == 0 {
            return Node::NIL;
        }
        self.parse_parameter_or_property_tag(start, tag_name, target, indent)
    }

    // Go: jsdoc.go:1252 parseTemplateTagTypeParameter
    fn parse_template_tag_type_parameter(&mut self) -> Node {
        let type_parameter_pos = self.node_pos();
        let is_bracketed = self.parse_optional_jsdoc(SyntaxKind::OpenBracketToken);
        if is_bracketed {
            self.skip_whitespace();
        }
        let modifiers = self.parse_modifiers_ex(false, true, false);
        let name = self.parse_jsdoc_identifier_name(true);
        let mut default_type = Node::NIL;
        if is_bracketed {
            self.skip_whitespace();
            self.parse_expected(SyntaxKind::EqualsToken);
            let save = self.ctx;
            self.set_context_flags(NodeFlags::JS_DOC, true);
            default_type = self.parse_jsdoc_type();
            self.ctx = save;
            self.parse_expected(SyntaxKind::CloseBracketToken);
        }
        if node_is_missing(name) {
            return Node::NIL;
        }
        let n = self.factory.new_type_parameter_declaration(
            modifiers,
            name,
            Node::NIL,
            Node::NIL,
            default_type,
        );
        self.finish_node(n, type_parameter_pos)
    }

    // Go: jsdoc.go:1278 parseTemplateTagTypeParameters
    fn parse_template_tag_type_parameters(&mut self) -> NodeList {
        let mut nodes: Vec<Node> = Vec::new();
        loop {
            self.skip_whitespace();
            let node = self.parse_template_tag_type_parameter();
            if !node.is_nil() {
                nodes.push(node);
            }
            self.skip_whitespace_or_asterisk();
            if !self.parse_optional_jsdoc(SyntaxKind::CommaToken) {
                break;
            }
        }
        // Go builds `ast.TypeParameterList{}`, whose Loc is the zero range.
        self.new_node_list(TextRange::new(0, 0), &nodes)
    }

    // Go: jsdoc.go:1291 parseTemplateTag
    fn parse_template_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        indent: i32,
        indent_text: &str,
    ) -> Node {
        let constraint = if self.token == SyntaxKind::OpenBraceToken {
            self.parse_jsdoc_type_expression(false)
        } else {
            Node::NIL
        };
        let type_parameters = self.parse_template_tag_type_parameters();
        let pos = self.node_pos();
        let comment = self.parse_trailing_tag_comments(start, pos, indent, indent_text);
        let result = alloc_synthetic_node(
            SyntaxKind::JsDocTemplateTag,
            D::JsDocTemplateTag(Box::new(ts_ast::JsDocTemplateTagData {
                comment: opt_list(comment),
                constraint: id(constraint),
                tag_name: id(tag_name),
                type_parameters: synthetic_req_list_value(type_parameters),
            })),
        );
        self.finish_node(result, start)
    }

    // Go: jsdoc.go:1320 parseJSDocEntityName
    fn parse_jsdoc_entity_name(&mut self, has_message: bool) -> Node {
        let mut entity = self.parse_jsdoc_identifier_name(has_message);
        if self.parse_optional(SyntaxKind::OpenBracketToken) {
            self.parse_expected(SyntaxKind::CloseBracketToken);
        }
        while self.parse_optional(SyntaxKind::DotToken) {
            let name = self.parse_jsdoc_identifier_name(true);
            if self.parse_optional(SyntaxKind::OpenBracketToken) {
                self.parse_expected(SyntaxKind::CloseBracketToken);
            }
            let pos = entity.pos();
            let q = self.factory.new_qualified_name(entity, name);
            entity = self.finish_node(q, pos);
        }
        entity
    }

    // Go: jsdoc.go:1339 parseJSDocIdentifierName
    // PORT: Go passes an optional diagnostic message; only its presence
    // matters here, since messages are not kept.
    fn parse_jsdoc_identifier_name(&mut self, has_message: bool) -> Node {
        if !token_is_identifier_or_keyword(self.token) {
            if has_message || is_reserved_word(self.token) {
                self.parse_error_at_current_token();
            }
            let n = self.new_identifier("");
            let pos = self.node_pos();
            return self.finish_node(n, pos);
        }
        let pos = self.sc.st.token_start;
        let end = self.sc.st.pos;
        let text = self.sc.st.value.clone();
        self.next_token_jsdoc();
        let n = self.new_identifier(&text);
        self.finish_node_with_end(n, pos, end)
    }
}

// Go: jsdoc.go:380 removeLeadingNewlines
fn remove_leading_newlines(comments: &mut Vec<String>) {
    let skip = comments
        .iter()
        .take_while(|c| c.trim_start_matches(['\r', '\n']).is_empty())
        .count();
    comments.drain(..skip);
}

// Go: jsdoc.go:392 removeTrailingWhitespace
fn remove_trailing_whitespace(comments: &mut Vec<String>) {
    while let Some(last) = comments.last() {
        let trimmed = last.trim_end_matches(is_white_space_like_char);
        if trimmed.is_empty() {
            comments.pop();
        } else {
            let trimmed = trimmed.to_string();
            *comments.last_mut().unwrap() = trimmed;
            break;
        }
    }
}

/// Go `stringutil.IsWhiteSpaceLike`.
fn is_white_space_like_char(c: char) -> bool {
    matches!(
        c,
        ' ' | '\t' | '\u{000B}' | '\u{000C}' | '\u{00A0}' | '\u{0085}' | '\u{1680}' | '\u{2000}'
            ..='\u{200B}'
                | '\u{202F}'
                | '\u{205F}'
                | '\u{3000}'
                | '\u{FEFF}'
                | '\n'
                | '\r'
                | '\u{2028}'
                | '\u{2029}'
    )
}

// Go: jsdoc.go:775 isJSDocLinkTag
fn is_jsdoc_link_tag(kind: &str) -> bool {
    kind == "link" || kind == "linkcode" || kind == "linkplain"
}

// Go: jsdoc.go:817 isObjectOrObjectArrayTypeReference
fn is_object_or_object_array_type_reference(node: Node) -> bool {
    match node.kind() {
        SyntaxKind::ObjectKeyword => true,
        SyntaxKind::ArrayType => is_object_or_object_array_type_reference(node.element_type()),
        SyntaxKind::TypeReference => {
            let name = node.type_name();
            name.kind() == SyntaxKind::Identifier
                && name.text() == "Object"
                && node.type_argument_list().is_nil()
        }
        _ => false,
    }
}

// Go: jsdoc.go:1172 textsEqual
fn texts_equal(mut a: Node, mut b: Node) -> bool {
    while a.kind() != SyntaxKind::Identifier || b.kind() != SyntaxKind::Identifier {
        if a.kind() != SyntaxKind::Identifier
            && b.kind() != SyntaxKind::Identifier
            && a.right().text() == b.right().text()
        {
            a = a.left();
            b = b.left();
        } else {
            return false;
        }
    }
    a.text() == b.text()
}

// Go: ast/ast_generated.go NewJSDocTypeLiteral
fn new_jsdoc_type_literal(tags: Option<&[Node]>, is_array_type: bool) -> Node {
    alloc_synthetic_node(
        SyntaxKind::JsDocTypeLiteral,
        D::JsDocTypeLiteral(Box::new(ts_ast::JsDocTypeLiteralData {
            is_array_type,
            js_doc_property_tags: tags.map(|t| t.iter().map(|&n| id(n)).collect()),
            symbol: None,
        })),
    )
}

// ──────────────────────────────────────────────────────────────────────
// Types (parser.go), as the JSDoc parser uses them
// ──────────────────────────────────────────────────────────────────────

/// Go `jsdocScannerInfo` bits.
const JSDOC_SCANNER_INFO_HAS_JSDOC: u8 = 1 << 0;
const JSDOC_SCANNER_INFO_HAS_DEPRECATED: u8 = 1 << 1;
const JSDOC_SCANNER_INFO_HAS_SEE_OR_LINK: u8 = 1 << 2;

fn new_jsdoc_wrapped_type(kind: SyntaxKind, t: Node) -> Node {
    let type_ = id(t);
    let data = match kind {
        SyntaxKind::JsDocNonNullableType => {
            D::JsDocNonNullableType(Box::new(ts_ast::JsDocNonNullableTypeData { type_ }))
        }
        SyntaxKind::JsDocNullableType => {
            D::JsDocNullableType(Box::new(ts_ast::JsDocNullableTypeData { type_ }))
        }
        SyntaxKind::JsDocVariadicType => {
            D::JsDocVariadicType(Box::new(ts_ast::JsDocVariadicTypeData { type_ }))
        }
        SyntaxKind::JsDocOptionalType => {
            D::JsDocOptionalType(Box::new(ts_ast::JsDocOptionalTypeData { type_ }))
        }
        _ => unreachable!("not a JSDoc wrapper type"),
    };
    alloc_synthetic_node(kind, data)
}

impl Parser {
    // Go: parser.go:416 jsdocScannerInfo
    fn jsdoc_scanner_info(&self) -> u8 {
        if !self.sc.has_flag(TokenFlags::PRECEDING_JS_DOC_COMMENT) {
            return 0;
        }
        let mut info = JSDOC_SCANNER_INFO_HAS_JSDOC;
        if self
            .sc
            .has_flag(TokenFlags::PRECEDING_JS_DOC_WITH_DEPRECATED)
        {
            info |= JSDOC_SCANNER_INFO_HAS_DEPRECATED;
        }
        if self
            .sc
            .has_flag(TokenFlags::PRECEDING_JS_DOC_WITH_SEE_OR_LINK)
        {
            info |= JSDOC_SCANNER_INFO_HAS_SEE_OR_LINK;
        }
        info
    }

    // Go: jsdoc.go:56 withJSDoc
    // PORT: only the TS path. Go returns the JSDoc list; no caller here uses it.
    fn with_jsdoc(&mut self, node: Node, info: u8) {
        if info & JSDOC_SCANNER_INFO_HAS_JSDOC == 0 {
            return;
        }
        let mut flags = node.flags() | NodeFlags::HAS_JS_DOC;
        if info & JSDOC_SCANNER_INFO_HAS_DEPRECATED != 0 {
            flags = flags | NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG;
        }
        set_node_flags(node, flags);
        if info & JSDOC_SCANNER_INFO_HAS_SEE_OR_LINK == 0 {
            return;
        }
        let text = self.sc.text;
        self.has_deprecated_tag = false;
        let mut jsdoc = Vec::new();
        let mut pos = node.pos();
        for (start, end) in get_jsdoc_comment_ranges(node, text) {
            let (parsed, infos, has_deprecated_tag) =
                parse_jsdoc_comment(text, self.ctx, start, end, pos);
            self.jsdoc_infos.extend(infos);
            self.has_deprecated_tag |= has_deprecated_tag;
            if !parsed.is_nil() {
                set_node_parent(parsed, node);
                jsdoc.push(parsed);
                pos = parsed.end();
            }
        }
        if !jsdoc.is_empty() {
            if self.has_deprecated_tag {
                self.has_deprecated_tag = false;
                set_node_flags(
                    node,
                    node.flags() | NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG,
                );
            }
            self.jsdoc_infos.push((node, jsdoc));
        }
    }

    // Go: parser.go:1710 parseTypeAnnotation
    fn parse_type_annotation(&mut self) -> Node {
        if self.parse_optional(SyntaxKind::ColonToken) {
            return self.parse_type();
        }
        Node::NIL
    }

    // Go: parser.go:1703 parseInitializer
    fn parse_initializer(&mut self) -> Node {
        if self.parse_optional(SyntaxKind::EqualsToken) {
            return self.parse_assignment_expression_or_higher();
        }
        Node::NIL
    }

    // Go: parser.go:2612 parseType
    fn parse_type(&mut self) -> Node {
        let save = self.ctx;
        self.set_context_flags(NodeFlags::TYPE_EXCLUDES_FLAGS, false);
        let type_node = if self.is_start_of_function_type_or_constructor_type() {
            self.parse_function_or_constructor_type()
        } else {
            let pos = self.node_pos();
            let mut type_node = self.parse_union_type_or_higher();
            if !self.in_disallow_conditional_types_context()
                && !self.has_preceding_line_break()
                && self.parse_optional(SyntaxKind::ExtendsKeyword)
            {
                let extends_type = self.do_in_context(
                    NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                    true,
                    Self::parse_type,
                );
                self.parse_expected(SyntaxKind::QuestionToken);
                let true_type = self.do_in_context(
                    NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                    false,
                    Self::parse_type,
                );
                self.parse_expected(SyntaxKind::ColonToken);
                let false_type = self.do_in_context(
                    NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                    false,
                    Self::parse_type,
                );
                let conditional_type = self.factory.new_conditional_type_node(
                    type_node,
                    extends_type,
                    true_type,
                    false_type,
                );
                type_node = self.finish_node(conditional_type, pos);
            }
            type_node
        };
        self.ctx = save;
        type_node
    }

    // Go: parser.go:2637 parseUnionTypeOrHigher
    fn parse_union_type_or_higher(&mut self) -> Node {
        self.parse_union_or_intersection_type(
            SyntaxKind::BarToken,
            Self::parse_intersection_type_or_higher,
        )
    }

    // Go: parser.go:2641 parseIntersectionTypeOrHigher
    fn parse_intersection_type_or_higher(&mut self) -> Node {
        self.parse_union_or_intersection_type(
            SyntaxKind::AmpersandToken,
            Self::parse_type_operator_or_higher,
        )
    }

    // Go: parser.go:2645 parseUnionOrIntersectionType
    fn parse_union_or_intersection_type(
        &mut self,
        operator: SyntaxKind,
        parse_constituent_type: fn(&mut Self) -> Node,
    ) -> Node {
        let pos = self.node_pos();
        let has_leading_operator = self.parse_optional(operator);
        let mut type_node = if has_leading_operator {
            self.parse_function_or_constructor_type_to_error(parse_constituent_type)
        } else {
            parse_constituent_type(self)
        };
        if self.token == operator || has_leading_operator {
            let mut types = vec![type_node];
            while self.parse_optional(operator) {
                types
                    .push(self.parse_function_or_constructor_type_to_error(parse_constituent_type));
            }
            let end = self.node_pos();
            let list = self.new_node_list(TextRange::new(pos, end), &types);
            type_node = if operator == SyntaxKind::BarToken {
                self.factory.new_union_type_node(list)
            } else {
                self.factory.new_intersection_type_node(list)
            };
            self.finish_node(type_node, pos);
        }
        type_node
    }

    // Go: parser.go:2678 parseTypeOperatorOrHigher
    fn parse_type_operator_or_higher(&mut self) -> Node {
        let operator = self.token;
        match operator {
            SyntaxKind::KeyOfKeyword | SyntaxKind::UniqueKeyword | SyntaxKind::ReadonlyKeyword => {
                self.parse_type_operator(operator)
            }
            SyntaxKind::InferKeyword => self.parse_infer_type(),
            _ => self.do_in_context(
                NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                false,
                Self::parse_postfix_type_or_higher,
            ),
        }
    }

    // Go: parser.go:2689 parseTypeOperator
    fn parse_type_operator(&mut self, operator: SyntaxKind) -> Node {
        let pos = self.node_pos();
        self.parse_expected(operator);
        let t = self.parse_type_operator_or_higher();
        let n = self.factory.new_type_operator_node(operator, t);
        self.finish_node(n, pos)
    }

    // Go: parser.go:2695 parseInferType
    fn parse_infer_type(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::InferKeyword);
        let tp = self.parse_type_parameter_of_infer_type();
        let n = self.factory.new_infer_type_node(tp);
        self.finish_node(n, pos)
    }

    // Go: parser.go:2701 parseTypeParameterOfInferType
    fn parse_type_parameter_of_infer_type(&mut self) -> Node {
        let pos = self.node_pos();
        let name = self.parse_identifier();
        let constraint = self.try_parse_constraint_of_infer_type();
        let n = self.factory.new_type_parameter_declaration(
            ModifierList::NIL,
            name,
            constraint,
            Node::NIL,
            Node::NIL,
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:2708 tryParseConstraintOfInferType
    fn try_parse_constraint_of_infer_type(&mut self) -> Node {
        let state = self.mark();
        if self.parse_optional(SyntaxKind::ExtendsKeyword) {
            let constraint = self.do_in_context(
                NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                true,
                Self::parse_type,
            );
            if self.in_disallow_conditional_types_context()
                || self.token != SyntaxKind::QuestionToken
            {
                return constraint;
            }
        }
        self.rewind(state);
        Node::NIL
    }

    // Go: parser.go:2720 parsePostfixTypeOrHigher
    fn parse_postfix_type_or_higher(&mut self) -> Node {
        let pos = self.node_pos();
        let mut type_node = self.parse_non_array_type();
        while !self.has_preceding_line_break() {
            match self.token {
                SyntaxKind::ExclamationToken => {
                    self.next_token();
                    let n = new_jsdoc_wrapped_type(SyntaxKind::JsDocNonNullableType, type_node);
                    type_node = self.finish_node(n, pos);
                }
                SyntaxKind::QuestionToken => {
                    if self.look_ahead(Self::next_is_start_of_type) {
                        return type_node;
                    }
                    self.next_token();
                    let n = new_jsdoc_wrapped_type(SyntaxKind::JsDocNullableType, type_node);
                    type_node = self.finish_node(n, pos);
                }
                SyntaxKind::OpenBracketToken => {
                    self.parse_expected(SyntaxKind::OpenBracketToken);
                    if self.is_start_of_type(false) {
                        let index_type = self.parse_type();
                        self.parse_expected(SyntaxKind::CloseBracketToken);
                        let n = self
                            .factory
                            .new_indexed_access_type_node(type_node, index_type);
                        type_node = self.finish_node(n, pos);
                    } else {
                        self.parse_expected(SyntaxKind::CloseBracketToken);
                        let n = self.factory.new_array_type_node(type_node);
                        type_node = self.finish_node(n, pos);
                    }
                }
                _ => return type_node,
            }
        }
        type_node
    }

    // Go: parser.go:2752 nextIsStartOfType
    fn next_is_start_of_type(&mut self) -> bool {
        self.next_token();
        self.is_start_of_type(false)
    }

    // Go: parser.go:2757 parseNonArrayType
    fn parse_non_array_type(&mut self) -> Node {
        match self.token {
            SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::ObjectKeyword => {
                let state = self.mark();
                let keyword_type_node = self.parse_keyword_type_node();
                if self.token != SyntaxKind::DotToken {
                    return keyword_type_node;
                }
                self.rewind(state);
                self.parse_type_reference()
            }
            SyntaxKind::AsteriskEqualsToken => {
                self.token = self.sc.rescan_asterisk_equals_token();
                self.parse_jsdoc_all_type()
            }
            SyntaxKind::AsteriskToken => self.parse_jsdoc_all_type(),
            SyntaxKind::QuestionQuestionToken => {
                self.token = self.sc.rescan_question_token();
                self.parse_jsdoc_nullable_type()
            }
            SyntaxKind::QuestionToken => self.parse_jsdoc_nullable_type(),
            SyntaxKind::ExclamationToken => self.parse_jsdoc_non_nullable_type(),
            SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::StringLiteral
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::NullKeyword => self.parse_literal_type_node(false),
            SyntaxKind::MinusToken => {
                if self.look_ahead(Self::next_token_is_numeric_or_big_int_literal) {
                    return self.parse_literal_type_node(true);
                }
                self.parse_type_reference()
            }
            SyntaxKind::VoidKeyword => self.parse_keyword_type_node(),
            SyntaxKind::ThisKeyword => {
                let this_keyword = self.parse_this_type_node();
                if self.token == SyntaxKind::IsKeyword && !self.has_preceding_line_break() {
                    return self.parse_this_type_predicate(this_keyword);
                }
                this_keyword
            }
            SyntaxKind::TypeOfKeyword => {
                if self.look_ahead(|p| p.next_token() == SyntaxKind::ImportKeyword) {
                    return self.parse_import_type();
                }
                self.parse_type_query()
            }
            SyntaxKind::OpenBraceToken => {
                if self.look_ahead(Self::next_is_start_of_mapped_type) {
                    return self.parse_mapped_type();
                }
                self.parse_type_literal()
            }
            SyntaxKind::OpenBracketToken => self.parse_tuple_type(),
            SyntaxKind::OpenParenToken => self.parse_parenthesized_type(),
            SyntaxKind::ImportKeyword => self.parse_import_type(),
            SyntaxKind::AssertsKeyword => {
                if self.look_ahead(Self::next_token_is_identifier_or_keyword_on_same_line) {
                    return self.parse_asserts_type_predicate();
                }
                self.parse_type_reference()
            }
            SyntaxKind::TemplateHead => self.parse_template_type(),
            _ => self.parse_type_reference(),
        }
    }

    // Go: parser.go:2827 parseKeywordTypeNode
    fn parse_keyword_type_node(&mut self) -> Node {
        let pos = self.node_pos();
        let result = self.factory.new_keyword_type_node(self.token);
        self.next_token();
        self.finish_node(result, pos)
    }

    // Go: parser.go:2834 parseThisTypeNode
    fn parse_this_type_node(&mut self) -> Node {
        let pos = self.node_pos();
        self.next_token();
        let n = self.factory.new_this_type_node();
        self.finish_node(n, pos)
    }

    // Go: parser.go:2840 parseThisTypePredicate
    fn parse_this_type_predicate(&mut self, lhs: Node) -> Node {
        self.next_token();
        let t = self.parse_type();
        let n = self.factory.new_type_predicate_node(Node::NIL, lhs, t);
        self.finish_node(n, lhs.pos())
    }

    // Go: parser.go:2845 parseJSDocAllType
    fn parse_jsdoc_all_type(&mut self) -> Node {
        let pos = self.node_pos();
        self.next_token();
        let n = alloc_synthetic_node(
            SyntaxKind::JsDocAllType,
            D::JsDocAllType(Box::new(ts_ast::JsDocAllTypeData)),
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:2851 parseJSDocNonNullableType
    fn parse_jsdoc_non_nullable_type(&mut self) -> Node {
        let pos = self.node_pos();
        self.next_token();
        let t = self.parse_type_operator_or_higher();
        let n = new_jsdoc_wrapped_type(SyntaxKind::JsDocNonNullableType, t);
        self.finish_node(n, pos)
    }

    // Go: parser.go:2857 parseJSDocNullableType
    fn parse_jsdoc_nullable_type(&mut self) -> Node {
        let pos = self.node_pos();
        self.next_token();
        let t = self.parse_type_operator_or_higher();
        let n = new_jsdoc_wrapped_type(SyntaxKind::JsDocNullableType, t);
        self.finish_node(n, pos)
    }

    // Go: parser.go:2864 parseJSDocType
    fn parse_jsdoc_type(&mut self) -> Node {
        self.sc.set_skip_jsdoc_leading_asterisks(true);
        let pos = self.node_pos();
        let has_dot_dot_dot = self.parse_optional(SyntaxKind::DotDotDotToken);
        let mut t = self.parse_type_or_type_predicate();
        self.sc.set_skip_jsdoc_leading_asterisks(false);
        if has_dot_dot_dot {
            let n = new_jsdoc_wrapped_type(SyntaxKind::JsDocVariadicType, t);
            t = self.finish_node(n, pos);
        }
        if self.token == SyntaxKind::EqualsToken {
            self.next_token();
            let n = new_jsdoc_wrapped_type(SyntaxKind::JsDocOptionalType, t);
            return self.finish_node(n, pos);
        }
        t
    }

    // Go: parser.go:2881 parseLiteralTypeNode
    fn parse_literal_type_node(&mut self, negative: bool) -> Node {
        let pos = self.node_pos();
        if negative {
            self.next_token();
        }
        let mut expression = if matches!(
            self.token,
            SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword | SyntaxKind::NullKeyword
        ) {
            self.parse_keyword_expression()
        } else {
            self.parse_literal_expression()
        };
        if negative {
            let n = self
                .factory
                .new_prefix_unary_expression(SyntaxKind::MinusToken, expression);
            expression = self.finish_node(n, pos);
        }
        let n = self.factory.new_literal_type_node(expression);
        self.finish_node(n, pos)
    }

    // Go: parser.go:5783 parseKeywordExpression
    fn parse_keyword_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let result = self.factory.new_keyword_expression(self.token);
        self.next_token();
        self.finish_node(result, pos)
    }

    // Go: parser.go:5790 parseLiteralExpression
    fn parse_literal_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let text = self.sc.st.value.clone();
        let token_flags = self.sc.st.flags;
        let result = match self.token {
            SyntaxKind::StringLiteral => self.factory.new_string_literal(text, token_flags),
            SyntaxKind::NumericLiteral => self.factory.new_numeric_literal(text, token_flags),
            SyntaxKind::BigIntLiteral => self.factory.new_big_int_literal(text, token_flags),
            SyntaxKind::RegularExpressionLiteral => self
                .factory
                .new_regular_expression_literal(text, token_flags),
            SyntaxKind::NoSubstitutionTemplateLiteral => self
                .factory
                .new_no_substitution_template_literal(text, token_flags),
            _ => panic!("Unhandled case in parseLiteralExpression"),
        };
        self.next_token();
        self.finish_node(result, pos)
    }

    // Go: parser.go:2898 parseTypeReference
    fn parse_type_reference(&mut self) -> Node {
        let pos = self.node_pos();
        let name = self.parse_entity_name(true, false);
        let args = self.parse_type_arguments_of_type_reference();
        let n = self.factory.new_type_reference_node(name, args);
        self.finish_node(n, pos)
    }

    // Go: parser.go:2907 parseEntityName
    fn parse_entity_name(&mut self, allow_reserved_words: bool, allow_private_name: bool) -> Node {
        let pos = self.node_pos();
        let mut entity = if allow_reserved_words {
            self.parse_identifier_name()
        } else {
            self.parse_identifier()
        };
        while self.parse_optional(SyntaxKind::DotToken) {
            if self.token == SyntaxKind::LessThanToken {
                break;
            }
            let right = self.parse_right_side_of_dot(allow_reserved_words, allow_private_name);
            let q = self.factory.new_qualified_name(entity, right);
            entity = self.finish_node(q, pos);
        }
        entity
    }

    // Go: parser.go:2926 parseRightSideOfDot
    // PORT: allowUnicodeEscapeSequenceInIdentifierName is always true here.
    fn parse_right_side_of_dot(
        &mut self,
        allow_identifier_names: bool,
        allow_private_identifiers: bool,
    ) -> Node {
        if self.has_preceding_line_break()
            && token_is_identifier_or_keyword(self.token)
            && self.look_ahead(Self::next_token_is_identifier_or_keyword_on_same_line)
        {
            let pos = self.node_pos();
            self.parse_error_at(pos, pos);
            return self.create_missing_identifier();
        }
        if self.token == SyntaxKind::PrivateIdentifier {
            let node = self.parse_private_identifier();
            if allow_private_identifiers {
                return node;
            }
            let pos = self.node_pos();
            self.parse_error_at(pos, pos);
            return self.create_missing_identifier();
        }
        if allow_identifier_names {
            return self.parse_identifier_name();
        }
        self.parse_identifier()
    }

    // Go: parser.go:3013 parseTypeArgumentsOfTypeReference
    fn parse_type_arguments_of_type_reference(&mut self) -> NodeList {
        if !self.has_preceding_line_break() {
            self.token = self.sc.rescan_less_than_token();
            if self.token == SyntaxKind::LessThanToken {
                return self.parse_type_arguments();
            }
        }
        NodeList::NIL
    }

    // Go: parser.go:3020 parseTypeArguments
    fn parse_type_arguments(&mut self) -> NodeList {
        if self.token == SyntaxKind::LessThanToken {
            return self.parse_bracketed_list(
                ParsingContext::TypeArguments,
                Self::parse_type,
                SyntaxKind::LessThanToken,
                SyntaxKind::GreaterThanToken,
            );
        }
        NodeList::NIL
    }

    // Go: parser.go:3117 parseTypeQuery
    fn parse_type_query(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::TypeOfKeyword);
        let entity_name = self.parse_entity_name(true, true);
        let type_arguments = if !self.has_preceding_line_break() {
            self.parse_type_arguments()
        } else {
            NodeList::NIL
        };
        let n = self
            .factory
            .new_type_query_node(entity_name, type_arguments);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3129 nextIsStartOfMappedType
    fn next_is_start_of_mapped_type(&mut self) -> bool {
        self.next_token();
        if self.token == SyntaxKind::PlusToken || self.token == SyntaxKind::MinusToken {
            return self.next_token() == SyntaxKind::ReadonlyKeyword;
        }
        if self.token == SyntaxKind::ReadonlyKeyword {
            self.next_token();
        }
        self.token == SyntaxKind::OpenBracketToken
            && self.next_token_is_identifier()
            && self.next_token() == SyntaxKind::InKeyword
    }

    // Go: parser.go nextTokenIsIdentifier
    fn next_token_is_identifier(&mut self) -> bool {
        self.next_token();
        self.is_identifier()
    }

    // Go: parser.go:3179 parseTypeMember
    fn parse_type_member(&mut self) -> Node {
        if self.token == SyntaxKind::OpenParenToken || self.token == SyntaxKind::LessThanToken {
            return self.parse_signature_member(SyntaxKind::CallSignature);
        }
        if self.token == SyntaxKind::NewKeyword
            && self.look_ahead(|p| {
                p.next_token();
                p.token == SyntaxKind::OpenParenToken || p.token == SyntaxKind::LessThanToken
            })
        {
            return self.parse_signature_member(SyntaxKind::ConstructSignature);
        }
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers_ex(false, false, false);
        if self.parse_contextual_modifier(SyntaxKind::GetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                SyntaxKind::GetAccessor,
                PARSE_FLAGS_TYPE,
            );
        }
        if self.parse_contextual_modifier(SyntaxKind::SetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                SyntaxKind::SetAccessor,
                PARSE_FLAGS_TYPE,
            );
        }
        if self.is_index_signature() {
            return self.parse_index_signature_declaration(pos, jsdoc, modifiers);
        }
        self.parse_property_or_method_signature(pos, jsdoc, modifiers)
    }

    // Go: parser.go:3206 parseSignatureMember
    fn parse_signature_member(&mut self, kind: SyntaxKind) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        if kind == SyntaxKind::ConstructSignature {
            self.parse_expected(SyntaxKind::NewKeyword);
        }
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(PARSE_FLAGS_TYPE);
        let type_node = self.parse_return_type(SyntaxKind::ColonToken, true);
        self.parse_type_member_semicolon();
        let result = if kind == SyntaxKind::CallSignature {
            self.factory
                .new_call_signature_declaration(type_parameters, parameters, type_node)
        } else {
            self.factory
                .new_construct_signature_declaration(type_parameters, parameters, type_node)
        };
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:3227 parseTypeParameters
    fn parse_type_parameters(&mut self) -> NodeList {
        if self.token == SyntaxKind::LessThanToken {
            return self.parse_bracketed_list(
                ParsingContext::TypeParameters,
                Self::parse_type_parameter,
                SyntaxKind::LessThanToken,
                SyntaxKind::GreaterThanToken,
            );
        }
        NodeList::NIL
    }

    // Go: parser.go:3234 parseTypeParameter
    fn parse_type_parameter(&mut self) -> Node {
        let pos = self.node_pos();
        let modifiers = self.parse_modifiers_ex(false, true, false);
        let name = self.parse_identifier();
        let mut constraint = Node::NIL;
        let mut expression = Node::NIL;
        if self.parse_optional(SyntaxKind::ExtendsKeyword) {
            if self.is_start_of_type(false) || !self.is_start_of_expression() {
                constraint = self.parse_type();
            } else {
                expression = self.parse_unary_expression_or_higher();
            }
        }
        let mut default_type = Node::NIL;
        if self.parse_optional(SyntaxKind::EqualsToken) {
            default_type = self.parse_type();
        }
        let result = self.factory.new_type_parameter_declaration(
            modifiers,
            name,
            constraint,
            expression,
            default_type,
        );
        self.finish_node(result, pos)
    }

    // Go: parser.go:3266 parseParameters
    fn parse_parameters(&mut self, flags: u8) -> NodeList {
        if self.parse_expected(SyntaxKind::OpenParenToken) {
            let parameters = self.parse_parameters_worker(flags, true);
            self.parse_expected(SyntaxKind::CloseParenToken);
            return parameters;
        }
        self.create_missing_list()
    }

    // Go: parser.go:3288 parseParametersWorker
    // PORT: checkJSSyntax is not ported; this parser only parses TS files.
    fn parse_parameters_worker(&mut self, flags: u8, allow_ambiguity: bool) -> NodeList {
        let in_await_context = self.in_await_context();
        let save = self.ctx;
        self.set_context_flags(NodeFlags::YIELD_CONTEXT, flags & PARSE_FLAGS_YIELD != 0);
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, flags & PARSE_FLAGS_AWAIT != 0);
        let parameters = self.parse_delimited_list(ParsingContext::Parameters, |p| {
            p.parse_parameter_ex(in_await_context, allow_ambiguity)
        });
        self.ctx = save;
        parameters
    }

    // Go: parser.go:3317 parseParameter
    fn parse_parameter(&mut self) -> Node {
        self.parse_parameter_ex(false, true)
    }

    // Go: parser.go:3321 parseParameterEx
    fn parse_parameter_ex(&mut self, in_outer_await_context: bool, allow_ambiguity: bool) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let save = self.ctx;
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, in_outer_await_context);
        let modifiers = self.parse_modifiers_ex(true, false, false);
        self.ctx = save;
        if self.token == SyntaxKind::ThisKeyword {
            let name = self.create_identifier_with_diagnostic(true, false);
            let type_annotation = self.parse_type_annotation();
            let result = self.factory.new_parameter_declaration(
                modifiers,
                Node::NIL,
                name,
                Node::NIL,
                type_annotation,
                Node::NIL,
            );
            if !modifiers.is_nil() {
                let first = modifiers.nodes().get(0).pos();
                self.parse_error_at_range(first);
            }
            self.finish_node(result, pos);
            self.with_jsdoc(result, jsdoc);
            return result;
        }
        let dot_dot_dot_token = self.parse_optional_token(SyntaxKind::DotDotDotToken);
        if !allow_ambiguity && !self.is_parameter_name_start() {
            return Node::NIL;
        }
        let name = self.parse_name_of_parameter(modifiers);
        let question_token = self.parse_optional_token(SyntaxKind::QuestionToken);
        let type_annotation = self.parse_type_annotation();
        let initializer = self.parse_initializer();
        let result = self.factory.new_parameter_declaration(
            modifiers,
            dot_dot_dot_token,
            name,
            question_token,
            type_annotation,
            initializer,
        );
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:3368 parseNameOfParameter
    fn parse_name_of_parameter(&mut self, modifiers: ModifierList) -> Node {
        let name = self.parse_identifier_or_pattern();
        if name.pos() == name.end() && modifiers.is_nil() && is_modifier_kind(self.token) {
            self.next_token();
        }
        name
    }

    // Go: parser.go:3387 parseReturnType
    fn parse_return_type(&mut self, return_token: SyntaxKind, is_type: bool) -> Node {
        if self.should_parse_return_type(return_token, is_type) {
            return self.do_in_context(
                NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                false,
                Self::parse_type_or_type_predicate,
            );
        }
        Node::NIL
    }

    // Go: parser.go:3394 shouldParseReturnType
    fn should_parse_return_type(&mut self, return_token: SyntaxKind, is_type: bool) -> bool {
        if return_token == SyntaxKind::EqualsGreaterThanToken {
            self.parse_expected(return_token);
            return true;
        } else if self.parse_optional(SyntaxKind::ColonToken) {
            return true;
        } else if is_type && self.token == SyntaxKind::EqualsGreaterThanToken {
            self.parse_error_at_current_token();
            self.next_token();
            return true;
        }
        false
    }

    // Go: parser.go:3409 parseTypeOrTypePredicate
    fn parse_type_or_type_predicate(&mut self) -> Node {
        if self.is_identifier() {
            let state = self.mark();
            let pos = self.node_pos();
            let id = self.parse_identifier();
            if self.token == SyntaxKind::IsKeyword && !self.has_preceding_line_break() {
                self.next_token();
                let t = self.parse_type();
                let n = self.factory.new_type_predicate_node(Node::NIL, id, t);
                return self.finish_node(n, pos);
            }
            self.rewind(state);
        }
        self.parse_type()
    }

    // Go: parser.go:3423 parseTypeMemberSemicolon
    fn parse_type_member_semicolon(&mut self) {
        if self.parse_optional(SyntaxKind::CommaToken) {
            return;
        }
        self.parse_semicolon();
    }

    // Go: parser.go:3453 parsePropertyName
    fn parse_property_name(&mut self) -> Node {
        if matches!(
            self.token,
            SyntaxKind::StringLiteral | SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral
        ) {
            return self.parse_literal_expression();
        }
        if self.token == SyntaxKind::OpenBracketToken {
            return self.parse_computed_property_name();
        }
        if self.token == SyntaxKind::PrivateIdentifier {
            return self.parse_private_identifier();
        }
        self.parse_identifier_name()
    }

    // Go: parser.go:3516 isIndexSignature
    fn is_index_signature(&mut self) -> bool {
        self.token == SyntaxKind::OpenBracketToken
            && self.look_ahead(Self::next_is_unambiguously_index_signature)
    }

    // Go: parser.go:3520 nextIsUnambiguouslyIndexSignature
    fn next_is_unambiguously_index_signature(&mut self) -> bool {
        self.next_token();
        if self.token == SyntaxKind::DotDotDotToken || self.token == SyntaxKind::CloseBracketToken {
            return true;
        }
        if is_modifier_kind(self.token) {
            self.next_token();
            if self.is_identifier() {
                return true;
            }
        } else if !self.is_identifier() {
            return false;
        } else {
            self.next_token();
        }
        if self.token == SyntaxKind::ColonToken || self.token == SyntaxKind::CommaToken {
            return true;
        }
        if self.token != SyntaxKind::QuestionToken {
            return false;
        }
        self.next_token();
        self.token == SyntaxKind::ColonToken
            || self.token == SyntaxKind::CommaToken
            || self.token == SyntaxKind::CloseBracketToken
    }

    // Go: parser.go:3569 parseIndexSignatureDeclaration
    fn parse_index_signature_declaration(
        &mut self,
        pos: i32,
        jsdoc: u8,
        modifiers: ModifierList,
    ) -> Node {
        let parameters = self.parse_bracketed_list(
            ParsingContext::Parameters,
            Self::parse_parameter,
            SyntaxKind::OpenBracketToken,
            SyntaxKind::CloseBracketToken,
        );
        let type_node = self.parse_type_annotation();
        self.parse_type_member_semicolon();
        let n = self
            .factory
            .new_index_signature_declaration(modifiers, parameters, type_node);
        let result = self.finish_node(n, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:3578 parsePropertyOrMethodSignature
    fn parse_property_or_method_signature(
        &mut self,
        pos: i32,
        jsdoc: u8,
        modifiers: ModifierList,
    ) -> Node {
        let name = self.parse_property_name();
        let question_token = self.parse_optional_token(SyntaxKind::QuestionToken);
        let result = if self.token == SyntaxKind::OpenParenToken
            || self.token == SyntaxKind::LessThanToken
        {
            let type_parameters = self.parse_type_parameters();
            let parameters = self.parse_parameters(PARSE_FLAGS_TYPE);
            let return_type = self.parse_return_type(SyntaxKind::ColonToken, true);
            self.factory.new_method_signature_declaration(
                modifiers,
                name,
                question_token,
                type_parameters,
                parameters,
                return_type,
            )
        } else {
            let type_node = self.parse_type_annotation();
            let initializer = if self.token == SyntaxKind::EqualsToken {
                self.parse_initializer()
            } else {
                Node::NIL
            };
            self.factory.new_property_signature_declaration(
                modifiers,
                name,
                question_token,
                type_node,
                initializer,
            )
        };
        self.parse_type_member_semicolon();
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:3605 parseTypeLiteral
    fn parse_type_literal(&mut self) -> Node {
        let pos = self.node_pos();
        let members = self.parse_object_type_members();
        let n = self.factory.new_type_literal_node(members);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3611 parseObjectTypeMembers
    fn parse_object_type_members(&mut self) -> NodeList {
        if self.parse_expected(SyntaxKind::OpenBraceToken) {
            let members = self.parse_list(ParsingContext::TypeMembers, Self::parse_type_member);
            self.parse_expected(SyntaxKind::CloseBraceToken);
            return members;
        }
        self.create_missing_list()
    }

    // Go: parser.go:3620 parseTupleType
    fn parse_tuple_type(&mut self) -> Node {
        let pos = self.node_pos();
        let elements = self.parse_bracketed_list(
            ParsingContext::TupleElementTypes,
            Self::parse_tuple_element_name_or_tuple_element_type,
            SyntaxKind::OpenBracketToken,
            SyntaxKind::CloseBracketToken,
        );
        let n = self.factory.new_tuple_type_node(elements);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3625 parseTupleElementNameOrTupleElementType
    fn parse_tuple_element_name_or_tuple_element_type(&mut self) -> Node {
        if self.look_ahead(Self::scan_start_of_named_tuple_element) {
            let pos = self.node_pos();
            let jsdoc = self.jsdoc_scanner_info();
            let dot_dot_dot_token = self.parse_optional_token(SyntaxKind::DotDotDotToken);
            let name = self.parse_identifier_name();
            let question_token = self.parse_optional_token(SyntaxKind::QuestionToken);
            self.parse_expected(SyntaxKind::ColonToken);
            let type_node = self.parse_tuple_element_type();
            let n = self.factory.new_named_tuple_member(
                dot_dot_dot_token,
                name,
                question_token,
                type_node,
            );
            let result = self.finish_node(n, pos);
            self.with_jsdoc(result, jsdoc);
            return result;
        }
        self.parse_tuple_element_type()
    }

    // Go: parser.go:3643 scanStartOfNamedTupleElement
    fn scan_start_of_named_tuple_element(&mut self) -> bool {
        if self.token == SyntaxKind::DotDotDotToken {
            return token_is_identifier_or_keyword(self.next_token())
                && self.next_token_is_colon_or_question_colon();
        }
        token_is_identifier_or_keyword(self.token) && self.next_token_is_colon_or_question_colon()
    }

    // Go: parser.go:3650 nextTokenIsColonOrQuestionColon
    fn next_token_is_colon_or_question_colon(&mut self) -> bool {
        self.next_token() == SyntaxKind::ColonToken
            || self.token == SyntaxKind::QuestionToken
                && self.next_token() == SyntaxKind::ColonToken
    }

    // Go: parser.go:3654 parseTupleElementType
    fn parse_tuple_element_type(&mut self) -> Node {
        let pos = self.node_pos();
        if self.parse_optional(SyntaxKind::DotDotDotToken) {
            let t = self.parse_type();
            let n = self.factory.new_rest_type_node(t);
            return self.finish_node(n, pos);
        }
        let type_node = self.parse_type();
        if type_node.kind() == SyntaxKind::JsDocNullableType
            && type_node.pos() == type_node.type_().pos()
        {
            let node = self.factory.new_optional_type_node(type_node.type_());
            set_node_flags(node, type_node.flags());
            set_node_loc(node, TextRange::new(type_node.pos(), type_node.end()));
            set_node_parent(type_node.type_(), node);
            return node;
        }
        type_node
    }

    // Go: parser.go:3668 parseParenthesizedType
    fn parse_parenthesized_type(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::OpenParenToken);
        let type_node = self.parse_type();
        self.parse_expected(SyntaxKind::CloseParenToken);
        let n = self.factory.new_parenthesized_type_node(type_node);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3676 parseAssertsTypePredicate
    fn parse_asserts_type_predicate(&mut self) -> Node {
        let pos = self.node_pos();
        let asserts_modifier = self.parse_expected_token(SyntaxKind::AssertsKeyword);
        let parameter_name = if self.token == SyntaxKind::ThisKeyword {
            self.parse_this_type_node()
        } else {
            self.parse_identifier()
        };
        let type_node = if self.parse_optional(SyntaxKind::IsKeyword) {
            self.parse_type()
        } else {
            Node::NIL
        };
        let n = self
            .factory
            .new_type_predicate_node(asserts_modifier, parameter_name, type_node);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3754 parseFunctionOrConstructorTypeToError
    fn parse_function_or_constructor_type_to_error(
        &mut self,
        parse_constituent_type: fn(&mut Self) -> Node,
    ) -> Node {
        if self.is_start_of_function_type_or_constructor_type() {
            let type_node = self.parse_function_or_constructor_type();
            self.parse_error_at_range(type_node.pos());
            return type_node;
        }
        parse_constituent_type(self)
    }

    // Go: parser.go:3776 isStartOfFunctionTypeOrConstructorType
    fn is_start_of_function_type_or_constructor_type(&mut self) -> bool {
        self.token == SyntaxKind::LessThanToken
            || self.token == SyntaxKind::OpenParenToken
                && self.look_ahead(Self::next_is_unambiguously_start_of_function_type)
            || self.token == SyntaxKind::NewKeyword
            || self.token == SyntaxKind::AbstractKeyword
                && self.look_ahead(|p| p.next_token() == SyntaxKind::NewKeyword)
    }

    // Go: parser.go:3783 parseFunctionOrConstructorType
    fn parse_function_or_constructor_type(&mut self) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers_for_constructor_type();
        let is_constructor_type = self.parse_optional(SyntaxKind::NewKeyword);
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(PARSE_FLAGS_TYPE);
        let return_type = self.parse_return_type(SyntaxKind::EqualsGreaterThanToken, false);
        let result = if is_constructor_type {
            self.factory.new_constructor_type_node(
                modifiers,
                type_parameters,
                parameters,
                return_type,
            )
        } else {
            self.factory
                .new_function_type_node(type_parameters, parameters, return_type)
        };
        if self.is_missing_node_list(parameters) {
            self.missing_parameter_hosts.push(result);
        }
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:3803 parseModifiersForConstructorType
    fn parse_modifiers_for_constructor_type(&mut self) -> ModifierList {
        if self.token == SyntaxKind::AbstractKeyword {
            let pos = self.node_pos();
            let modifier = self.factory.new_modifier(self.token);
            self.next_token();
            self.finish_node(modifier, pos);
            return self
                .new_modifier_list(TextRange::new(modifier.pos(), modifier.end()), &[modifier]);
        }
        ModifierList::NIL
    }

    // Go: parser.go:3818 nextIsUnambiguouslyStartOfFunctionType
    fn next_is_unambiguously_start_of_function_type(&mut self) -> bool {
        self.next_token();
        if self.token == SyntaxKind::CloseParenToken || self.token == SyntaxKind::DotDotDotToken {
            return true;
        }
        if self.skip_parameter_start() {
            if matches!(
                self.token,
                SyntaxKind::ColonToken
                    | SyntaxKind::CommaToken
                    | SyntaxKind::QuestionToken
                    | SyntaxKind::EqualsToken
            ) {
                return true;
            }
            if self.token == SyntaxKind::CloseParenToken
                && self.next_token() == SyntaxKind::EqualsGreaterThanToken
            {
                return true;
            }
        }
        false
    }

    // Go: parser.go:3843 skipParameterStart
    fn skip_parameter_start(&mut self) -> bool {
        if is_modifier_kind(self.token) {
            self.parse_modifiers_ex(false, false, false);
        }
        self.parse_optional(SyntaxKind::DotDotDotToken);
        if self.is_identifier() || self.token == SyntaxKind::ThisKeyword {
            self.next_token();
            return true;
        }
        if self.token == SyntaxKind::OpenBracketToken || self.token == SyntaxKind::OpenBraceToken {
            let previous_error_count = self.diagnostics.len();
            self.parse_identifier_or_pattern();
            return previous_error_count == self.diagnostics.len();
        }
        false
    }

    // Go: parser.go:3866 parseModifiersEx
    fn parse_modifiers_ex(
        &mut self,
        allow_decorators: bool,
        permit_const_as_modifier: bool,
        stop_on_start_of_class_static_block: bool,
    ) -> ModifierList {
        let mut has_leading_modifier = false;
        let mut has_trailing_decorator = false;
        let mut has_trailing_modifier = false;
        let mut has_static_modifier = false;
        let pos = self.node_pos();
        let mut list = Vec::new();
        loop {
            if allow_decorators && self.token == SyntaxKind::AtToken && !has_trailing_modifier {
                let decorator = self.parse_decorator();
                list.push(decorator);
                if has_leading_modifier {
                    has_trailing_decorator = true;
                }
            } else {
                let modifier = self.try_parse_modifier(
                    has_static_modifier,
                    permit_const_as_modifier,
                    stop_on_start_of_class_static_block,
                );
                if modifier.is_nil() {
                    break;
                }
                if modifier.kind() == SyntaxKind::StaticKeyword {
                    has_static_modifier = true;
                }
                list.push(modifier);
                if has_trailing_decorator {
                    has_trailing_modifier = true;
                } else {
                    has_leading_modifier = true;
                }
            }
        }
        if !list.is_empty() {
            let end = self.node_pos();
            return self.new_modifier_list(TextRange::new(pos, end), &list);
        }
        ModifierList::NIL
    }

    // Go: parser.go:3926 tryParseModifier
    fn try_parse_modifier(
        &mut self,
        has_seen_static_modifier: bool,
        permit_const_as_modifier: bool,
        stop_on_start_of_class_static_block: bool,
    ) -> Node {
        let pos = self.node_pos();
        let kind = self.token;
        if self.token == SyntaxKind::ConstKeyword && permit_const_as_modifier {
            if !self.look_ahead(Self::next_token_is_on_same_line_and_can_follow_modifier) {
                return Node::NIL;
            }
            self.next_token();
        } else if stop_on_start_of_class_static_block
            && self.token == SyntaxKind::StaticKeyword
            && self.look_ahead(|p| p.next_token() == SyntaxKind::OpenBraceToken)
        {
            return Node::NIL;
        } else if has_seen_static_modifier && self.token == SyntaxKind::StaticKeyword {
            return Node::NIL;
        } else if !self.parse_any_contextual_modifier() {
            return Node::NIL;
        }
        let n = self.factory.new_modifier(kind);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3949 parseContextualModifier
    fn parse_contextual_modifier(&mut self, t: SyntaxKind) -> bool {
        let state = self.mark();
        if self.token == t && self.next_token_can_follow_modifier() {
            return true;
        }
        self.rewind(state);
        false
    }

    // Go: parser.go:3958 parseAnyContextualModifier
    fn parse_any_contextual_modifier(&mut self) -> bool {
        let state = self.mark();
        if is_modifier_kind(self.token) && self.next_token_can_follow_modifier() {
            return true;
        }
        self.rewind(state);
        false
    }

    // Go: parser.go:3967 nextTokenCanFollowModifier
    fn next_token_can_follow_modifier(&mut self) -> bool {
        match self.token {
            SyntaxKind::ConstKeyword => self.next_token() == SyntaxKind::EnumKeyword,
            SyntaxKind::ExportKeyword => {
                self.next_token();
                if self.token == SyntaxKind::DefaultKeyword {
                    return self.look_ahead(Self::next_token_can_follow_default_keyword);
                }
                if self.token == SyntaxKind::TypeKeyword {
                    return self.look_ahead(|p| {
                        p.next_token();
                        p.can_follow_export_modifier()
                    });
                }
                self.can_follow_export_modifier()
            }
            SyntaxKind::DefaultKeyword => self.next_token_can_follow_default_keyword(),
            SyntaxKind::StaticKeyword => {
                self.next_token();
                self.can_follow_modifier()
            }
            SyntaxKind::GetKeyword | SyntaxKind::SetKeyword => {
                self.next_token();
                self.token == SyntaxKind::OpenBracketToken || self.is_literal_property_name()
            }
            _ => self.next_token_is_on_same_line_and_can_follow_modifier(),
        }
    }

    // Go: parser.go:4006 nextTokenIsIdentifierOrKeyword
    fn next_token_is_identifier_or_keyword(&mut self) -> bool {
        token_is_identifier_or_keyword(self.next_token())
    }

    // Go: parser.go:4014 nextTokenIsIdentifierOrKeywordOnSameLine
    fn next_token_is_identifier_or_keyword_on_same_line(&mut self) -> bool {
        self.next_token_is_identifier_or_keyword() && !self.has_preceding_line_break()
    }

    // Go: parser.go:4039 canFollowModifier
    fn can_follow_modifier(&self) -> bool {
        matches!(
            self.token,
            SyntaxKind::OpenBracketToken
                | SyntaxKind::OpenBraceToken
                | SyntaxKind::AsteriskToken
                | SyntaxKind::DotDotDotToken
        ) || self.is_literal_property_name()
    }

    // Go: parser.go:4047 nextTokenIsOnSameLineAndCanFollowModifier
    fn next_token_is_on_same_line_and_can_follow_modifier(&mut self) -> bool {
        self.next_token();
        if self.has_preceding_line_break() {
            return false;
        }
        self.can_follow_modifier()
    }

    // Go: parser.go:5950 scanTypeMemberStart
    fn scan_type_member_start(&mut self) -> bool {
        if matches!(
            self.token,
            SyntaxKind::OpenParenToken
                | SyntaxKind::LessThanToken
                | SyntaxKind::GetKeyword
                | SyntaxKind::SetKeyword
        ) {
            return true;
        }
        let mut id_token = false;
        while is_modifier_kind(self.token) {
            id_token = true;
            self.next_token();
        }
        if self.token == SyntaxKind::OpenBracketToken {
            return true;
        }
        if self.is_literal_property_name() {
            id_token = true;
            self.next_token();
        }
        if id_token {
            return matches!(
                self.token,
                SyntaxKind::OpenParenToken
                    | SyntaxKind::LessThanToken
                    | SyntaxKind::QuestionToken
                    | SyntaxKind::ColonToken
                    | SyntaxKind::CommaToken
            ) || self.can_parse_semicolon();
        }
        false
    }

    // Go: parser.go:5978 scanClassMemberStart
    fn scan_class_member_start(&mut self) -> bool {
        let mut id_token = SyntaxKind::Unknown;
        if self.token == SyntaxKind::AtToken {
            return true;
        }
        // Eat up all modifiers, but hold on to the last one in case it is actually an identifier.
        while is_modifier_kind(self.token) {
            id_token = self.token;
            // If the idToken is a class modifier (protected, private, public, and static), it is
            // certain that we are starting to parse class member. This allows better error recovery
            // Example:
            //      public foo() ...     // true
            //      public @dec blah ... // true; we will then report an error later
            //      export public ...    // true; we will then report an error later
            if is_class_member_modifier(id_token) {
                return true;
            }
            self.next_token();
        }
        if self.token == SyntaxKind::AsteriskToken {
            return true;
        }
        // Try to get the first property-like token following all modifiers.
        // This can either be an identifier or the 'get' or 'set' keywords.
        if self.is_literal_property_name() {
            id_token = self.token;
            self.next_token();
        }
        // Index signatures and computed properties are class members; we can parse.
        if self.token == SyntaxKind::OpenBracketToken {
            return true;
        }
        // If we were able to get any potential identifier...
        if id_token != SyntaxKind::Unknown {
            // If we have a non-keyword identifier, or if we have an accessor, then it's safe to parse.
            if !is_keyword(id_token)
                || id_token == SyntaxKind::SetKeyword
                || id_token == SyntaxKind::GetKeyword
            {
                return true;
            }
            // If it *is* a keyword, but not an accessor, check a little farther along
            // to see if it should actually be parsed as a class member.
            match self.token {
                SyntaxKind::OpenParenToken // Method declaration
                | SyntaxKind::LessThanToken // Generic Method declaration
                | SyntaxKind::ExclamationToken // Non-null assertion on property name
                | SyntaxKind::ColonToken // Type Annotation for declaration
                | SyntaxKind::EqualsToken // Initializer for declaration
                | SyntaxKind::QuestionToken => {
                    // Not valid, but permitted so that it gets caught later on.
                    return true;
                }
                _ => {}
            }
            // Covers
            //  - Semicolons     (declaration termination)
            //  - Closing braces (end-of-class, must be declaration)
            //  - End-of-files   (not valid, but permitted so that it gets caught later on)
            //  - Line-breaks    (enabling *automatic semicolon insertion*)
            return self.can_parse_semicolon();
        }
        false
    }

    // Go: parser.go:6205 isStartOfType
    fn is_start_of_type(&mut self, in_start_of_parameter: bool) -> bool {
        match self.token {
            SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::ReadonlyKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::UniqueKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::ThisKeyword
            | SyntaxKind::TypeOfKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::OpenBraceToken
            | SyntaxKind::OpenBracketToken
            | SyntaxKind::LessThanToken
            | SyntaxKind::BarToken
            | SyntaxKind::AmpersandToken
            | SyntaxKind::NewKeyword
            | SyntaxKind::StringLiteral
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::AsteriskToken
            | SyntaxKind::QuestionToken
            | SyntaxKind::ExclamationToken
            | SyntaxKind::DotDotDotToken
            | SyntaxKind::InferKeyword
            | SyntaxKind::ImportKeyword
            | SyntaxKind::AssertsKeyword
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::TemplateHead => true,
            SyntaxKind::FunctionKeyword => !in_start_of_parameter,
            SyntaxKind::MinusToken => {
                !in_start_of_parameter
                    && self.look_ahead(Self::next_token_is_numeric_or_big_int_literal)
            }
            SyntaxKind::OpenParenToken => {
                !in_start_of_parameter
                    && self.look_ahead(Self::next_is_parenthesized_or_function_type)
            }
            _ => self.is_identifier(),
        }
    }

    // Go: parser.go:6228 nextTokenIsNumericOrBigIntLiteral
    fn next_token_is_numeric_or_big_int_literal(&mut self) -> bool {
        self.next_token();
        self.token == SyntaxKind::NumericLiteral || self.token == SyntaxKind::BigIntLiteral
    }

    // Go: parser.go:6233 nextIsParenthesizedOrFunctionType
    fn next_is_parenthesized_or_function_type(&mut self) -> bool {
        self.next_token();
        self.token == SyntaxKind::CloseParenToken
            || self.is_start_of_parameter(false)
            || self.is_start_of_type(false)
    }

    // Go: parser.go:6238 isStartOfParameter
    fn is_start_of_parameter(&mut self, is_jsdoc_parameter: bool) -> bool {
        self.token == SyntaxKind::DotDotDotToken
            || self.is_binding_identifier_or_private_identifier_or_pattern()
            || is_modifier_kind(self.token)
            || self.token == SyntaxKind::AtToken
            || self.is_start_of_type(!is_jsdoc_parameter)
    }

    // Go: parser.go:6246 isBindingIdentifierOrPrivateIdentifierOrPattern
    fn is_binding_identifier_or_private_identifier_or_pattern(&self) -> bool {
        matches!(
            self.token,
            SyntaxKind::OpenBraceToken
                | SyntaxKind::OpenBracketToken
                | SyntaxKind::PrivateIdentifier
        ) || self.is_binding_identifier()
    }
}

// ──────────────────────────────────────────────────────────────────────
// Entry points
// ──────────────────────────────────────────────────────────────────────

// Go: jsdoc.go:139 parseJSDocComment
// PORT: a new parser per comment replaces Go's save and restore of the file
// parser state. `ctx` is the context the host node was parsed in.
// The result also has Go `p.jsdocInfos` from nested withJSDoc calls and Go
// `p.hasDeprecatedTag`, because the caller's parser keeps them.
fn parse_jsdoc_comment(
    source_text: &'static str,
    ctx: NodeFlags,
    start: i32,
    end: i32,
    full_start: i32,
) -> (Node, Vec<(Node, Vec<Node>)>, bool) {
    let end = if end == -1 {
        source_text.len() as i32
    } else {
        end
    };
    if !is_jsdoc_like_text(&source_text.as_bytes()[start as usize..]) {
        return (Node::NIL, Vec::new(), false);
    }
    let initial_indent = start + 4
        - source_text[..start as usize]
            .rfind('\n')
            .map_or(0, |i| i as i32 + 1);
    let mut p = Parser {
        sc: Sc::new(&source_text[..(end - 2) as usize]),
        source_text,
        factory: NodeFactory::new(),
        ctx: ctx | NodeFlags::JS_DOC,
        has_parse_error: false,
        token: SyntaxKind::Unknown,
        diagnostics: Vec::new(),
        jsdoc_infos: Vec::new(),
        has_deprecated_tag: false,
        not_parenthesized_arrow: Vec::new(),
        missing_lists: Vec::new(),
        missing_parameter_hosts: Vec::new(),
    };
    p.sc.reset_pos(start + 3);
    let comment = p.parse_jsdoc_comment_worker(start, end, full_start, initial_indent);
    (comment, p.jsdoc_infos, p.has_deprecated_tag)
}

/// Go `SourceFile.jsdocCache` for a TS file: the eager JSDoc nodes that Go
/// builds in `withJSDoc` for hosts whose JSDoc has `@see` or `@link`.
// PORT: Go builds these during the parse. Here the parsed tree is walked
// after the parse: each node with HasJSDoc is a host, and the scanner flag
// at its start says whether Go parsed its JSDoc eagerly.
#[must_use]
pub fn build_jsdoc_cache(root: Node) -> FxHashMap<Node, Vec<Node>> {
    let text = source_file_text(root);
    let mut cache = FxHashMap::default();
    let mut scanner = ts_scanner::Scanner::new(text);
    let mut visit = |host: Node, cache: &mut FxHashMap<Node, Vec<Node>>| {
        if !host.flags().intersects(NodeFlags::HAS_JS_DOC) {
            return;
        }
        scanner.reset_pos(host.pos() as usize);
        let t = scanner.scan();
        if !t
            .flags
            .contains(ts_scanner::TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK)
        {
            return;
        }
        let ctx = host.flags() & NodeFlags::CONTEXT_FLAGS;
        let mut jsdoc = Vec::new();
        let mut pos = host.pos();
        for (start, end) in get_jsdoc_comment_ranges(host, text) {
            let (parsed, infos, _) = parse_jsdoc_comment(text, ctx, start, end, pos);
            for (node, list) in infos {
                cache.insert(node, list);
            }
            if !parsed.is_nil() {
                set_node_parent(parsed, host);
                jsdoc.push(parsed);
                pos = parsed.end();
            }
        }
        if !jsdoc.is_empty() {
            cache.insert(host, jsdoc);
        }
    };
    fn walk(
        n: Node,
        cache: &mut FxHashMap<Node, Vec<Node>>,
        visit: &mut dyn FnMut(Node, &mut FxHashMap<Node, Vec<Node>>),
    ) {
        visit(n, cache);
        n.for_each_child(|c| {
            walk(c, cache, visit);
            false
        });
    }
    walk(root, &mut cache, &mut visit);
    let eof = root.end_of_file_token();
    if !eof.is_nil() {
        visit(eof, &mut cache);
    }
    cache
}

// ──────────────────────────────────────────────────────────────────────
// Expressions (parser.go). The JSDoc parser needs them only for a default
// in a bracketed @param name, e.g. `[options.name='x']`.
// ──────────────────────────────────────────────────────────────────────

impl Sc {
    // Go: scanner.go ReScanGreaterThanToken
    fn rescan_greater_than_token(&mut self) -> SyntaxKind {
        if self.st.token == SyntaxKind::GreaterThanToken {
            let b = self.text.as_bytes();
            let at = |i: i32| b.get(i as usize).copied().unwrap_or(0);
            self.st.pos = self.st.token_start + 1;
            let p = self.st.pos;
            if at(p) == b'>' {
                if at(p + 1) == b'>' {
                    if at(p + 2) == b'=' {
                        self.st.pos += 3;
                        self.st.token = SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken;
                        return self.st.token;
                    }
                    self.st.pos += 2;
                    self.st.token = SyntaxKind::GreaterThanGreaterThanGreaterThanToken;
                    return self.st.token;
                }
                if at(p + 1) == b'=' {
                    self.st.pos += 2;
                    self.st.token = SyntaxKind::GreaterThanGreaterThanEqualsToken;
                    return self.st.token;
                }
                self.st.pos += 1;
                self.st.token = SyntaxKind::GreaterThanGreaterThanToken;
                return self.st.token;
            }
            if at(p) == b'=' {
                self.st.pos += 1;
                self.st.token = SyntaxKind::GreaterThanEqualsToken;
                return self.st.token;
            }
        }
        self.st.token
    }
}

impl Parser {
    fn in_disallow_in_context(&self) -> bool {
        self.ctx.intersects(NodeFlags::DISALLOW_IN_CONTEXT)
    }

    fn in_decorator_context(&self) -> bool {
        self.ctx.intersects(NodeFlags::DECORATOR_CONTEXT)
    }

    // Go: parser.go:2998 reScanGreaterThanToken
    fn rescan_greater_than_token(&mut self) -> SyntaxKind {
        self.token = self.sc.rescan_greater_than_token();
        self.token
    }

    // Go: parser.go:4059 parseExpression
    fn parse_expression(&mut self) -> Node {
        let save = self.ctx;
        self.set_context_flags(NodeFlags::DECORATOR_CONTEXT, false);
        let pos = self.node_pos();
        let mut expr = self.parse_assignment_expression_or_higher();
        loop {
            let operator_token = self.parse_optional_token(SyntaxKind::CommaToken);
            if operator_token.is_nil() {
                break;
            }
            let right = self.parse_assignment_expression_or_higher();
            expr = self.make_binary_expression(expr, operator_token, right, pos);
        }
        self.ctx = save;
        expr
    }

    // Go: parser.go:4080 parseExpressionAllowIn
    fn parse_expression_allow_in(&mut self) -> Node {
        self.do_in_context(
            NodeFlags::DISALLOW_IN_CONTEXT,
            false,
            Self::parse_expression,
        )
    }

    // Go: parser.go:4084 parseAssignmentExpressionOrHigher
    fn parse_assignment_expression_or_higher(&mut self) -> Node {
        self.parse_assignment_expression_or_higher_worker(true)
    }

    // Go: parser.go:4088 parseAssignmentExpressionOrHigherWorker
    fn parse_assignment_expression_or_higher_worker(
        &mut self,
        allow_return_type_in_arrow_function: bool,
    ) -> Node {
        if self.is_yield_expression() {
            return self.parse_yield_expression();
        }
        let arrow_expression = self
            .try_parse_parenthesized_arrow_function_expression(allow_return_type_in_arrow_function);
        if !arrow_expression.is_nil() {
            return arrow_expression;
        }
        let arrow_expression = self
            .try_parse_async_simple_arrow_function_expression(allow_return_type_in_arrow_function);
        if !arrow_expression.is_nil() {
            return arrow_expression;
        }
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let expr = self.parse_binary_expression_or_higher(OperatorPrecedence::LOWEST);
        if expr.kind() == SyntaxKind::Identifier && self.token == SyntaxKind::EqualsGreaterThanToken
        {
            return self.parse_simple_arrow_function_expression(
                pos,
                expr,
                allow_return_type_in_arrow_function,
                jsdoc,
                ModifierList::NIL,
            );
        }
        if is_left_hand_side_expression(expr)
            && is_assignment_operator(self.rescan_greater_than_token())
        {
            let operator_token = self.parse_token_node();
            let right = self
                .parse_assignment_expression_or_higher_worker(allow_return_type_in_arrow_function);
            return self.make_binary_expression(expr, operator_token, right, pos);
        }
        self.parse_conditional_expression_rest(expr, pos, allow_return_type_in_arrow_function)
    }

    // Go: parser.go:4558 parseConditionalExpressionRest
    fn parse_conditional_expression_rest(
        &mut self,
        left_operand: Node,
        pos: i32,
        allow_return_type_in_arrow_function: bool,
    ) -> Node {
        let question_token = self.parse_optional_token(SyntaxKind::QuestionToken);
        if question_token.is_nil() {
            return left_operand;
        }
        let save = self.ctx;
        self.set_context_flags(NodeFlags::DISALLOW_IN_CONTEXT, false);
        let true_expression = self.parse_assignment_expression_or_higher_worker(false);
        self.ctx = save;
        let colon_token = self.parse_expected_token(SyntaxKind::ColonToken);
        let false_expression = if !node_is_missing(colon_token) {
            self.parse_assignment_expression_or_higher_worker(allow_return_type_in_arrow_function)
        } else {
            self.create_missing_identifier()
        };
        let n = self.factory.new_conditional_expression(
            left_operand,
            question_token,
            true_expression,
            colon_token,
            false_expression,
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:4580 parseBinaryExpressionOrHigher
    fn parse_binary_expression_or_higher(&mut self, precedence: OperatorPrecedence) -> Node {
        let pos = self.node_pos();
        let left_operand = self.parse_unary_expression_or_higher();
        self.parse_binary_expression_rest(precedence, left_operand, pos)
    }

    // Go: parser.go:4586 parseBinaryExpressionRest
    fn parse_binary_expression_rest(
        &mut self,
        precedence: OperatorPrecedence,
        mut left_operand: Node,
        pos: i32,
    ) -> Node {
        let mut last_operand = left_operand;
        loop {
            let operator = self.rescan_greater_than_token();
            let new_precedence = get_binary_operator_precedence(operator);
            if !should_consume_binary_operator(operator, new_precedence, precedence) {
                break;
            }
            if operator == SyntaxKind::InKeyword && self.in_disallow_in_context() {
                break;
            }
            if operator == SyntaxKind::AsKeyword || operator == SyntaxKind::SatisfiesKeyword {
                if self.has_preceding_line_break() {
                    break;
                }
                self.next_token();
                let last_precedence = if last_operand.kind() == SyntaxKind::BinaryExpression {
                    get_binary_operator_precedence(last_operand.operator_token().kind())
                } else {
                    OperatorPrecedence::HIGHEST
                };
                let type_node = self.parse_type();
                left_operand = if operator == SyntaxKind::SatisfiesKeyword {
                    self.make_satisfies_expression(left_operand, type_node)
                } else {
                    self.make_as_expression(left_operand, type_node)
                };
                let next_operator = self.rescan_greater_than_token();
                let next_precedence = get_binary_operator_precedence(next_operator);
                if should_consume_binary_operator(next_operator, next_precedence, last_precedence) {
                    break;
                }
                continue;
            }
            let operator_token = self.parse_token_node();
            let right = self.parse_binary_expression_or_higher(new_precedence);
            left_operand = self.make_binary_expression(left_operand, operator_token, right, pos);
            last_operand = left_operand;
        }
        left_operand
    }

    // Go: parser.go:4662 makeSatisfiesExpression
    fn make_satisfies_expression(&mut self, left: Node, right: Node) -> Node {
        let n = self.factory.new_satisfies_expression(left, right);
        self.finish_node(n, left.pos())
    }

    // Go: parser.go:4666 makeAsExpression
    fn make_as_expression(&mut self, left: Node, right: Node) -> Node {
        let n = self.factory.new_as_expression(left, right);
        self.finish_node(n, left.pos())
    }

    // Go: parser.go:4670 makeBinaryExpression
    fn make_binary_expression(
        &mut self,
        left: Node,
        operator_token: Node,
        right: Node,
        pos: i32,
    ) -> Node {
        let n = self.factory.new_binary_expression(
            ModifierList::NIL,
            left,
            Node::NIL,
            operator_token,
            right,
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:4674 parseUnaryExpressionOrHigher
    fn parse_unary_expression_or_higher(&mut self) -> Node {
        if self.is_update_expression() {
            let pos = self.node_pos();
            let update_expression = self.parse_update_expression();
            if self.token == SyntaxKind::AsteriskAsteriskToken {
                let precedence = get_binary_operator_precedence(self.token);
                return self.parse_binary_expression_rest(precedence, update_expression, pos);
            }
            return update_expression;
        }
        let simple_unary_expression = self.parse_simple_unary_expression();
        if self.token == SyntaxKind::AsteriskAsteriskToken {
            let start = skip_trivia(self.sc.text, simple_unary_expression.pos());
            let end = simple_unary_expression.end();
            self.parse_error_at(start, end);
        }
        simple_unary_expression
    }

    // Go: parser.go:4713 isUpdateExpression
    // PORT: TS files only, so `<` never starts JSX here.
    fn is_update_expression(&self) -> bool {
        !matches!(
            self.token,
            SyntaxKind::PlusToken
                | SyntaxKind::MinusToken
                | SyntaxKind::TildeToken
                | SyntaxKind::ExclamationToken
                | SyntaxKind::DeleteKeyword
                | SyntaxKind::TypeOfKeyword
                | SyntaxKind::VoidKeyword
                | SyntaxKind::AwaitKeyword
                | SyntaxKind::LessThanToken
        )
    }

    // Go: parser.go:4723 parseUpdateExpression
    fn parse_update_expression(&mut self) -> Node {
        let pos = self.node_pos();
        if self.token == SyntaxKind::PlusPlusToken || self.token == SyntaxKind::MinusMinusToken {
            let operator = self.token;
            self.next_token();
            let operand = self.parse_left_hand_side_expression_or_higher();
            let n = self.factory.new_prefix_unary_expression(operator, operand);
            return self.finish_node(n, pos);
        }
        let expression = self.parse_left_hand_side_expression_or_higher();
        if (self.token == SyntaxKind::PlusPlusToken || self.token == SyntaxKind::MinusMinusToken)
            && !self.has_preceding_line_break()
        {
            let operator = self.token;
            self.next_token();
            let n = alloc_synthetic_node(
                SyntaxKind::PostfixUnaryExpression,
                D::PostfixUnaryExpression(Box::new(ts_ast::PostfixUnaryExpressionData {
                    operand: id(expression),
                    operator,
                })),
            );
            return self.finish_node(n, pos);
        }
        expression
    }

    // Go: parser.go:5066 parseSimpleUnaryExpression
    fn parse_simple_unary_expression(&mut self) -> Node {
        let token = self.token;
        match token {
            SyntaxKind::PlusToken
            | SyntaxKind::MinusToken
            | SyntaxKind::TildeToken
            | SyntaxKind::ExclamationToken => self.parse_prefix_unary_expression(),
            SyntaxKind::DeleteKeyword | SyntaxKind::TypeOfKeyword | SyntaxKind::VoidKeyword => {
                // Go: parser.go:5103 parseDeleteExpression, 5109 parseTypeOfExpression,
                // 5115 parseVoidExpression. They differ only in the node kind.
                let kind = self.token;
                let pos = self.node_pos();
                self.next_token();
                let expression = self.parse_simple_unary_expression();
                let n = match kind {
                    SyntaxKind::DeleteKeyword => self.factory.new_delete_expression(expression),
                    SyntaxKind::TypeOfKeyword => self.factory.new_type_of_expression(expression),
                    _ => self.factory.new_void_expression(expression),
                };
                self.finish_node(n, pos)
            }
            SyntaxKind::LessThanToken => self.parse_type_assertion(),
            SyntaxKind::AwaitKeyword if self.is_await_expression() => {
                // Go: parser.go:5132 parseAwaitExpression
                let pos = self.node_pos();
                self.next_token();
                let expression = self.parse_simple_unary_expression();
                let n = self.factory.new_await_expression(expression);
                self.finish_node(n, pos)
            }
            _ => self.parse_update_expression(),
        }
    }

    // Go: parser.go:5096 parsePrefixUnaryExpression
    fn parse_prefix_unary_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let operator = self.token;
        self.next_token();
        let operand = self.parse_simple_unary_expression();
        let n = self.factory.new_prefix_unary_expression(operator, operand);
        self.finish_node(n, pos)
    }

    // Go: parser.go:5148 parseLeftHandSideExpressionOrHigher
    fn parse_left_hand_side_expression_or_higher(&mut self) -> Node {
        let pos = self.node_pos();
        let expression;
        if self.token == SyntaxKind::ImportKeyword {
            if self.look_ahead(|p| {
                p.next_token();
                p.token == SyntaxKind::OpenParenToken || p.token == SyntaxKind::LessThanToken
            }) {
                // PORT: sourceFlags is not kept.
                expression = self.parse_keyword_expression();
            } else if self.look_ahead(|p| p.next_token() == SyntaxKind::DotToken) {
                self.next_token();
                self.next_token();
                let name = self.parse_identifier_name();
                let n = new_meta_property(SyntaxKind::ImportKeyword, name);
                expression = self.finish_node(n, pos);
            } else {
                expression = self.parse_member_expression_or_higher();
            }
        } else if self.token == SyntaxKind::SuperKeyword {
            expression = self.parse_super_expression();
        } else {
            expression = self.parse_member_expression_or_higher();
        }
        self.parse_call_expression_rest(pos, expression)
    }

    // Go: parser.go:5244 isTemplateStartOfTaggedTemplate
    fn is_template_start_of_tagged_template(&self) -> bool {
        self.token == SyntaxKind::NoSubstitutionTemplateLiteral
            || self.token == SyntaxKind::TemplateHead
    }

    // Go: parser.go:5289 parseMemberExpressionOrHigher
    fn parse_member_expression_or_higher(&mut self) -> Node {
        let pos = self.node_pos();
        let expression = self.parse_primary_expression();
        self.parse_member_expression_rest(pos, expression, true)
    }

    // Go: parser.go:5342 parseMemberExpressionRest
    fn parse_member_expression_rest(
        &mut self,
        pos: i32,
        mut expression: Node,
        allow_optional_chain: bool,
    ) -> Node {
        loop {
            let mut question_dot_token = Node::NIL;
            let is_property_access;
            if allow_optional_chain && self.is_start_of_optional_property_or_element_access_chain()
            {
                question_dot_token = self.parse_expected_token(SyntaxKind::QuestionDotToken);
                is_property_access = token_is_identifier_or_keyword(self.token);
            } else {
                is_property_access = self.parse_optional(SyntaxKind::DotToken);
            }
            if is_property_access {
                expression =
                    self.parse_property_access_expression_rest(pos, expression, question_dot_token);
                continue;
            }
            if (!question_dot_token.is_nil() || !self.in_decorator_context())
                && self.parse_optional(SyntaxKind::OpenBracketToken)
            {
                expression =
                    self.parse_element_access_expression_rest(pos, expression, question_dot_token);
                continue;
            }
            if self.is_template_start_of_tagged_template() {
                if question_dot_token.is_nil()
                    && expression.kind() == SyntaxKind::ExpressionWithTypeArguments
                {
                    let original_expression = expression.expression();
                    let original_type_arguments = expression.type_argument_list();
                    expression = self.parse_tagged_template_rest(
                        pos,
                        original_expression,
                        question_dot_token,
                        original_type_arguments,
                    );
                    unparse_expression_with_type_arguments(
                        original_expression,
                        original_type_arguments,
                        expression,
                    );
                } else {
                    expression = self.parse_tagged_template_rest(
                        pos,
                        expression,
                        question_dot_token,
                        NodeList::NIL,
                    );
                }
                continue;
            }
            if question_dot_token.is_nil() {
                if self.token == SyntaxKind::ExclamationToken && !self.has_preceding_line_break() {
                    self.next_token();
                    let n = self
                        .factory
                        .new_non_null_expression(expression, NodeFlags::NONE);
                    expression = self.finish_node(n, pos);
                    continue;
                }
                let type_arguments = self.try_parse_type_arguments_in_expression();
                if !type_arguments.is_nil() {
                    let n = self
                        .factory
                        .new_expression_with_type_arguments(expression, type_arguments);
                    expression = self.finish_node(n, pos);
                    continue;
                }
            }
            return expression;
        }
    }

    // Go: parser.go:5383 isStartOfOptionalPropertyOrElementAccessChain
    fn is_start_of_optional_property_or_element_access_chain(&mut self) -> bool {
        self.token == SyntaxKind::QuestionDotToken
            && self.look_ahead(|p| {
                p.next_token();
                token_is_identifier_or_keyword(p.token)
                    || p.token == SyntaxKind::OpenBracketToken
                    || p.is_template_start_of_tagged_template()
            })
    }

    // Go: parser.go:5397 parsePropertyAccessExpressionRest
    fn parse_property_access_expression_rest(
        &mut self,
        pos: i32,
        expression: Node,
        question_dot_token: Node,
    ) -> Node {
        let name = self.parse_right_side_of_dot(true, true);
        let is_optional_chain =
            !question_dot_token.is_nil() || self.try_reparse_optional_chain(expression);
        let flags = if is_optional_chain {
            NodeFlags::OPTIONAL_CHAIN
        } else {
            NodeFlags::NONE
        };
        let property_access = self.factory.new_property_access_expression(
            expression,
            question_dot_token,
            name,
            flags,
        );
        if is_optional_chain && name.kind() == SyntaxKind::PrivateIdentifier {
            let start = skip_trivia(self.sc.text, name.pos());
            self.parse_error_at_range(start);
        }
        if expression.kind() == SyntaxKind::ExpressionWithTypeArguments {
            let type_arguments = expression.type_argument_list();
            if !type_arguments.is_nil() {
                self.parse_error_at_range(type_arguments.pos() - 1);
            }
        }
        self.finish_node(property_access, pos)
    }

    // Go: parser.go:5414 tryReparseOptionalChain
    fn try_reparse_optional_chain(&mut self, node: Node) -> bool {
        if node.flags().intersects(NodeFlags::OPTIONAL_CHAIN) {
            return true;
        }
        if node.kind() == SyntaxKind::NonNullExpression {
            let mut expr = node.expression();
            while expr.kind() == SyntaxKind::NonNullExpression
                && !expr.flags().intersects(NodeFlags::OPTIONAL_CHAIN)
            {
                expr = expr.expression();
            }
            if expr.flags().intersects(NodeFlags::OPTIONAL_CHAIN) {
                let mut node = node;
                while node.kind() == SyntaxKind::NonNullExpression {
                    set_node_flags(node, node.flags() | NodeFlags::OPTIONAL_CHAIN);
                    node = node.expression();
                }
                return true;
            }
        }
        false
    }

    // Go: parser.go:5436 parseElementAccessExpressionRest
    fn parse_element_access_expression_rest(
        &mut self,
        pos: i32,
        expression: Node,
        question_dot_token: Node,
    ) -> Node {
        let mut argument_expression = self.create_missing_identifier();
        if self.token == SyntaxKind::CloseBracketToken {
            let p = self.node_pos();
            self.parse_error_at(p, p);
        } else {
            argument_expression = self.parse_expression_allow_in();
        }
        self.parse_expected(SyntaxKind::CloseBracketToken);
        let is_optional_chain =
            !question_dot_token.is_nil() || self.try_reparse_optional_chain(expression);
        let flags = if is_optional_chain {
            NodeFlags::OPTIONAL_CHAIN
        } else {
            NodeFlags::NONE
        };
        let n = self.factory.new_element_access_expression(
            expression,
            question_dot_token,
            argument_expression,
            flags,
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:5458 parseCallExpressionRest
    fn parse_call_expression_rest(&mut self, pos: i32, mut expression: Node) -> Node {
        loop {
            expression = self.parse_member_expression_rest(pos, expression, true);
            let mut type_arguments = NodeList::NIL;
            let question_dot_token = self.parse_optional_token(SyntaxKind::QuestionDotToken);
            if !question_dot_token.is_nil() {
                type_arguments = self.try_parse_type_arguments_in_expression();
                if self.is_template_start_of_tagged_template() {
                    expression = self.parse_tagged_template_rest(
                        pos,
                        expression,
                        question_dot_token,
                        type_arguments,
                    );
                    continue;
                }
            }
            if !type_arguments.is_nil() || self.token == SyntaxKind::OpenParenToken {
                if question_dot_token.is_nil()
                    && expression.kind() == SyntaxKind::ExpressionWithTypeArguments
                {
                    type_arguments = expression.type_argument_list();
                    expression = expression.expression();
                }
                let inner = expression;
                let argument_list = self.parse_argument_list();
                let is_optional_chain =
                    !question_dot_token.is_nil() || self.try_reparse_optional_chain(expression);
                let flags = if is_optional_chain {
                    NodeFlags::OPTIONAL_CHAIN
                } else {
                    NodeFlags::NONE
                };
                let n = self.factory.new_call_expression(
                    expression,
                    question_dot_token,
                    type_arguments,
                    argument_list,
                    flags,
                );
                expression = self.finish_node(n, pos);
                unparse_expression_with_type_arguments(inner, type_arguments, expression);
                continue;
            }
            if !question_dot_token.is_nil() {
                self.parse_error_at_current_token();
                let name = self.create_missing_identifier();
                let n = self.factory.new_property_access_expression(
                    expression,
                    question_dot_token,
                    name,
                    NodeFlags::OPTIONAL_CHAIN,
                );
                expression = self.finish_node(n, pos);
            }
            break;
        }
        expression
    }

    // Go: parser.go:5494 parseArgumentList
    fn parse_argument_list(&mut self) -> NodeList {
        self.parse_expected(SyntaxKind::OpenParenToken);
        let result = self.parse_delimited_list(
            ParsingContext::ArgumentExpressions,
            Self::parse_argument_expression,
        );
        self.parse_expected(SyntaxKind::CloseParenToken);
        result
    }

    // Go: parser.go:5501 parseArgumentExpression
    fn parse_argument_expression(&mut self) -> Node {
        self.do_in_context(
            NodeFlags::DISALLOW_IN_CONTEXT | NodeFlags::DECORATOR_CONTEXT,
            false,
            Self::parse_argument_or_array_literal_element,
        )
    }

    // Go: parser.go:5505 parseArgumentOrArrayLiteralElement
    fn parse_argument_or_array_literal_element(&mut self) -> Node {
        match self.token {
            SyntaxKind::DotDotDotToken => self.parse_spread_element(),
            SyntaxKind::CommaToken => {
                let pos = self.node_pos();
                let n = alloc_synthetic_node(
                    SyntaxKind::OmittedExpression,
                    D::OmittedExpression(Box::new(ts_ast::OmittedExpressionData)),
                );
                self.finish_node(n, pos)
            }
            _ => self.parse_assignment_expression_or_higher(),
        }
    }

    // Go: parser.go:5515 parseSpreadElement
    fn parse_spread_element(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::DotDotDotToken);
        let expression = self.parse_assignment_expression_or_higher();
        let n = self.factory.new_spread_element(expression);
        self.finish_node(n, pos)
    }

    // Go: parser.go:5559 parsePrimaryExpression
    // PORT: the match is on a copy of the token, because two guards change
    // the parser.
    fn parse_primary_expression(&mut self) -> Node {
        let token = self.token;
        match token {
            SyntaxKind::NoSubstitutionTemplateLiteral => {
                if self.sc.has_flag(TokenFlags::IS_INVALID) {
                    self.token = self.sc.rescan_template_token(false);
                }
                self.parse_literal_expression()
            }
            SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral | SyntaxKind::StringLiteral => {
                self.parse_literal_expression()
            }
            SyntaxKind::ThisKeyword
            | SyntaxKind::SuperKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword => self.parse_keyword_expression(),
            SyntaxKind::OpenParenToken => self.parse_parenthesized_expression(),
            SyntaxKind::OpenBracketToken => self.parse_array_literal_expression(),
            SyntaxKind::OpenBraceToken => self.parse_object_literal_expression(),
            SyntaxKind::AsyncKeyword
                if self.look_ahead(|p| {
                    p.next_token() == SyntaxKind::FunctionKeyword && !p.has_preceding_line_break()
                }) =>
            {
                self.parse_function_expression()
            }
            SyntaxKind::AtToken => self.parse_decorated_expression(),
            SyntaxKind::ClassKeyword => self.parse_class_expression(),
            SyntaxKind::FunctionKeyword => self.parse_function_expression(),
            SyntaxKind::NewKeyword => self.parse_new_expression_or_new_dot_target(),
            SyntaxKind::SlashToken | SyntaxKind::SlashEqualsToken
                if {
                    self.token = self.sc.rescan_slash_token();
                    self.token == SyntaxKind::RegularExpressionLiteral
                } =>
            {
                self.parse_literal_expression()
            }
            SyntaxKind::TemplateHead => self.parse_template_expression(false),
            SyntaxKind::PrivateIdentifier => self.parse_private_identifier(),
            _ => self.parse_identifier(),
        }
    }

    // Go: parser.go:5604 parseParenthesizedExpression
    fn parse_parenthesized_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(SyntaxKind::OpenParenToken);
        let expression = self.parse_expression_allow_in();
        self.parse_expected(SyntaxKind::CloseParenToken);
        let n = self.factory.new_parenthesized_expression(expression);
        let result = self.finish_node(n, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:5615 parseArrayLiteralExpression
    fn parse_array_literal_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let open_bracket_parsed = self.parse_expected(SyntaxKind::OpenBracketToken);
        let multi_line = self.has_preceding_line_break();
        let elements = self.parse_delimited_list(
            ParsingContext::ArrayLiteralMembers,
            Self::parse_argument_or_array_literal_element,
        );
        self.parse_expected_matching_brackets(SyntaxKind::CloseBracketToken, open_bracket_parsed);
        let n = self
            .factory
            .new_array_literal_expression(elements, multi_line);
        self.finish_node(n, pos)
    }

    // Go: parser.go:976 parseExpectedMatchingBrackets
    // PORT: messages are not kept, so the related info is dropped.
    fn parse_expected_matching_brackets(&mut self, close_kind: SyntaxKind, _open_parsed: bool) {
        if self.token == close_kind {
            self.next_token();
            return;
        }
        self.parse_error_at_current_token();
    }

    // Go: parser.go:6169 isStartOfExpression
    fn is_start_of_expression(&mut self) -> bool {
        if self.is_start_of_left_hand_side_expression() {
            return true;
        }
        if matches!(
            self.token,
            SyntaxKind::PlusToken
                | SyntaxKind::MinusToken
                | SyntaxKind::TildeToken
                | SyntaxKind::ExclamationToken
                | SyntaxKind::DeleteKeyword
                | SyntaxKind::TypeOfKeyword
                | SyntaxKind::VoidKeyword
                | SyntaxKind::PlusPlusToken
                | SyntaxKind::MinusMinusToken
                | SyntaxKind::LessThanToken
                | SyntaxKind::AwaitKeyword
                | SyntaxKind::YieldKeyword
                | SyntaxKind::PrivateIdentifier
                | SyntaxKind::AtToken
        ) {
            return true;
        }
        if self.is_binary_operator() {
            return true;
        }
        self.is_identifier()
    }

    // Go: parser.go:6192 isStartOfLeftHandSideExpression
    fn is_start_of_left_hand_side_expression(&mut self) -> bool {
        match self.token {
            SyntaxKind::ThisKeyword
            | SyntaxKind::SuperKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::TrueKeyword
            | SyntaxKind::FalseKeyword
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::StringLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::TemplateHead
            | SyntaxKind::OpenParenToken
            | SyntaxKind::OpenBracketToken
            | SyntaxKind::OpenBraceToken
            | SyntaxKind::FunctionKeyword
            | SyntaxKind::ClassKeyword
            | SyntaxKind::NewKeyword
            | SyntaxKind::SlashToken
            | SyntaxKind::SlashEqualsToken
            | SyntaxKind::Identifier => true,
            SyntaxKind::ImportKeyword => self.look_ahead(|p| {
                p.next_token();
                matches!(
                    p.token,
                    SyntaxKind::OpenParenToken | SyntaxKind::LessThanToken | SyntaxKind::DotToken
                )
            }),
            _ => self.is_identifier(),
        }
    }

    // Go: parser.go:6296 isBinaryOperator
    fn is_binary_operator(&self) -> bool {
        if self.in_disallow_in_context() && self.token == SyntaxKind::InKeyword {
            return false;
        }
        get_binary_operator_precedence(self.token) != OperatorPrecedence::INVALID
    }
}

// ──────────────────────────────────────────────────────────────────────
// Types, binding patterns, decorators and statement starts
// ──────────────────────────────────────────────────────────────────────

impl Parser {
    // Go: parser.go:722 parseEmptyNodeList
    fn parse_empty_node_list(&mut self) -> NodeList {
        let pos = self.node_pos();
        self.new_node_list(TextRange::new(pos, pos), &[])
    }

    // Go: parser.go:3032 parseImportType
    // PORT: sourceFlags is not kept. The related info of the diagnostics is
    // dropped, because only diagnostic positions are kept.
    fn parse_import_type(&mut self) -> Node {
        let pos = self.node_pos();
        let is_type_of = self.parse_optional(SyntaxKind::TypeOfKeyword);
        self.parse_expected(SyntaxKind::ImportKeyword);
        self.parse_expected(SyntaxKind::OpenParenToken);
        let type_node = self.parse_type();
        let mut attributes = Node::NIL;
        if self.parse_optional(SyntaxKind::CommaToken) {
            self.parse_expected(SyntaxKind::OpenBraceToken);
            let current_token = self.token;
            if current_token == SyntaxKind::WithKeyword
                || current_token == SyntaxKind::AssertKeyword
            {
                if current_token == SyntaxKind::AssertKeyword {
                    self.parse_error_at_current_token();
                }
                self.next_token();
            } else {
                self.parse_error_at_current_token();
            }
            self.parse_expected(SyntaxKind::ColonToken);
            attributes = self.parse_import_attributes(current_token, true);
            self.parse_optional(SyntaxKind::CommaToken);
            self.parse_expected(SyntaxKind::CloseBraceToken);
        }
        self.parse_expected(SyntaxKind::CloseParenToken);
        let mut qualifier = Node::NIL;
        if self.parse_optional(SyntaxKind::DotToken) {
            // Go: parser.go:2903 parseEntityNameOfTypeReference
            qualifier = self.parse_entity_name(true, false);
        }
        let type_arguments = self.parse_type_arguments_of_type_reference();
        let n = self.factory.new_import_type_node(
            is_type_of,
            type_node,
            attributes,
            qualifier,
            type_arguments,
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:3074 parseImportAttribute
    fn parse_import_attribute(&mut self) -> Node {
        let pos = self.node_pos();
        let mut name = Node::NIL;
        if token_is_identifier_or_keyword(self.token) {
            name = self.parse_identifier_name();
        } else if self.token == SyntaxKind::StringLiteral {
            name = self.parse_literal_expression();
        }
        if !name.is_nil() {
            self.parse_expected(SyntaxKind::ColonToken);
        } else {
            self.parse_error_at_current_token();
        }
        let value = self.parse_assignment_expression_or_higher();
        let n = self.factory.new_import_attribute(name, value);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3091 parseImportAttributes
    // PORT: the related info of the diagnostics is dropped.
    fn parse_import_attributes(&mut self, token: SyntaxKind, skip_keyword: bool) -> Node {
        let pos = self.node_pos();
        if !skip_keyword {
            self.parse_expected(token);
        }
        let elements;
        let mut multi_line = false;
        if self.parse_expected(SyntaxKind::OpenBraceToken) {
            multi_line = self.has_preceding_line_break();
            elements = self.parse_delimited_list(
                ParsingContext::ImportAttributes,
                Self::parse_import_attribute,
            );
            self.parse_expected(SyntaxKind::CloseBraceToken);
        } else {
            elements = self.parse_empty_node_list();
        }
        let n = self
            .factory
            .new_import_attributes(token, elements, multi_line);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3140 parseMappedType
    fn parse_mapped_type(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::OpenBraceToken);
        let mut readonly_token = Node::NIL;
        if matches!(
            self.token,
            SyntaxKind::ReadonlyKeyword | SyntaxKind::PlusToken | SyntaxKind::MinusToken
        ) {
            readonly_token = self.parse_token_node();
            if readonly_token.kind() != SyntaxKind::ReadonlyKeyword {
                self.parse_expected(SyntaxKind::ReadonlyKeyword);
            }
        }
        self.parse_expected(SyntaxKind::OpenBracketToken);
        let type_parameter = self.parse_mapped_type_parameter();
        let mut name_type = Node::NIL;
        if self.parse_optional(SyntaxKind::AsKeyword) {
            name_type = self.parse_type();
        }
        self.parse_expected(SyntaxKind::CloseBracketToken);
        let mut question_token = Node::NIL;
        if matches!(
            self.token,
            SyntaxKind::QuestionToken | SyntaxKind::PlusToken | SyntaxKind::MinusToken
        ) {
            question_token = self.parse_token_node();
            if question_token.kind() != SyntaxKind::QuestionToken {
                self.parse_expected(SyntaxKind::QuestionToken);
            }
        }
        let type_node = self.parse_type_annotation();
        self.parse_semicolon();
        let members = self.parse_list(ParsingContext::TypeMembers, Self::parse_type_member);
        self.parse_expected(SyntaxKind::CloseBraceToken);
        let n = self.factory.new_mapped_type_node(
            readonly_token,
            type_parameter,
            name_type,
            question_token,
            type_node,
            members,
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:3171 parseMappedTypeParameter
    fn parse_mapped_type_parameter(&mut self) -> Node {
        let pos = self.node_pos();
        let name = self.parse_identifier_name();
        self.parse_expected(SyntaxKind::InKeyword);
        let type_node = self.parse_type();
        let n = self.factory.new_type_parameter_declaration(
            ModifierList::NIL,
            name,
            type_node,
            Node::NIL,
            Node::NIL,
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:3692 parseTemplateType
    fn parse_template_type(&mut self) -> Node {
        let pos = self.node_pos();
        let head = self.parse_template_head(false);
        let spans = self.parse_template_type_spans();
        let n = self.factory.new_template_literal_type_node(head, spans);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3697 parseTemplateHead
    fn parse_template_head(&mut self, is_tagged_template: bool) -> Node {
        if !is_tagged_template && self.sc.has_flag(TokenFlags::IS_INVALID) {
            self.token = self.sc.rescan_template_token(false);
        }
        let pos = self.node_pos();
        let raw_text = self.get_template_literal_raw_text(2);
        let result =
            self.factory
                .new_template_head(self.sc.st.value.clone(), raw_text, self.sc.st.flags);
        self.next_token();
        self.finish_node(result, pos)
    }

    // Go: parser.go:3707 getTemplateLiteralRawText
    fn get_template_literal_raw_text(&self, end_length: usize) -> String {
        let token_text = self.sc.token_text();
        let end_length = if self.sc.has_flag(TokenFlags::UNTERMINATED) {
            0
        } else {
            end_length
        };
        token_text[1..token_text.len() - end_length].to_string()
    }

    // Go: parser.go:3715 parseTemplateTypeSpans
    fn parse_template_type_spans(&mut self) -> NodeList {
        let pos = self.node_pos();
        let mut list = Vec::new();
        loop {
            let span = self.parse_template_type_span();
            list.push(span);
            let literal = with_ast_data(span, |d| match d {
                D::TemplateLiteralTypeSpan(d) => d.literal,
                _ => unreachable!(),
            });
            if resolve_synthetic_id(literal).kind() != SyntaxKind::TemplateMiddle {
                break;
            }
        }
        let end = self.node_pos();
        self.new_node_list(TextRange::new(pos, end), &list)
    }

    // Go: parser.go:3728 parseTemplateTypeSpan
    fn parse_template_type_span(&mut self) -> Node {
        let pos = self.node_pos();
        let type_node = self.parse_type();
        let literal = self.parse_literal_of_template_span(false);
        let n = self
            .factory
            .new_template_literal_type_span(type_node, literal);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3733 parseLiteralOfTemplateSpan
    fn parse_literal_of_template_span(&mut self, is_tagged_template: bool) -> Node {
        if self.token == SyntaxKind::CloseBraceToken {
            self.token = self.sc.rescan_template_token(is_tagged_template);
            return self.parse_template_middle_or_tail();
        }
        self.parse_error_at_current_token();
        let n = self.factory.new_template_tail("", "", TokenFlags::NONE);
        let pos = self.node_pos();
        self.finish_node(n, pos)
    }

    // Go: parser.go:3742 parseTemplateMiddleOrTail
    fn parse_template_middle_or_tail(&mut self) -> Node {
        let pos = self.node_pos();
        let value = self.sc.st.value.clone();
        let flags = self.sc.st.flags;
        let result = if self.token == SyntaxKind::TemplateMiddle {
            let raw_text = self.get_template_literal_raw_text(2);
            self.factory.new_template_middle(value, raw_text, flags)
        } else {
            let raw_text = self.get_template_literal_raw_text(1);
            self.factory.new_template_tail(value, raw_text, flags)
        };
        self.next_token();
        self.finish_node(result, pos)
    }

    // Go: parser.go:3433 parseAccessorDeclaration
    fn parse_accessor_declaration(
        &mut self,
        pos: i32,
        jsdoc: u8,
        modifiers: ModifierList,
        kind: SyntaxKind,
        flags: u8,
    ) -> Node {
        let name = self.parse_property_name();
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(PARSE_FLAGS_NONE);
        let return_type = self.parse_return_type(SyntaxKind::ColonToken, false);
        let body = self.parse_function_block_or_semicolon(flags);
        let result = if kind == SyntaxKind::GetAccessor {
            self.factory.new_get_accessor_declaration(
                modifiers,
                name,
                type_parameters,
                parameters,
                return_type,
                Node::NIL,
                body,
            )
        } else {
            self.factory.new_set_accessor_declaration(
                modifiers,
                name,
                type_parameters,
                parameters,
                return_type,
                Node::NIL,
                body,
            )
        };
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:3474 parseComputedPropertyName
    fn parse_computed_property_name(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::OpenBracketToken);
        let expression = self.parse_expression_allow_in();
        self.parse_expected(SyntaxKind::CloseBracketToken);
        let n = self.factory.new_computed_property_name(expression);
        self.finish_node(n, pos)
    }

    // Go: parser.go:1636 parseIdentifierOrPattern
    fn parse_identifier_or_pattern(&mut self) -> Node {
        if self.token == SyntaxKind::OpenBracketToken {
            return self.parse_array_binding_pattern();
        }
        if self.token == SyntaxKind::OpenBraceToken {
            return self.parse_object_binding_pattern();
        }
        self.parse_binding_identifier()
    }

    // Go: parser.go:1650 parseArrayBindingPattern
    fn parse_array_binding_pattern(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::OpenBracketToken);
        let save = self.ctx;
        self.set_context_flags(NodeFlags::DISALLOW_IN_CONTEXT, false);
        let elements = self.parse_delimited_list(
            ParsingContext::ArrayBindingElements,
            Self::parse_array_binding_element,
        );
        self.ctx = save;
        self.parse_expected(SyntaxKind::CloseBracketToken);
        let n = new_binding_pattern(SyntaxKind::ArrayBindingPattern, elements);
        self.finish_node(n, pos)
    }

    // Go: parser.go:1661 parseArrayBindingElement
    fn parse_array_binding_element(&mut self) -> Node {
        let pos = self.node_pos();
        let mut dot_dot_dot_token = Node::NIL;
        let mut name = Node::NIL;
        let mut initializer = Node::NIL;
        if self.token != SyntaxKind::CommaToken {
            dot_dot_dot_token = self.parse_optional_token(SyntaxKind::DotDotDotToken);
            name = self.parse_identifier_or_pattern();
            initializer = self.parse_initializer();
        }
        let n = new_binding_element(dot_dot_dot_token, Node::NIL, name, initializer);
        self.finish_node(n, pos)
    }

    // Go: parser.go:1675 parseObjectBindingPattern
    fn parse_object_binding_pattern(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::OpenBraceToken);
        let save = self.ctx;
        self.set_context_flags(NodeFlags::DISALLOW_IN_CONTEXT, false);
        let elements = self.parse_delimited_list(
            ParsingContext::ObjectBindingElements,
            Self::parse_object_binding_element,
        );
        self.ctx = save;
        self.parse_expected(SyntaxKind::CloseBraceToken);
        let n = new_binding_pattern(SyntaxKind::ObjectBindingPattern, elements);
        self.finish_node(n, pos)
    }

    // Go: parser.go:1686 parseObjectBindingElement
    fn parse_object_binding_element(&mut self) -> Node {
        let pos = self.node_pos();
        let dot_dot_dot_token = self.parse_optional_token(SyntaxKind::DotDotDotToken);
        let token_is_identifier = self.is_binding_identifier();
        let mut property_name = self.parse_property_name();
        let name;
        if token_is_identifier && self.token != SyntaxKind::ColonToken {
            name = property_name;
            property_name = Node::NIL;
        } else {
            self.parse_expected(SyntaxKind::ColonToken);
            name = self.parse_identifier_or_pattern();
        }
        let initializer = self.parse_initializer();
        let n = new_binding_element(dot_dot_dot_token, property_name, name, initializer);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3906 parseDecorator
    fn parse_decorator(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::AtToken);
        let expression = self.do_in_context(
            NodeFlags::DECORATOR_CONTEXT,
            true,
            Self::parse_decorator_expression,
        );
        let n = self.factory.new_decorator(expression);
        self.finish_node(n, pos)
    }

    // Go: parser.go:3913 parseDecoratorExpression
    fn parse_decorator_expression(&mut self) -> Node {
        if self.in_await_context() && self.token == SyntaxKind::AwaitKeyword {
            let pos = self.node_pos();
            let await_expression =
                self.create_identifier_with_diagnostic(self.is_identifier(), false);
            self.next_token();
            let member_expression = self.parse_member_expression_rest(pos, await_expression, true);
            return self.parse_call_expression_rest(pos, member_expression);
        }
        self.parse_left_hand_side_expression_or_higher()
    }

    // Go: parser.go:3994 nextTokenCanFollowDefaultKeyword
    fn next_token_can_follow_default_keyword(&mut self) -> bool {
        match self.next_token() {
            SyntaxKind::ClassKeyword
            | SyntaxKind::FunctionKeyword
            | SyntaxKind::InterfaceKeyword
            | SyntaxKind::AtToken => true,
            SyntaxKind::AbstractKeyword => self.look_ahead(|p| {
                p.next_token() == SyntaxKind::ClassKeyword && !p.has_preceding_line_break()
            }),
            SyntaxKind::AsyncKeyword => self.look_ahead(|p| {
                p.next_token() == SyntaxKind::FunctionKeyword && !p.has_preceding_line_break()
            }),
            _ => false,
        }
    }

    // Go: parser.go:4035 canFollowExportModifier
    fn can_follow_export_modifier(&self) -> bool {
        self.token == SyntaxKind::AtToken
            || self.token != SyntaxKind::AsteriskToken
                && self.token != SyntaxKind::AsKeyword
                && self.token != SyntaxKind::OpenBraceToken
                && self.can_follow_modifier()
    }

    // Go: parser.go:6062 isStartOfStatement
    fn is_start_of_statement(&mut self) -> bool {
        match self.token {
            SyntaxKind::AtToken
            | SyntaxKind::SemicolonToken
            | SyntaxKind::OpenBraceToken
            | SyntaxKind::VarKeyword
            | SyntaxKind::LetKeyword
            | SyntaxKind::UsingKeyword
            | SyntaxKind::FunctionKeyword
            | SyntaxKind::ClassKeyword
            | SyntaxKind::EnumKeyword
            | SyntaxKind::IfKeyword
            | SyntaxKind::DoKeyword
            | SyntaxKind::WhileKeyword
            | SyntaxKind::ForKeyword
            | SyntaxKind::ContinueKeyword
            | SyntaxKind::BreakKeyword
            | SyntaxKind::ReturnKeyword
            | SyntaxKind::WithKeyword
            | SyntaxKind::SwitchKeyword
            | SyntaxKind::ThrowKeyword
            | SyntaxKind::TryKeyword
            | SyntaxKind::DebuggerKeyword
            | SyntaxKind::CatchKeyword
            | SyntaxKind::FinallyKeyword => true,
            SyntaxKind::ImportKeyword => {
                self.is_start_of_declaration()
                    || self.look_ahead(|p| {
                        matches!(
                            p.next_token(),
                            SyntaxKind::OpenParenToken
                                | SyntaxKind::LessThanToken
                                | SyntaxKind::DotToken
                        )
                    })
            }
            SyntaxKind::ConstKeyword | SyntaxKind::ExportKeyword => self.is_start_of_declaration(),
            SyntaxKind::AsyncKeyword
            | SyntaxKind::DeclareKeyword
            | SyntaxKind::InterfaceKeyword
            | SyntaxKind::ModuleKeyword
            | SyntaxKind::NamespaceKeyword
            | SyntaxKind::TypeKeyword
            | SyntaxKind::GlobalKeyword
            | SyntaxKind::DeferKeyword => true,
            SyntaxKind::AccessorKeyword
            | SyntaxKind::PublicKeyword
            | SyntaxKind::PrivateKeyword
            | SyntaxKind::ProtectedKeyword
            | SyntaxKind::StaticKeyword
            | SyntaxKind::ReadonlyKeyword => {
                self.is_start_of_declaration()
                    || !self.look_ahead(Self::next_token_is_identifier_or_keyword_on_same_line)
            }
            _ => self.is_start_of_expression(),
        }
    }

    // Go: parser.go:6091 isStartOfDeclaration
    fn is_start_of_declaration(&mut self) -> bool {
        self.look_ahead(Self::scan_start_of_declaration)
    }

    // Go: parser.go:6095 scanStartOfDeclaration
    fn scan_start_of_declaration(&mut self) -> bool {
        loop {
            match self.token {
                SyntaxKind::VarKeyword
                | SyntaxKind::LetKeyword
                | SyntaxKind::ConstKeyword
                | SyntaxKind::FunctionKeyword
                | SyntaxKind::ClassKeyword
                | SyntaxKind::EnumKeyword => return true,
                SyntaxKind::UsingKeyword => {
                    return self.look_ahead(|p| {
                        p.next_token_is_binding_identifier_or_start_of_destructuring_on_same_line(
                            false,
                        )
                    });
                }
                SyntaxKind::AwaitKeyword => {
                    return self.look_ahead(|p| {
                        p.next_token() == SyntaxKind::UsingKeyword
                            && p.next_token_is_binding_identifier_or_start_of_destructuring_on_same_line(false)
                    });
                }
                SyntaxKind::InterfaceKeyword
                | SyntaxKind::TypeKeyword
                | SyntaxKind::DeferKeyword => {
                    self.next_token();
                    return self.is_identifier() && !self.has_preceding_line_break();
                }
                SyntaxKind::ModuleKeyword | SyntaxKind::NamespaceKeyword => {
                    self.next_token();
                    return (self.is_identifier() || self.token == SyntaxKind::StringLiteral)
                        && !self.has_preceding_line_break();
                }
                SyntaxKind::AbstractKeyword
                | SyntaxKind::AccessorKeyword
                | SyntaxKind::AsyncKeyword
                | SyntaxKind::DeclareKeyword
                | SyntaxKind::PrivateKeyword
                | SyntaxKind::ProtectedKeyword
                | SyntaxKind::PublicKeyword
                | SyntaxKind::ReadonlyKeyword => {
                    let previous_token = self.token;
                    self.next_token();
                    if self.has_preceding_line_break() {
                        return false;
                    }
                    if previous_token == SyntaxKind::DeclareKeyword
                        && self.token == SyntaxKind::TypeKeyword
                    {
                        return true;
                    }
                    continue;
                }
                SyntaxKind::GlobalKeyword => {
                    self.next_token();
                    return matches!(
                        self.token,
                        SyntaxKind::OpenBraceToken
                            | SyntaxKind::Identifier
                            | SyntaxKind::ExportKeyword
                    );
                }
                SyntaxKind::ImportKeyword => {
                    self.next_token();
                    return matches!(
                        self.token,
                        SyntaxKind::DeferKeyword
                            | SyntaxKind::StringLiteral
                            | SyntaxKind::AsteriskToken
                            | SyntaxKind::OpenBraceToken
                    ) || token_is_identifier_or_keyword(self.token);
                }
                SyntaxKind::ExportKeyword => {
                    self.next_token();
                    if matches!(
                        self.token,
                        SyntaxKind::EqualsToken
                            | SyntaxKind::AsteriskToken
                            | SyntaxKind::OpenBraceToken
                            | SyntaxKind::DefaultKeyword
                            | SyntaxKind::AsKeyword
                            | SyntaxKind::AtToken
                    ) {
                        return true;
                    }
                    if self.token == SyntaxKind::TypeKeyword {
                        self.next_token();
                        return self.token == SyntaxKind::AsteriskToken
                            || self.token == SyntaxKind::OpenBraceToken
                            || self.is_identifier() && !self.has_preceding_line_break();
                    }
                    continue;
                }
                SyntaxKind::StaticKeyword => {
                    self.next_token();
                    continue;
                }
                _ => return false,
            }
        }
    }

    // Go: parser.go:6349 nextTokenIsBindingIdentifierOrStartOfDestructuringOnSameLine
    fn next_token_is_binding_identifier_or_start_of_destructuring_on_same_line(
        &mut self,
        disallow_of: bool,
    ) -> bool {
        self.next_token();
        if disallow_of && self.token == SyntaxKind::OfKeyword {
            return self.look_ahead(|p| {
                p.next_token();
                matches!(
                    p.token,
                    SyntaxKind::EqualsToken | SyntaxKind::SemicolonToken | SyntaxKind::ColonToken
                )
            });
        }
        (self.is_binding_identifier() || self.token == SyntaxKind::OpenBraceToken)
            && !self.has_preceding_line_break()
    }

    // Go: parser.go:6292 isImportAttributeName
    fn is_import_attribute_name(&self) -> bool {
        token_is_identifier_or_keyword(self.token) || self.token == SyntaxKind::StringLiteral
    }

    // Go: parser.go:6303 isValidHeritageClauseObjectLiteral
    fn is_valid_heritage_clause_object_literal(&mut self) -> bool {
        self.look_ahead(|p| {
            if p.next_token() == SyntaxKind::CloseBraceToken {
                let next = p.next_token();
                return matches!(
                    next,
                    SyntaxKind::CommaToken
                        | SyntaxKind::OpenBraceToken
                        | SyntaxKind::ExtendsKeyword
                        | SyntaxKind::ImplementsKeyword
                );
            }
            true
        })
    }

    // Go: parser.go:6322 isHeritageClause
    fn is_heritage_clause(&self) -> bool {
        self.token == SyntaxKind::ExtendsKeyword || self.token == SyntaxKind::ImplementsKeyword
    }

    // Go: parser.go:6326 isHeritageClauseExtendsOrImplementsKeyword
    fn is_heritage_clause_extends_or_implements_keyword(&mut self) -> bool {
        self.is_heritage_clause()
            && self.look_ahead(|p| {
                p.next_token();
                p.is_start_of_expression()
            })
    }

    // Go: parser.go:6369 nextTokenIsTokenStringLiteral
    fn next_token_is_token_string_literal(&mut self) -> bool {
        self.next_token() == SyntaxKind::StringLiteral
    }

    // Go: parser.go:3362 isParameterNameStart
    fn is_parameter_name_start(&self) -> bool {
        self.is_binding_identifier()
            || self.token == SyntaxKind::OpenBracketToken
            || self.token == SyntaxKind::OpenBraceToken
    }
}

// ──────────────────────────────────────────────────────────────────────
// Arrow functions, yield and await, templates, object literals, function
// and class expressions, blocks and the @import tag
// ──────────────────────────────────────────────────────────────────────

impl Parser {
    // Go: parser.go:4018 nextTokenIsIdentifierOrKeywordOrLiteralOnSameLine
    fn next_token_is_identifier_or_keyword_or_literal_on_same_line(&mut self) -> bool {
        (self.next_token_is_identifier_or_keyword()
            || matches!(
                self.token,
                SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral | SyntaxKind::StringLiteral
            ))
            && !self.has_preceding_line_break()
    }

    // Go: parser.go:4157 isYieldExpression
    fn is_yield_expression(&mut self) -> bool {
        if self.token == SyntaxKind::YieldKeyword {
            if self.in_yield_context() {
                return true;
            }
            return self
                .look_ahead(Self::next_token_is_identifier_or_keyword_or_literal_on_same_line);
        }
        false
    }

    // Go: parser.go:4184 parseYieldExpression
    fn parse_yield_expression(&mut self) -> Node {
        let pos = self.node_pos();
        self.next_token();
        let result = if !self.has_preceding_line_break()
            && (self.token == SyntaxKind::AsteriskToken || self.is_start_of_expression())
        {
            let asterisk_token = self.parse_optional_token(SyntaxKind::AsteriskToken);
            let expression = self.parse_assignment_expression_or_higher();
            self.factory
                .new_yield_expression(asterisk_token, expression)
        } else {
            self.factory.new_yield_expression(Node::NIL, Node::NIL)
        };
        self.finish_node(result, pos)
    }

    // Go: parser.go:4202 isParenthesizedArrowFunctionExpression
    fn is_parenthesized_arrow_function_expression(&mut self) -> Tristate {
        if matches!(
            self.token,
            SyntaxKind::OpenParenToken | SyntaxKind::LessThanToken | SyntaxKind::AsyncKeyword
        ) {
            let state = self.mark();
            let result = self.next_is_parenthesized_arrow_function_expression();
            self.rewind(state);
            return result;
        }
        if self.token == SyntaxKind::EqualsGreaterThanToken {
            return Tristate::True;
        }
        Tristate::False
    }

    // Go: parser.go:4219 nextIsParenthesizedArrowFunctionExpression
    // PORT: TS files only, so the JSX branch for `<` is not ported.
    fn next_is_parenthesized_arrow_function_expression(&mut self) -> Tristate {
        if self.token == SyntaxKind::AsyncKeyword {
            self.next_token();
            if self.has_preceding_line_break() {
                return Tristate::False;
            }
            if self.token != SyntaxKind::OpenParenToken && self.token != SyntaxKind::LessThanToken {
                return Tristate::False;
            }
        }
        let first = self.token;
        let second = self.next_token();
        if first == SyntaxKind::OpenParenToken {
            if second == SyntaxKind::CloseParenToken {
                let third = self.next_token();
                return match third {
                    SyntaxKind::EqualsGreaterThanToken
                    | SyntaxKind::ColonToken
                    | SyntaxKind::OpenBraceToken => Tristate::True,
                    _ => Tristate::False,
                };
            }
            if second == SyntaxKind::OpenBracketToken || second == SyntaxKind::OpenBraceToken {
                return Tristate::Unknown;
            }
            if second == SyntaxKind::DotDotDotToken {
                return Tristate::True;
            }
            if is_modifier_kind(second)
                && second != SyntaxKind::AsyncKeyword
                && self.look_ahead(Self::next_token_is_identifier)
            {
                if self.next_token() == SyntaxKind::AsKeyword {
                    return Tristate::False;
                }
                return Tristate::True;
            }
            if !self.is_identifier() && second != SyntaxKind::ThisKeyword {
                return Tristate::False;
            }
            return match self.next_token() {
                SyntaxKind::ColonToken => Tristate::True,
                SyntaxKind::QuestionToken => {
                    self.next_token();
                    if matches!(
                        self.token,
                        SyntaxKind::ColonToken
                            | SyntaxKind::CommaToken
                            | SyntaxKind::EqualsToken
                            | SyntaxKind::CloseParenToken
                    ) {
                        Tristate::True
                    } else {
                        Tristate::False
                    }
                }
                SyntaxKind::CommaToken | SyntaxKind::EqualsToken | SyntaxKind::CloseParenToken => {
                    Tristate::Unknown
                }
                _ => Tristate::False,
            };
        }
        debug_assert!(first == SyntaxKind::LessThanToken);
        if !self.is_identifier() && self.token != SyntaxKind::ConstKeyword {
            return Tristate::False;
        }
        Tristate::Unknown
    }

    // Go: parser.go:4327 tryParseParenthesizedArrowFunctionExpression
    fn try_parse_parenthesized_arrow_function_expression(
        &mut self,
        allow_return_type_in_arrow_function: bool,
    ) -> Node {
        let tristate = self.is_parenthesized_arrow_function_expression();
        if tristate == Tristate::False {
            return Node::NIL;
        }
        if tristate == Tristate::True {
            return self.parse_parenthesized_arrow_function_expression(true, true);
        }
        let state = self.mark();
        let result = self.parse_possible_parenthesized_arrow_function_expression(
            allow_return_type_in_arrow_function,
        );
        if result.is_nil() {
            self.rewind(state);
        }
        result
    }

    // Go: parser.go:4348 parseParenthesizedArrowFunctionExpression
    // PORT: Go computes `unwrappedType` and never reads it; it is not ported.
    // checkJSSyntax is not ported; this parser only parses TS files.
    fn parse_parenthesized_arrow_function_expression(
        &mut self,
        allow_ambiguity: bool,
        allow_return_type_in_arrow_function: bool,
    ) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers_for_arrow_function();
        let is_async = modifier_list_has_async(modifiers);
        let signature_flags = if is_async {
            PARSE_FLAGS_AWAIT
        } else {
            PARSE_FLAGS_NONE
        };
        let type_parameters = self.parse_type_parameters();
        let parameters;
        if !self.parse_expected(SyntaxKind::OpenParenToken) {
            if !allow_ambiguity {
                return Node::NIL;
            }
            parameters = self.create_missing_list();
        } else {
            parameters = self.parse_parameters_worker(signature_flags, allow_ambiguity);
            if !allow_ambiguity && parameters.is_nil() {
                return Node::NIL;
            }
            if !self.parse_expected(SyntaxKind::CloseParenToken) && !allow_ambiguity {
                return Node::NIL;
            }
        }
        let has_return_colon = self.token == SyntaxKind::ColonToken;
        let return_type = self.parse_return_type(SyntaxKind::ColonToken, false);
        if !return_type.is_nil()
            && !allow_ambiguity
            && self.type_has_arrow_function_blocking_parse_error(return_type)
        {
            return Node::NIL;
        }
        if !allow_ambiguity
            && self.token != SyntaxKind::EqualsGreaterThanToken
            && self.token != SyntaxKind::OpenBraceToken
        {
            return Node::NIL;
        }
        let last_token = self.token;
        let equals_greater_than_token =
            self.parse_expected_token(SyntaxKind::EqualsGreaterThanToken);
        let body = if last_token == SyntaxKind::EqualsGreaterThanToken
            || last_token == SyntaxKind::OpenBraceToken
        {
            self.parse_arrow_function_expression_body(is_async, allow_return_type_in_arrow_function)
        } else {
            self.parse_identifier()
        };
        if !allow_return_type_in_arrow_function
            && has_return_colon
            && self.token != SyntaxKind::ColonToken
        {
            return Node::NIL;
        }
        let n = self.factory.new_arrow_function(
            modifiers,
            type_parameters,
            parameters,
            return_type,
            Node::NIL,
            equals_greater_than_token,
            body,
        );
        let result = self.finish_node(n, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:4446 parseModifiersForArrowFunction
    fn parse_modifiers_for_arrow_function(&mut self) -> ModifierList {
        if self.token == SyntaxKind::AsyncKeyword {
            let pos = self.node_pos();
            self.next_token();
            let n = self.factory.new_modifier(SyntaxKind::AsyncKeyword);
            let modifier = self.finish_node(n, pos);
            return self.new_modifier_list(modifier.loc(), &[modifier]);
        }
        ModifierList::NIL
    }

    // Go: parser.go:4457 typeHasArrowFunctionBlockingParseError
    // PORT: a method, because isMissingNodeList for a finished function or
    // constructor type is kept in `missing_parameter_hosts`.
    fn type_has_arrow_function_blocking_parse_error(&self, node: Node) -> bool {
        match node.kind() {
            SyntaxKind::TypeReference => node_is_missing(node.type_name()),
            SyntaxKind::FunctionType | SyntaxKind::ConstructorType => {
                self.missing_parameter_hosts.contains(&node)
                    || self.type_has_arrow_function_blocking_parse_error(node.type_())
            }
            SyntaxKind::ParenthesizedType => {
                self.type_has_arrow_function_blocking_parse_error(node.type_())
            }
            _ => false,
        }
    }

    // Go: parser.go:4469 parseArrowFunctionExpressionBody
    fn parse_arrow_function_expression_body(
        &mut self,
        is_async: bool,
        allow_return_type_in_arrow_function: bool,
    ) -> Node {
        let await_flag = if is_async {
            PARSE_FLAGS_AWAIT
        } else {
            PARSE_FLAGS_NONE
        };
        if self.token == SyntaxKind::OpenBraceToken {
            return self.parse_function_block(await_flag);
        }
        if self.token != SyntaxKind::SemicolonToken
            && self.token != SyntaxKind::FunctionKeyword
            && self.token != SyntaxKind::ClassKeyword
            && self.is_start_of_statement()
            && !self.is_start_of_expression_statement()
        {
            return self.parse_function_block(PARSE_FLAGS_IGNORE_MISSING_OPEN_BRACE | await_flag);
        }
        let save = self.ctx;
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, is_async);
        self.set_context_flags(NodeFlags::YIELD_CONTEXT, false);
        let node =
            self.parse_assignment_expression_or_higher_worker(allow_return_type_in_arrow_function);
        self.ctx = save;
        node
    }

    // Go: parser.go:4498 isStartOfExpressionStatement
    fn is_start_of_expression_statement(&mut self) -> bool {
        self.token != SyntaxKind::OpenBraceToken
            && self.token != SyntaxKind::FunctionKeyword
            && self.token != SyntaxKind::ClassKeyword
            && self.token != SyntaxKind::AtToken
            && self.is_start_of_expression()
    }

    // Go: parser.go:4503 parsePossibleParenthesizedArrowFunctionExpression
    fn parse_possible_parenthesized_arrow_function_expression(
        &mut self,
        allow_return_type_in_arrow_function: bool,
    ) -> Node {
        let token_pos = self.sc.st.token_start;
        if self.not_parenthesized_arrow.contains(&token_pos) {
            return Node::NIL;
        }
        let result = self.parse_parenthesized_arrow_function_expression(
            false,
            allow_return_type_in_arrow_function,
        );
        if result.is_nil() {
            self.not_parenthesized_arrow.push(token_pos);
        }
        result
    }

    // Go: parser.go:4515 tryParseAsyncSimpleArrowFunctionExpression
    fn try_parse_async_simple_arrow_function_expression(
        &mut self,
        allow_return_type_in_arrow_function: bool,
    ) -> Node {
        if self.token == SyntaxKind::AsyncKeyword
            && self.look_ahead(Self::next_is_un_parenthesized_async_arrow_function)
        {
            let pos = self.node_pos();
            let jsdoc = self.jsdoc_scanner_info();
            let async_modifier = self.parse_modifiers_for_arrow_function();
            let expr = self.parse_binary_expression_or_higher(OperatorPrecedence::LOWEST);
            return self.parse_simple_arrow_function_expression(
                pos,
                expr,
                allow_return_type_in_arrow_function,
                jsdoc,
                async_modifier,
            );
        }
        Node::NIL
    }

    // Go: parser.go:4527 nextIsUnParenthesizedAsyncArrowFunction
    fn next_is_un_parenthesized_async_arrow_function(&mut self) -> bool {
        if self.token == SyntaxKind::AsyncKeyword {
            self.next_token();
            if self.has_preceding_line_break() || self.token == SyntaxKind::EqualsGreaterThanToken {
                return false;
            }
            if !self.is_identifier() {
                return false;
            }
            self.next_token_without_check();
            return !self.has_preceding_line_break()
                && self.token == SyntaxKind::EqualsGreaterThanToken;
        }
        false
    }

    // Go: parser.go:4547 parseSimpleArrowFunctionExpression
    fn parse_simple_arrow_function_expression(
        &mut self,
        pos: i32,
        identifier: Node,
        allow_return_type_in_arrow_function: bool,
        jsdoc: u8,
        async_modifier: ModifierList,
    ) -> Node {
        debug_assert!(self.token == SyntaxKind::EqualsGreaterThanToken);
        let n = self.factory.new_parameter_declaration(
            ModifierList::NIL,
            Node::NIL,
            identifier,
            Node::NIL,
            Node::NIL,
            Node::NIL,
        );
        let parameter = self.finish_node(n, identifier.pos());
        let parameters = self.new_node_list(parameter.loc(), &[parameter]);
        let equals_greater_than_token =
            self.parse_expected_token(SyntaxKind::EqualsGreaterThanToken);
        let body = self.parse_arrow_function_expression_body(
            !async_modifier.is_nil(),
            allow_return_type_in_arrow_function,
        );
        let n = self.factory.new_arrow_function(
            async_modifier,
            NodeList::NIL,
            parameters,
            Node::NIL,
            Node::NIL,
            equals_greater_than_token,
            body,
        );
        let result = self.finish_node(n, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:5121 isAwaitExpression
    fn is_await_expression(&mut self) -> bool {
        if self.token == SyntaxKind::AwaitKeyword {
            if self.in_await_context() {
                return true;
            }
            return self
                .look_ahead(Self::next_token_is_identifier_or_keyword_or_literal_on_same_line);
        }
        false
    }

    // Go: parser.go:5138 parseTypeAssertion
    fn parse_type_assertion(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::LessThanToken);
        let type_node = self.parse_type();
        self.parse_expected(SyntaxKind::GreaterThanToken);
        let expression = self.parse_simple_unary_expression();
        let n = self.factory.new_type_assertion(type_node, expression);
        self.finish_node(n, pos)
    }

    // Go: parser.go:5221 parseSuperExpression
    fn parse_super_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let mut expression = self.parse_keyword_expression();
        if self.token == SyntaxKind::LessThanToken {
            let start_pos = self.node_pos();
            let type_arguments = self.try_parse_type_arguments_in_expression();
            if !type_arguments.is_nil() {
                let end = self.node_pos();
                self.parse_error_at(start_pos, end);
                if !self.is_template_start_of_tagged_template() {
                    let n = self
                        .factory
                        .new_expression_with_type_arguments(expression, type_arguments);
                    expression = self.finish_node(n, pos);
                }
            }
        }
        if matches!(
            self.token,
            SyntaxKind::OpenParenToken | SyntaxKind::DotToken | SyntaxKind::OpenBracketToken
        ) {
            return expression;
        }
        self.parse_error_at_current_token();
        let name = self.parse_right_side_of_dot(true, true);
        let n = self.factory.new_property_access_expression(
            expression,
            Node::NIL,
            name,
            NodeFlags::NONE,
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:5247 tryParseTypeArgumentsInExpression
    fn try_parse_type_arguments_in_expression(&mut self) -> NodeList {
        if self.ctx.intersects(NodeFlags::JAVA_SCRIPT_FILE)
            || (self.token != SyntaxKind::LessThanToken
                && self.token != SyntaxKind::LessThanLessThanToken)
        {
            return NodeList::NIL;
        }
        let state = self.mark();
        self.token = self.sc.rescan_less_than_token();
        if self.token == SyntaxKind::LessThanToken {
            self.next_token();
            let type_arguments =
                self.parse_delimited_list(ParsingContext::TypeArguments, Self::parse_type);
            if self.rescan_greater_than_token() == SyntaxKind::GreaterThanToken {
                self.next_token();
                if self.can_follow_type_arguments_in_expression() {
                    return type_arguments;
                }
            }
        }
        self.rewind(state);
        NodeList::NIL
    }

    // Go: parser.go:5270 canFollowTypeArgumentsInExpression
    fn can_follow_type_arguments_in_expression(&mut self) -> bool {
        match self.token {
            SyntaxKind::OpenParenToken
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::TemplateHead => true,
            SyntaxKind::LessThanToken
            | SyntaxKind::GreaterThanToken
            | SyntaxKind::PlusToken
            | SyntaxKind::MinusToken => false,
            _ => {
                self.has_preceding_line_break()
                    || self.is_binary_operator()
                    || !self.is_start_of_expression()
            }
        }
    }

    // Go: parser.go:5522 parseTaggedTemplateRest
    // PORT: checkJSSyntax is not ported; this parser only parses TS files.
    fn parse_tagged_template_rest(
        &mut self,
        pos: i32,
        tag: Node,
        question_dot_token: Node,
        type_arguments: NodeList,
    ) -> Node {
        let template = if self.token == SyntaxKind::NoSubstitutionTemplateLiteral {
            self.token = self.sc.rescan_template_token(true);
            self.parse_literal_expression()
        } else {
            self.parse_template_expression(true)
        };
        let is_optional_chain =
            !question_dot_token.is_nil() || tag.flags().intersects(NodeFlags::OPTIONAL_CHAIN);
        let flags = if is_optional_chain {
            NodeFlags::OPTIONAL_CHAIN
        } else {
            NodeFlags::NONE
        };
        let n = self.factory.new_tagged_template_expression(
            tag,
            question_dot_token,
            type_arguments,
            template,
            flags,
        );
        self.finish_node(n, pos)
    }

    // Go: parser.go:5534 parseTemplateExpression
    fn parse_template_expression(&mut self, is_tagged_template: bool) -> Node {
        let pos = self.node_pos();
        let head = self.parse_template_head(is_tagged_template);
        let spans = self.parse_template_spans(is_tagged_template);
        let n = new_template_expression(head, spans);
        self.finish_node(n, pos)
    }

    // Go: parser.go:5539 parseTemplateSpans
    fn parse_template_spans(&mut self, is_tagged_template: bool) -> NodeList {
        let pos = self.node_pos();
        let mut list = Vec::new();
        loop {
            let span = self.parse_template_span(is_tagged_template);
            list.push(span);
            let literal = with_ast_data(span, |d| match d {
                D::TemplateSpan(d) => d.literal,
                _ => unreachable!(),
            });
            if resolve_synthetic_id(literal).kind() != SyntaxKind::TemplateMiddle {
                break;
            }
        }
        let end = self.node_pos();
        self.new_node_list(TextRange::new(pos, end), &list)
    }

    // Go: parser.go:5552 parseTemplateSpan
    fn parse_template_span(&mut self, is_tagged_template: bool) -> Node {
        let pos = self.node_pos();
        let expression = self.parse_expression_allow_in();
        let literal = self.parse_literal_of_template_span(is_tagged_template);
        let n = new_template_span(expression, literal);
        self.finish_node(n, pos)
    }

    // Go: parser.go:5625 parseObjectLiteralExpression
    fn parse_object_literal_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let open_brace_parsed = self.parse_expected(SyntaxKind::OpenBraceToken);
        let multi_line = self.has_preceding_line_break();
        let properties = self.parse_delimited_list(
            ParsingContext::ObjectLiteralMembers,
            Self::parse_object_literal_element,
        );
        self.parse_expected_matching_brackets(SyntaxKind::CloseBraceToken, open_brace_parsed);
        let n = self
            .factory
            .new_object_literal_expression(properties, multi_line);
        self.finish_node(n, pos)
    }

    // Go: parser.go:5635 parseObjectLiteralElement
    fn parse_object_literal_element(&mut self) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        if self.parse_optional(SyntaxKind::DotDotDotToken) {
            let expression = self.parse_assignment_expression_or_higher();
            let n = new_spread_assignment(expression);
            let result = self.finish_node(n, pos);
            self.with_jsdoc(result, jsdoc);
            return result;
        }
        let modifiers = self.parse_modifiers_ex(true, false, false);
        if self.parse_contextual_modifier(SyntaxKind::GetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                SyntaxKind::GetAccessor,
                PARSE_FLAGS_NONE,
            );
        }
        if self.parse_contextual_modifier(SyntaxKind::SetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                SyntaxKind::SetAccessor,
                PARSE_FLAGS_NONE,
            );
        }
        let asterisk_token = self.parse_optional_token(SyntaxKind::AsteriskToken);
        let token_is_identifier = self.is_identifier();
        let name = self.parse_property_name();
        let mut postfix_token = self.parse_optional_token(SyntaxKind::QuestionToken);
        if postfix_token.is_nil() {
            postfix_token = self.parse_optional_token(SyntaxKind::ExclamationToken);
        }
        if !asterisk_token.is_nil()
            || self.token == SyntaxKind::OpenParenToken
            || self.token == SyntaxKind::LessThanToken
        {
            return self.parse_method_declaration(
                pos,
                jsdoc,
                modifiers,
                asterisk_token,
                name,
                postfix_token,
            );
        }
        let node;
        let is_shorthand_property_assignment =
            token_is_identifier && self.token != SyntaxKind::ColonToken;
        if is_shorthand_property_assignment {
            let equals_token = self.parse_optional_token(SyntaxKind::EqualsToken);
            let mut initializer = Node::NIL;
            if !equals_token.is_nil() {
                initializer = self.do_in_context(
                    NodeFlags::DISALLOW_IN_CONTEXT,
                    false,
                    Self::parse_assignment_expression_or_higher,
                );
            }
            node = new_shorthand_property_assignment(
                modifiers,
                name,
                postfix_token,
                Node::NIL,
                equals_token,
                initializer,
            );
        } else {
            self.parse_expected(SyntaxKind::ColonToken);
            let initializer = self.do_in_context(
                NodeFlags::DISALLOW_IN_CONTEXT,
                false,
                Self::parse_assignment_expression_or_higher,
            );
            node = self.factory.new_property_assignment(
                modifiers,
                name,
                postfix_token,
                Node::NIL,
                initializer,
            );
        }
        self.finish_node(node, pos);
        self.with_jsdoc(node, jsdoc);
        node
    }

    // Go: parser.go:1955 parseMethodDeclaration
    // PORT: the diagnostic message argument is not kept. checkJSSyntax is
    // not ported; this parser only parses TS files.
    fn parse_method_declaration(
        &mut self,
        pos: i32,
        jsdoc: u8,
        modifiers: ModifierList,
        asterisk_token: Node,
        name: Node,
        question_token: Node,
    ) -> Node {
        let signature_flags = (if !asterisk_token.is_nil() {
            PARSE_FLAGS_YIELD
        } else {
            PARSE_FLAGS_NONE
        }) | (if modifier_list_has_async(modifiers) {
            PARSE_FLAGS_AWAIT
        } else {
            PARSE_FLAGS_NONE
        });
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(signature_flags);
        let type_node = self.parse_return_type(SyntaxKind::ColonToken, false);
        let body = self.parse_function_block_or_semicolon(signature_flags);
        let n = self.factory.new_method_declaration(
            modifiers,
            asterisk_token,
            name,
            question_token,
            type_parameters,
            parameters,
            type_node,
            Node::NIL,
            body,
        );
        let result = self.finish_node(n, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:5687 parseFunctionExpression
    // PORT: checkJSSyntax is not ported; this parser only parses TS files.
    fn parse_function_expression(&mut self) -> Node {
        let save = self.ctx;
        self.set_context_flags(NodeFlags::DECORATOR_CONTEXT, false);
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers();
        self.parse_expected(SyntaxKind::FunctionKeyword);
        let asterisk_token = self.parse_optional_token(SyntaxKind::AsteriskToken);
        let is_generator = !asterisk_token.is_nil();
        let is_async = modifier_list_has_async(modifiers);
        let signature_flags = (if is_generator {
            PARSE_FLAGS_YIELD
        } else {
            PARSE_FLAGS_NONE
        }) | (if is_async {
            PARSE_FLAGS_AWAIT
        } else {
            PARSE_FLAGS_NONE
        });
        let name = match (is_generator, is_async) {
            (true, true) => self.do_in_context(
                NodeFlags::YIELD_CONTEXT | NodeFlags::AWAIT_CONTEXT,
                true,
                Self::parse_optional_binding_identifier,
            ),
            (true, false) => self.do_in_context(
                NodeFlags::YIELD_CONTEXT,
                true,
                Self::parse_optional_binding_identifier,
            ),
            (false, true) => self.do_in_context(
                NodeFlags::AWAIT_CONTEXT,
                true,
                Self::parse_optional_binding_identifier,
            ),
            (false, false) => self.parse_optional_binding_identifier(),
        };
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(signature_flags);
        let return_type = self.parse_return_type(SyntaxKind::ColonToken, false);
        let body = self.parse_function_block(signature_flags);
        self.ctx = save;
        let result = self.factory.new_function_expression(
            modifiers,
            asterisk_token,
            name,
            type_parameters,
            parameters,
            return_type,
            Node::NIL,
            body,
        );
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:5726 parseOptionalBindingIdentifier
    fn parse_optional_binding_identifier(&mut self) -> Node {
        if self.is_binding_identifier() {
            return self.parse_binding_identifier();
        }
        Node::NIL
    }

    // Go: parser.go:5733 parseDecoratedExpression
    fn parse_decorated_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers_ex(true, false, false);
        if self.token == SyntaxKind::ClassKeyword {
            return self.parse_class_declaration_or_expression(
                pos,
                jsdoc,
                modifiers,
                SyntaxKind::ClassExpression,
            );
        }
        let p = self.node_pos();
        self.parse_error_at(p, p);
        let n = new_missing_declaration(modifiers);
        self.finish_node(n, pos)
    }

    // Go: parser.go:5756 parseNewExpressionOrNewDotTarget
    // PORT: checkJSSyntax is not ported; this parser only parses TS files.
    fn parse_new_expression_or_new_dot_target(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::NewKeyword);
        if self.parse_optional(SyntaxKind::DotToken) {
            let name = self.parse_identifier_name();
            let n = new_meta_property(SyntaxKind::NewKeyword, name);
            return self.finish_node(n, pos);
        }
        let expression_pos = self.node_pos();
        let primary = self.parse_primary_expression();
        let mut expression = self.parse_member_expression_rest(expression_pos, primary, false);
        let mut type_arguments = NodeList::NIL;
        if expression.kind() == SyntaxKind::ExpressionWithTypeArguments {
            type_arguments = expression.type_argument_list();
            expression = expression.expression();
        }
        if self.token == SyntaxKind::QuestionDotToken {
            self.parse_error_at_current_token();
        }
        let mut argument_list = NodeList::NIL;
        if self.token == SyntaxKind::OpenParenToken {
            argument_list = self.parse_argument_list();
        }
        let n = self
            .factory
            .new_new_expression(expression, type_arguments, argument_list);
        let result = self.finish_node(n, pos);
        unparse_expression_with_type_arguments(expression, type_arguments, result);
        result
    }

    // Go: parser.go:1745 parseClassExpression
    fn parse_class_expression(&mut self) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_class_declaration_or_expression(
            pos,
            jsdoc,
            ModifierList::NIL,
            SyntaxKind::ClassExpression,
        )
    }

    // Go: parser.go:1749 parseClassDeclarationOrExpression
    // PORT: statementHasAwaitIdentifier and checkJSSyntax are not ported;
    // this parser only parses TS files.
    fn parse_class_declaration_or_expression(
        &mut self,
        pos: i32,
        jsdoc: u8,
        modifiers: ModifierList,
        kind: SyntaxKind,
    ) -> Node {
        let save = self.ctx;
        self.parse_expected(SyntaxKind::ClassKeyword);
        let name = self.parse_name_of_class_declaration_or_expression();
        let type_parameters = self.parse_type_parameters();
        // PORT: Go also checks `p.parsingContexts` here (tsgo#4823: a
        // `SourceElements` parse outside `BlockStatements` and
        // `SwitchClauseStatements`). This parser does not track parsing
        // contexts, and it reaches a class only as a decorated class
        // expression inside a JSDoc comment, so it keeps the modifier check.
        if !modifiers.is_nil()
            && modifiers
                .nodes()
                .iter()
                .any(|m| m.kind() == SyntaxKind::ExportKeyword)
        {
            self.set_context_flags(NodeFlags::AWAIT_CONTEXT, true);
        }
        let heritage_clauses = self.parse_heritage_clauses();
        let members = if self.parse_expected(SyntaxKind::OpenBraceToken) {
            let members = self.parse_list(ParsingContext::ClassMembers, Self::parse_class_element);
            self.parse_expected(SyntaxKind::CloseBraceToken);
            members
        } else {
            self.create_missing_list()
        };
        self.ctx = save;
        let result = if kind == SyntaxKind::ClassDeclaration {
            self.factory.new_class_declaration(
                modifiers,
                name,
                type_parameters,
                heritage_clauses,
                members,
            )
        } else {
            self.factory.new_class_expression(
                modifiers,
                name,
                type_parameters,
                heritage_clauses,
                members,
            )
        };
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:1796 parseNameOfClassDeclarationOrExpression
    fn parse_name_of_class_declaration_or_expression(&mut self) -> Node {
        if self.is_binding_identifier() && !self.is_implements_clause() {
            let is_binding_identifier = self.is_binding_identifier();
            return self.create_identifier_with_diagnostic(is_binding_identifier, false);
        }
        Node::NIL
    }

    // Go: parser.go:1811 isImplementsClause
    fn is_implements_clause(&mut self) -> bool {
        self.token == SyntaxKind::ImplementsKeyword
            && self.look_ahead(Self::next_token_is_identifier_or_keyword)
    }

    // Go: parser.go:1823 parseHeritageClauses
    fn parse_heritage_clauses(&mut self) -> NodeList {
        if self.is_heritage_clause() {
            return self.parse_list(ParsingContext::HeritageClauses, Self::parse_heritage_clause);
        }
        NodeList::NIL
    }

    // Go: parser.go:1832 parseHeritageClause
    // PORT: checkJSSyntax is not ported; this parser only parses TS files.
    fn parse_heritage_clause(&mut self) -> Node {
        let pos = self.node_pos();
        let kind = self.token;
        self.next_token();
        let types = self.parse_delimited_list(
            ParsingContext::HeritageClauseElement,
            Self::parse_expression_with_type_arguments,
        );
        let n = self.factory.new_heritage_clause(kind, types);
        self.finish_node(n, pos)
    }

    // Go: parser.go:1840 parseExpressionWithTypeArguments
    fn parse_expression_with_type_arguments(&mut self) -> Node {
        let pos = self.node_pos();
        let expression = self.parse_left_hand_side_expression_or_higher();
        if expression.kind() == SyntaxKind::ExpressionWithTypeArguments {
            return expression;
        }
        let type_arguments = self.parse_type_arguments();
        let n = self
            .factory
            .new_expression_with_type_arguments(expression, type_arguments);
        self.finish_node(n, pos)
    }

    // Go: parser.go:1850 parseClassElement
    // PORT: the diagnostic message is not kept. checkJSSyntax is not ported;
    // this parser only parses TS files.
    fn parse_class_element(&mut self) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        if self.token == SyntaxKind::SemicolonToken {
            self.next_token();
            let n = self.factory.new_semicolon_class_element();
            let result = self.finish_node(n, pos);
            self.with_jsdoc(result, jsdoc);
            return result;
        }
        let modifiers = self.parse_modifiers_ex(
            true, /*allowDecorators*/
            true, /*permitConstAsModifier*/
            true, /*stopOnStartOfClassStaticBlock*/
        );
        if self.token == SyntaxKind::StaticKeyword
            && self.look_ahead(Self::next_token_is_open_brace)
        {
            return self.parse_class_static_block_declaration(pos, jsdoc, modifiers);
        }
        if self.parse_contextual_modifier(SyntaxKind::GetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                SyntaxKind::GetAccessor,
                PARSE_FLAGS_NONE,
            );
        }
        if self.parse_contextual_modifier(SyntaxKind::SetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                SyntaxKind::SetAccessor,
                PARSE_FLAGS_NONE,
            );
        }
        if self.token == SyntaxKind::ConstructorKeyword || self.token == SyntaxKind::StringLiteral {
            let constructor_declaration =
                self.try_parse_constructor_declaration(pos, jsdoc, modifiers);
            if !constructor_declaration.is_nil() {
                return constructor_declaration;
            }
        }
        if self.is_index_signature() {
            return self.parse_index_signature_declaration(pos, jsdoc, modifiers);
        }
        // It is very important that we check this *after* checking indexers because
        // the [ token can start an index signature or a computed property name
        if token_is_identifier_or_keyword(self.token)
            || self.token == SyntaxKind::StringLiteral
            || self.token == SyntaxKind::NumericLiteral
            || self.token == SyntaxKind::BigIntLiteral
            || self.token == SyntaxKind::AsteriskToken
            || self.token == SyntaxKind::OpenBracketToken
        {
            let is_ambient =
                !modifiers.is_nil() && modifiers.nodes().iter().any(is_declare_modifier);
            if is_ambient {
                for m in modifiers.nodes().iter() {
                    set_node_flags(m, m.flags() | NodeFlags::AMBIENT);
                }
                let save_context_flags = self.ctx;
                self.set_context_flags(NodeFlags::AMBIENT, true);
                let result = self.parse_property_or_method_declaration(pos, jsdoc, modifiers);
                self.ctx = save_context_flags;
                return result;
            } else {
                return self.parse_property_or_method_declaration(pos, jsdoc, modifiers);
            }
        }
        if !modifiers.is_nil() {
            // treat this as a property declaration with a missing name.
            let node_pos = self.node_pos();
            self.parse_error_at(node_pos, node_pos);
            let name = self.create_missing_identifier();
            return self.parse_property_declaration(
                pos,
                jsdoc,
                modifiers,
                name,
                Node::NIL, /*questionToken*/
            );
        }
        // 'isClassMemberStart' should have hinted not to attempt parsing.
        panic!("Should not have attempted to parse class member declaration.");
    }

    // Go: parser.go:1905 parseClassStaticBlockDeclaration
    fn parse_class_static_block_declaration(
        &mut self,
        pos: i32,
        jsdoc: u8,
        modifiers: ModifierList,
    ) -> Node {
        self.parse_expected_token(SyntaxKind::StaticKeyword);
        let body = self.parse_class_static_block_body();
        let n = self
            .factory
            .new_class_static_block_declaration(modifiers, body);
        let result = self.finish_node(n, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:1913 parseClassStaticBlockBody
    fn parse_class_static_block_body(&mut self) -> Node {
        let save_context_flags = self.ctx;
        self.set_context_flags(NodeFlags::YIELD_CONTEXT, false);
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, true);
        let body = self.parse_block(false /*ignoreMissingOpenBrace*/);
        self.ctx = save_context_flags;
        body
    }

    // Go: parser.go:1922 tryParseConstructorDeclaration
    // PORT: the diagnostic message argument is not kept. checkJSSyntax is
    // not ported; this parser only parses TS files.
    fn try_parse_constructor_declaration(
        &mut self,
        pos: i32,
        jsdoc: u8,
        modifiers: ModifierList,
    ) -> Node {
        let state = self.mark();
        if self.token == SyntaxKind::ConstructorKeyword
            || self.token == SyntaxKind::StringLiteral
                && self.sc.st.value == "constructor"
                && self.look_ahead(Self::next_token_is_open_paren)
        {
            self.next_token();
            let type_parameters = self.parse_type_parameters();
            let parameters = self.parse_parameters(PARSE_FLAGS_NONE);
            let return_type = self.parse_return_type(SyntaxKind::ColonToken, false /*isType*/);
            let body = self.parse_function_block_or_semicolon(PARSE_FLAGS_NONE);
            let n = self.factory.new_constructor_declaration(
                modifiers,
                type_parameters,
                parameters,
                return_type,
                Node::NIL, /*fullSignature*/
                body,
            );
            let result = self.finish_node(n, pos);
            self.with_jsdoc(result, jsdoc);
            return result;
        }
        self.rewind(state);
        Node::NIL
    }

    // Go: parser.go:1939 nextTokenIsOpenParen
    fn next_token_is_open_paren(&mut self) -> bool {
        self.next_token() == SyntaxKind::OpenParenToken
    }

    // Go: parser.go:4055 nextTokenIsOpenBrace
    fn next_token_is_open_brace(&mut self) -> bool {
        self.next_token() == SyntaxKind::OpenBraceToken
    }

    // Go: parser.go:1943 parsePropertyOrMethodDeclaration
    // PORT: the diagnostic message argument of parseMethodDeclaration is not
    // kept.
    fn parse_property_or_method_declaration(
        &mut self,
        pos: i32,
        jsdoc: u8,
        modifiers: ModifierList,
    ) -> Node {
        let asterisk_token = self.parse_optional_token(SyntaxKind::AsteriskToken);
        let name = self.parse_property_name();
        // Note: this is not legal as per the grammar.  But we allow it in the parser and
        // report an error in the grammar checker.
        let question_token = self.parse_optional_token(SyntaxKind::QuestionToken);
        if !asterisk_token.is_nil()
            || self.token == SyntaxKind::OpenParenToken
            || self.token == SyntaxKind::LessThanToken
        {
            return self.parse_method_declaration(
                pos,
                jsdoc,
                modifiers,
                asterisk_token,
                name,
                question_token,
            );
        }
        self.parse_property_declaration(pos, jsdoc, modifiers, name, question_token)
    }

    // Go: parser.go:1971 parsePropertyDeclaration
    // PORT: checkJSSyntax is not ported; this parser only parses TS files.
    fn parse_property_declaration(
        &mut self,
        pos: i32,
        jsdoc: u8,
        modifiers: ModifierList,
        name: Node,
        question_token: Node,
    ) -> Node {
        let mut postfix_token = question_token;
        if postfix_token.is_nil() && !self.has_preceding_line_break() {
            postfix_token = self.parse_optional_token(SyntaxKind::ExclamationToken);
        }
        let type_node = self.parse_type_annotation();
        let initializer = self.do_in_context(
            NodeFlags::YIELD_CONTEXT | NodeFlags::AWAIT_CONTEXT | NodeFlags::DISALLOW_IN_CONTEXT,
            false,
            Self::parse_initializer,
        );
        self.parse_semicolon_after_property_name(name, type_node, initializer);
        let n = self.factory.new_property_declaration(
            modifiers,
            name,
            postfix_token,
            type_node,
            initializer,
        );
        let result = self.finish_node(n, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:1985 parseSemicolonAfterPropertyName
    // PORT: the diagnostic messages are not kept, so both branches of the
    // type-node case report at the current token.
    fn parse_semicolon_after_property_name(
        &mut self,
        name: Node,
        type_node: Node,
        initializer: Node,
    ) {
        if self.token == SyntaxKind::AtToken && !self.has_preceding_line_break() {
            // Go: Decorators_must_precede_the_name_and_all_keywords_of_property_declarations
            self.parse_error_at_current_token();
            return;
        }
        if self.token == SyntaxKind::OpenParenToken {
            // Go: Cannot_start_a_function_call_in_a_type_annotation
            self.parse_error_at_current_token();
            self.next_token();
            return;
        }
        if !type_node.is_nil() && !self.can_parse_semicolon() {
            if !initializer.is_nil() {
                // Go: X_0_expected with ";"
                self.parse_error_at_current_token();
            } else {
                // Go: Expected_for_property_initializer
                self.parse_error_at_current_token();
            }
            return;
        }
        if self.try_parse_semicolon() {
            return;
        }
        if !initializer.is_nil() {
            // Go: X_0_expected with ";"
            self.parse_error_at_current_token();
            return;
        }
        self.parse_error_for_missing_semicolon_after(name);
    }

    // Go: parser.go:2013 parseErrorForMissingSemicolonAfter
    // PORT: the diagnostic messages and their arguments are not kept. The
    // spelling suggestion is still computed, because an unknown token is only
    // skipped when there is no suggestion.
    fn parse_error_for_missing_semicolon_after(&mut self, node: Node) {
        // Tagged template literals are sometimes used in places where only simple strings are allowed, i.e.:
        //   module `M1` {
        //   ^^^^^^^^^^^ This block is parsed as a template literal like module`M1`.
        if node.kind() == SyntaxKind::TaggedTemplateExpression {
            let range = self.skip_range_trivia(node.template().loc());
            // Go: Module_declaration_names_may_only_use_or_quoted_strings
            self.parse_error_at_range(range.pos());
            return;
        }
        // Otherwise, if this isn't a well-known keyword-like identifier, give the generic fallback message.
        let mut expression_text = "";
        if node.kind() == SyntaxKind::Identifier {
            expression_text = node.text();
        }
        if expression_text.is_empty() {
            // Go: X_0_expected with ";"
            self.parse_error_at_current_token();
            return;
        }
        let pos = skip_trivia(self.source_text, node.pos());
        // Some known keywords are likely signs of syntax being used improperly.
        match expression_text {
            "const" | "let" | "var" => {
                // Go: Variable_declaration_not_allowed_at_this_location
                self.parse_error_at(pos, node.end());
                return;
            }
            "declare" => {
                // If a declared node failed to parse, it would have emitted a diagnostic already.
                return;
            }
            "interface" => {
                self.parse_error_for_invalid_name(SyntaxKind::OpenBraceToken);
                return;
            }
            "is" => {
                // Go: A_type_predicate_is_only_allowed_in_return_type_position_for_functions_and_methods
                let token_start = self.sc.st.token_start;
                self.parse_error_at(pos, token_start);
                return;
            }
            "module" | "namespace" => {
                self.parse_error_for_invalid_name(SyntaxKind::OpenBraceToken);
                return;
            }
            "type" => {
                self.parse_error_for_invalid_name(SyntaxKind::EqualsToken);
                return;
            }
            _ => {}
        }
        // The user alternatively might have misspelled or forgotten to add a space after a common keyword.
        let mut suggestion = get_spelling_suggestion_for_strings(
            expression_text,
            VIABLE_KEYWORD_SUGGESTIONS.iter().cloned(),
        );
        if suggestion.is_empty() {
            suggestion = get_space_suggestion(expression_text);
        }
        if !suggestion.is_empty() {
            // Go: Unknown_keyword_or_identifier_Did_you_mean_0
            self.parse_error_at(pos, node.end());
            return;
        }
        // Unknown tokens are handled with their own errors in the scanner
        if self.token == SyntaxKind::Unknown {
            return;
        }
        // Otherwise, we know this some kind of unknown word, not just a missing expected semicolon.
        // Go: Unexpected_keyword_or_identifier
        self.parse_error_at(pos, node.end());
    }

    // Go: parser.go:2078 parseErrorForInvalidName
    // PORT: the diagnostic messages are not kept; both report at the current
    // token.
    fn parse_error_for_invalid_name(&mut self, token_if_blank_name: SyntaxKind) {
        if self.token == token_if_blank_name {
            self.parse_error_at_current_token();
        } else {
            self.parse_error_at_current_token();
        }
    }

    // Go: parser.go:6409 skipRangeTrivia
    fn skip_range_trivia(&self, text_range: TextRange) -> TextRange {
        TextRange::new(
            skip_trivia(self.source_text, text_range.pos()),
            text_range.end(),
        )
    }

    // Go: parser.go:1210 parseBlock
    // PORT: the diagnostic message argument is not kept. parseStatement is
    // not ported yet.
    fn parse_block(&mut self, ignore_missing_open_brace: bool) -> Node {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let open_brace_parsed = self.parse_expected(SyntaxKind::OpenBraceToken);
        if open_brace_parsed || ignore_missing_open_brace {
            let multi_line = self.has_preceding_line_break();
            let statements = self.parse_list(ParsingContext::BlockStatements, |_| {
                unported!("parseStatement")
            });
            self.parse_expected_matching_brackets(SyntaxKind::CloseBraceToken, open_brace_parsed);
            let n = self.factory.new_block(statements, multi_line);
            let result = self.finish_node(n, pos);
            self.with_jsdoc(result, jsdoc);
            if self.token == SyntaxKind::EqualsToken {
                self.parse_error_at_current_token();
                self.next_token();
            }
            return result;
        }
        let statements = self.create_missing_list();
        let n = self.factory.new_block(statements, false);
        let result = self.finish_node(n, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    // Go: parser.go:3488 parseFunctionBlockOrSemicolon
    // PORT: the diagnostic message argument is not kept.
    fn parse_function_block_or_semicolon(&mut self, flags: u8) -> Node {
        if self.token != SyntaxKind::OpenBraceToken {
            if flags & PARSE_FLAGS_TYPE != 0 {
                self.parse_type_member_semicolon();
                return Node::NIL;
            }
            if self.can_parse_semicolon() {
                self.parse_semicolon();
                return Node::NIL;
            }
        }
        self.parse_function_block(flags)
    }

    // Go: parser.go:3502 parseFunctionBlock
    // PORT: the diagnostic message argument and statementHasAwaitIdentifier
    // are not kept.
    fn parse_function_block(&mut self, flags: u8) -> Node {
        let save = self.ctx;
        self.set_context_flags(NodeFlags::YIELD_CONTEXT, flags & PARSE_FLAGS_YIELD != 0);
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, flags & PARSE_FLAGS_AWAIT != 0);
        self.set_context_flags(NodeFlags::DECORATOR_CONTEXT, false);
        let block = self.parse_block(flags & PARSE_FLAGS_IGNORE_MISSING_OPEN_BRACE != 0);
        self.ctx = save;
        block
    }

    // Go: parser.go:3862 parseModifiers
    fn parse_modifiers(&mut self) -> ModifierList {
        self.parse_modifiers_ex(false, false, false)
    }

    // Go: jsdoc.go:939 parseImportTag
    fn parse_import_tag(
        &mut self,
        start: i32,
        tag_name: Node,
        margin: i32,
        indent_text: &str,
    ) -> Node {
        let after_import_tag_pos = self.sc.st.full_start;
        let mut identifier = Node::NIL;
        if self.is_identifier() {
            identifier = self.parse_identifier();
        }
        let import_clause = self.try_parse_import_clause(
            identifier,
            after_import_tag_pos,
            SyntaxKind::TypeKeyword,
            true,
        );
        let module_specifier = self.parse_module_specifier();
        let attributes = self.try_parse_import_attributes();
        let end = self.node_pos();
        let comments = self.parse_trailing_tag_comments(start, end, margin, indent_text);
        let n = new_jsdoc_import_tag(
            tag_name,
            import_clause,
            module_specifier,
            attributes,
            comments,
        );
        self.finish_node(n, start)
    }

    // Go: parser.go:2327 parseModuleSpecifier
    fn parse_module_specifier(&mut self) -> Node {
        if self.token == SyntaxKind::StringLiteral {
            return self.parse_literal_expression();
        }
        self.parse_expression()
    }

    // Go: parser.go:2338 tryParseImportClause
    fn try_parse_import_clause(
        &mut self,
        identifier: Node,
        pos: i32,
        phase_modifier: SyntaxKind,
        skip_jsdoc_leading_asterisks: bool,
    ) -> Node {
        if !identifier.is_nil()
            || self.token == SyntaxKind::AsteriskToken
            || self.token == SyntaxKind::OpenBraceToken
        {
            let import_clause = self.parse_import_clause(
                identifier,
                pos,
                phase_modifier,
                skip_jsdoc_leading_asterisks,
            );
            self.parse_expected(SyntaxKind::FromKeyword);
            return import_clause;
        }
        Node::NIL
    }

    // Go: parser.go:2350 parseImportClause
    // PORT: statementHasAwaitIdentifier is not kept.
    fn parse_import_clause(
        &mut self,
        identifier: Node,
        pos: i32,
        phase_modifier: SyntaxKind,
        skip_jsdoc_leading_asterisks: bool,
    ) -> Node {
        let mut named_bindings = Node::NIL;
        if identifier.is_nil() || self.parse_optional(SyntaxKind::CommaToken) {
            if skip_jsdoc_leading_asterisks {
                self.sc.set_skip_jsdoc_leading_asterisks(true);
            }
            named_bindings = if self.token == SyntaxKind::AsteriskToken {
                self.parse_namespace_import()
            } else {
                self.parse_named_imports()
            };
            if skip_jsdoc_leading_asterisks {
                self.sc.set_skip_jsdoc_leading_asterisks(false);
            }
        }
        let n = new_import_clause(phase_modifier, identifier, named_bindings);
        self.finish_node(n, pos)
    }

    // Go: parser.go:2379 parseNamespaceImport
    fn parse_namespace_import(&mut self) -> Node {
        let pos = self.node_pos();
        self.parse_expected(SyntaxKind::AsteriskToken);
        self.parse_expected(SyntaxKind::AsKeyword);
        let name = self.parse_identifier();
        let n = new_namespace_import(name);
        self.finish_node(n, pos)
    }

    // Go: parser.go:2389 parseNamedImports
    fn parse_named_imports(&mut self) -> Node {
        let pos = self.node_pos();
        let imports = self.parse_bracketed_list(
            ParsingContext::ImportOrExportSpecifiers,
            Self::parse_import_specifier,
            SyntaxKind::OpenBraceToken,
            SyntaxKind::CloseBraceToken,
        );
        let n = new_named_imports(imports);
        self.finish_node(n, pos)
    }

    // Go: parser.go:2399 parseImportSpecifier
    // PORT: checkJSSyntax is not ported; this parser only parses TS files.
    fn parse_import_specifier(&mut self) -> Node {
        let pos = self.node_pos();
        let (is_type_only, property_name, name) =
            self.parse_import_or_export_specifier(SyntaxKind::ImportSpecifier);
        let identifier_name;
        if name.kind() == SyntaxKind::Identifier {
            identifier_name = name;
        } else {
            let start = skip_trivia(self.sc.text, name.pos());
            self.parse_error_at_range(start);
            identifier_name = self.new_identifier("");
            self.finish_node(identifier_name, name.pos());
        }
        let n = new_import_specifier(is_type_only, property_name, identifier_name);
        self.finish_node(n, pos)
    }

    // Go: parser.go:2414 parseImportOrExportSpecifier
    fn parse_import_or_export_specifier(&mut self, kind: SyntaxKind) -> (bool, Node, Node) {
        let mut is_type_only = false;
        let mut property_name = Node::NIL;
        let mut can_parse_as_keyword = true;
        let disallow_keywords = kind == SyntaxKind::ImportSpecifier;
        let (mut name, mut name_ok) = self.parse_module_export_name(disallow_keywords);
        if name.kind() == SyntaxKind::Identifier && name.text() == "type" {
            if self.token == SyntaxKind::AsKeyword {
                let first_as = self.parse_identifier_name();
                if self.token == SyntaxKind::AsKeyword {
                    let second_as = self.parse_identifier_name();
                    if self.can_parse_module_export_name() {
                        is_type_only = true;
                        property_name = first_as;
                        (name, name_ok) = self.parse_module_export_name(disallow_keywords);
                        can_parse_as_keyword = false;
                    } else {
                        property_name = name;
                        name = second_as;
                        can_parse_as_keyword = false;
                    }
                } else if self.can_parse_module_export_name() {
                    property_name = name;
                    can_parse_as_keyword = false;
                    (name, name_ok) = self.parse_module_export_name(disallow_keywords);
                } else {
                    is_type_only = true;
                    name = first_as;
                }
            } else if self.can_parse_module_export_name() {
                is_type_only = true;
                (name, name_ok) = self.parse_module_export_name(disallow_keywords);
            }
        }
        if can_parse_as_keyword && self.token == SyntaxKind::AsKeyword {
            property_name = name;
            self.parse_expected(SyntaxKind::AsKeyword);
            (name, name_ok) = self.parse_module_export_name(disallow_keywords);
        }
        if !name_ok {
            let start = skip_trivia(self.sc.text, name.pos());
            self.parse_error_at_range(start);
        }
        (is_type_only, property_name, name)
    }

    // Go: parser.go:2486 canParseModuleExportName
    fn can_parse_module_export_name(&self) -> bool {
        token_is_identifier_or_keyword(self.token) || self.token == SyntaxKind::StringLiteral
    }

    // Go: parser.go:2490 parseModuleExportName
    fn parse_module_export_name(&mut self, disallow_keywords: bool) -> (Node, bool) {
        let mut name_ok = true;
        if self.token == SyntaxKind::StringLiteral {
            return (self.parse_literal_expression(), name_ok);
        }
        if disallow_keywords && is_keyword(self.token) && !self.is_identifier() {
            name_ok = false;
        }
        (self.parse_identifier_name(), name_ok)
    }

    // Go: parser.go:2502 tryParseImportAttributes
    fn try_parse_import_attributes(&mut self) -> Node {
        if self.token == SyntaxKind::WithKeyword
            || (self.token == SyntaxKind::AssertKeyword && !self.has_preceding_line_break())
        {
            if self.token == SyntaxKind::AssertKeyword {
                self.parse_error_at_current_token();
            }
            return self.parse_import_attributes(self.token, false);
        }
        Node::NIL
    }
}

// Go: parser.go:112 viableKeywordSuggestions
static VIABLE_KEYWORD_SUGGESTIONS: std::sync::LazyLock<Vec<String>> =
    std::sync::LazyLock::new(get_viable_keyword_suggestions);

// Go: parser.go:1195 isDeclareModifier
fn is_declare_modifier(modifier: Node) -> bool {
    modifier.kind() == SyntaxKind::DeclareKeyword
}

// Go: parser.go:2069 getSpaceSuggestion
fn get_space_suggestion(expression_text: &str) -> String {
    for keyword in VIABLE_KEYWORD_SUGGESTIONS.iter() {
        if expression_text.len() > keyword.len() + 2
            && expression_text.starts_with(keyword.as_str())
        {
            return format!("{} {}", keyword, &expression_text[keyword.len()..]);
        }
    }
    String::new()
}

// Go: parser.go:1967 modifierListHasAsync
fn modifier_list_has_async(modifiers: ModifierList) -> bool {
    !modifiers.is_nil()
        && modifiers
            .nodes()
            .iter()
            .any(|m| m.kind() == SyntaxKind::AsyncKeyword)
}

// Go: parser.go:5744 unparseExpressionWithTypeArguments
fn unparse_expression_with_type_arguments(
    expression: Node,
    type_arguments: NodeList,
    result: Node,
) {
    if !expression.is_nil() {
        set_node_parent(expression, result);
    }
    if !type_arguments.is_nil() {
        for a in type_arguments.nodes().iter() {
            set_node_parent(a, result);
        }
    }
}

/// Go `factory.NewMetaProperty(keywordToken, name)`.
// PORT: the Rust factory has no meta property constructor.
fn new_meta_property(keyword_token: SyntaxKind, name: Node) -> Node {
    let data = ts_ast::MetaPropertyData {
        flow_node: None,
        keyword_token,
        facts: 0,
        name: id(name),
    };
    alloc_synthetic_node(SyntaxKind::MetaProperty, D::MetaProperty(Box::new(data)))
}

/// Go `factory.NewTemplateExpression(head, templateSpans)`.
// PORT: the Rust factory has no template expression constructor.
fn new_template_expression(head: Node, template_spans: NodeList) -> Node {
    let data = ts_ast::TemplateExpressionData {
        head: id(head),
        template_spans: synthetic_req_list_value(template_spans),
        facts: 0,
    };
    alloc_synthetic_node(
        SyntaxKind::TemplateExpression,
        D::TemplateExpression(Box::new(data)),
    )
}

/// Go `factory.NewTemplateSpan(expression, literal)`.
// PORT: the Rust factory has no template span constructor.
fn new_template_span(expression: Node, literal: Node) -> Node {
    let data = ts_ast::TemplateSpanData {
        expression: id(expression),
        literal: id(literal),
    };
    alloc_synthetic_node(SyntaxKind::TemplateSpan, D::TemplateSpan(Box::new(data)))
}

/// Go `factory.NewSpreadAssignment(expression)`.
// PORT: the Rust factory has no spread assignment constructor.
fn new_spread_assignment(expression: Node) -> Node {
    let data = ts_ast::SpreadAssignmentData {
        expression: id(expression),
        symbol: None,
    };
    alloc_synthetic_node(
        SyntaxKind::SpreadAssignment,
        D::SpreadAssignment(Box::new(data)),
    )
}

/// Go `factory.NewShorthandPropertyAssignment(modifiers, name, postfixToken, typeNode, equalsToken, objectAssignmentInitializer)`.
// PORT: the Rust factory has no shorthand property assignment constructor.
fn new_shorthand_property_assignment(
    modifiers: ModifierList,
    name: Node,
    postfix_token: Node,
    type_node: Node,
    equals_token: Node,
    object_assignment_initializer: Node,
) -> Node {
    let data = ts_ast::ShorthandPropertyAssignmentData {
        equals_token: oid(equals_token),
        object_assignment_initializer: oid(object_assignment_initializer),
        postfix_token: oid(postfix_token),
        symbol: None,
        type_: oid(type_node),
        facts: 0,
        modifiers: synthetic_modifiers_value(modifiers),
        name: id(name),
    };
    alloc_synthetic_node(
        SyntaxKind::ShorthandPropertyAssignment,
        D::ShorthandPropertyAssignment(Box::new(data)),
    )
}

/// Go `factory.NewMissingDeclaration(modifiers)`.
// PORT: the Rust factory has no missing declaration constructor.
fn new_missing_declaration(modifiers: ModifierList) -> Node {
    let data = ts_ast::MissingDeclarationData {
        flow_node: None,
        symbol: None,
        modifiers: synthetic_modifiers_value(modifiers),
    };
    alloc_synthetic_node(
        SyntaxKind::MissingDeclaration,
        D::MissingDeclaration(Box::new(data)),
    )
}

/// Go `factory.NewImportClause(phaseModifier, name, namedBindings)`.
// PORT: the Rust factory has no import clause constructor. Go KindUnknown
// is `None`.
fn new_import_clause(phase_modifier: SyntaxKind, name: Node, named_bindings: Node) -> Node {
    let data = ts_ast::ImportClauseData {
        local_symbol: None,
        named_bindings: oid(named_bindings),
        phase_modifier: if phase_modifier == SyntaxKind::Unknown {
            None
        } else {
            Some(phase_modifier)
        },
        symbol: None,
        facts: 0,
        name: oid(name),
    };
    alloc_synthetic_node(SyntaxKind::ImportClause, D::ImportClause(Box::new(data)))
}

/// Go `factory.NewNamedImports(elements)`.
// PORT: the Rust factory has no named imports constructor.
fn new_named_imports(elements: NodeList) -> Node {
    let data = ts_ast::NamedImportsData {
        elements: synthetic_req_list_value(elements),
        facts: 0,
    };
    alloc_synthetic_node(SyntaxKind::NamedImports, D::NamedImports(Box::new(data)))
}

/// Go `factory.NewImportSpecifier(isTypeOnly, propertyName, name)`.
// PORT: the Rust factory has no import specifier constructor.
fn new_import_specifier(is_type_only: bool, property_name: Node, name: Node) -> Node {
    let data = ts_ast::ImportSpecifierData {
        is_type_only,
        local_symbol: None,
        property_name: oid(property_name),
        symbol: None,
        facts: 0,
        name: id(name),
    };
    alloc_synthetic_node(
        SyntaxKind::ImportSpecifier,
        D::ImportSpecifier(Box::new(data)),
    )
}

/// Go `factory.NewNamespaceImport(name)`.
// PORT: the Rust factory has no namespace import constructor.
fn new_namespace_import(name: Node) -> Node {
    let data = ts_ast::NamespaceImportData {
        local_symbol: None,
        symbol: None,
        name: id(name),
    };
    alloc_synthetic_node(
        SyntaxKind::NamespaceImport,
        D::NamespaceImport(Box::new(data)),
    )
}

/// Go `factory.NewJSDocImportTag(tagName, importClause, moduleSpecifier, attributes, comment)`.
// PORT: the Rust factory has no JSDoc import tag constructor.
fn new_jsdoc_import_tag(
    tag_name: Node,
    import_clause: Node,
    module_specifier: Node,
    attributes: Node,
    comment: NodeList,
) -> Node {
    let data = ts_ast::JsDocImportTagData {
        attributes: oid(attributes),
        comment: opt_list(comment),
        import_clause: oid(import_clause),
        module_specifier: id(module_specifier),
        tag_name: id(tag_name),
    };
    alloc_synthetic_node(
        SyntaxKind::JsDocImportTag,
        D::JsDocImportTag(Box::new(data)),
    )
}

/// Go `factory.NewBindingPattern(kind, elements)`.
// PORT: the Rust factory has no binding pattern constructor.
fn new_binding_pattern(kind: SyntaxKind, elements: NodeList) -> Node {
    let data = ts_ast::BindingPatternData {
        elements: synthetic_req_list_value(elements),
        facts: 0,
    };
    alloc_synthetic_node(kind, D::BindingPattern(Box::new(data)))
}

/// Go `factory.NewBindingElement(dotDotDotToken, propertyName, name, initializer)`.
// PORT: the Rust factory has no binding element constructor.
fn new_binding_element(
    dot_dot_dot_token: Node,
    property_name: Node,
    name: Node,
    initializer: Node,
) -> Node {
    let data = ts_ast::BindingElementData {
        dot_dot_dot_token: oid(dot_dot_dot_token),
        flow_node: None,
        initializer: oid(initializer),
        local_symbol: None,
        property_name: oid(property_name),
        symbol: None,
        facts: 0,
        name: oid(name),
    };
    alloc_synthetic_node(
        SyntaxKind::BindingElement,
        D::BindingElement(Box::new(data)),
    )
}
