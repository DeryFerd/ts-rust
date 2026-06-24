use ts_ast::SyntaxKind;
use ts_core::{Diagnostic, DiagnosticCategory, JsString, TextPos, TextRange};
use ts_diagnostics::{Category, message_by_code};

/// One lexical token. `range` uses UTF-8 byte offsets and `text` is the exact
/// source spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token<'a> {
    pub kind: SyntaxKind,
    pub full_start: TextPos,
    pub range: TextRange,
    pub text: &'a str,
    pub flags: TokenFlags,
    pub value: Option<JsString>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TokenFlags(u32);

impl TokenFlags {
    pub const NONE: Self = Self(0);
    pub const PRECEDING_LINE_BREAK: Self = Self(1 << 0);
    pub const PRECEDING_JSDOC_COMMENT: Self = Self(1 << 1);
    pub const UNTERMINATED: Self = Self(1 << 2);
    pub const EXTENDED_UNICODE_ESCAPE: Self = Self(1 << 3);
    pub const SCIENTIFIC: Self = Self(1 << 4);
    pub const OCTAL: Self = Self(1 << 5);
    pub const HEX_SPECIFIER: Self = Self(1 << 6);
    pub const BINARY_SPECIFIER: Self = Self(1 << 7);
    pub const OCTAL_SPECIFIER: Self = Self(1 << 8);
    pub const CONTAINS_SEPARATOR: Self = Self(1 << 9);
    pub const UNICODE_ESCAPE: Self = Self(1 << 10);
    pub const CONTAINS_INVALID_ESCAPE: Self = Self(1 << 11);
    pub const HEX_ESCAPE: Self = Self(1 << 12);
    pub const CONTAINS_LEADING_ZERO: Self = Self(1 << 13);
    pub const CONTAINS_INVALID_SEPARATOR: Self = Self(1 << 14);
    pub const PRECEDING_JSDOC_LEADING_ASTERISKS: Self = Self(1 << 15);
    pub const SINGLE_QUOTE: Self = Self(1 << 16);
    pub const PRECEDING_JSDOC_WITH_DEPRECATED: Self = Self(1 << 17);
    pub const PRECEDING_JSDOC_WITH_SEE_OR_LINK: Self = Self(1 << 18);

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    fn insert(&mut self, other: Self) {
        self.0 |= other.0;
    }
}

/// A cheap scanner checkpoint used for parser lookahead and speculative parse.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScannerCheckpoint {
    byte_pos: usize,
    diagnostics_len: usize,
    last_full_start: usize,
    last_start: usize,
    last_kind: SyntaxKind,
    last_flags: TokenFlags,
    last_value: Option<JsString>,
}

/// Stateful scanner for TypeScript source text.
pub struct Scanner<'a> {
    source: &'a str,
    byte_pos: usize,
    skip_trivia: bool,
    skip_jsdoc_leading_asterisks: u32,
    language_variant: LanguageVariant,
    diagnostics: Vec<Diagnostic>,
    last_full_start: usize,
    last_start: usize,
    last_kind: SyntaxKind,
    last_flags: TokenFlags,
    last_value: Option<JsString>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum LanguageVariant {
    #[default]
    Standard,
    Jsx,
}

impl<'a> Scanner<'a> {
    #[must_use]
    pub const fn new(source: &'a str) -> Self {
        Self {
            source,
            byte_pos: 0,
            skip_trivia: true,
            skip_jsdoc_leading_asterisks: 0,
            language_variant: LanguageVariant::Standard,
            diagnostics: Vec::new(),
            last_full_start: 0,
            last_start: 0,
            last_kind: SyntaxKind::Unknown,
            last_flags: TokenFlags::NONE,
            last_value: None,
        }
    }

    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub fn set_text(&mut self, source: &'a str) {
        self.source = source;
        self.diagnostics.clear();
        self.reset_token_state(0);
    }

    pub fn reset(&mut self) {
        self.source = "";
        self.diagnostics.clear();
        self.skip_trivia = true;
        self.skip_jsdoc_leading_asterisks = 0;
        self.language_variant = LanguageVariant::Standard;
        self.reset_token_state(0);
    }

    /// Resets scanning to a byte offset in the current source text.
    ///
    /// # Panics
    ///
    /// Panics if `byte_pos` is not a UTF-8 character boundary.
    pub fn reset_pos(&mut self, byte_pos: usize) {
        assert!(
            self.source.is_char_boundary(byte_pos),
            "scanner position must be a UTF-8 character boundary"
        );
        self.byte_pos = byte_pos;
        self.last_full_start = byte_pos;
        self.last_start = byte_pos;
    }

    pub fn reset_token_state(&mut self, byte_pos: usize) {
        self.reset_pos(byte_pos);
        self.last_kind = SyntaxKind::Unknown;
        self.last_flags = TokenFlags::NONE;
        self.last_value = None;
    }

    pub const fn set_skip_trivia(&mut self, skip: bool) {
        self.skip_trivia = skip;
    }

    pub const fn set_language_variant(&mut self, variant: LanguageVariant) {
        self.language_variant = variant;
    }

    pub fn set_skip_jsdoc_leading_asterisks(&mut self, skip: bool) {
        if skip {
            self.skip_jsdoc_leading_asterisks += 1;
        } else {
            self.skip_jsdoc_leading_asterisks = self.skip_jsdoc_leading_asterisks.saturating_sub(1);
        }
    }

    #[must_use]
    pub fn mark(&self) -> ScannerCheckpoint {
        ScannerCheckpoint {
            byte_pos: self.byte_pos,
            diagnostics_len: self.diagnostics.len(),
            last_full_start: self.last_full_start,
            last_start: self.last_start,
            last_kind: self.last_kind,
            last_flags: self.last_flags,
            last_value: self.last_value.clone(),
        }
    }

    pub fn rewind(&mut self, checkpoint: ScannerCheckpoint) {
        self.byte_pos = checkpoint.byte_pos;
        self.diagnostics.truncate(checkpoint.diagnostics_len);
        self.last_full_start = checkpoint.last_full_start;
        self.last_start = checkpoint.last_start;
        self.last_kind = checkpoint.last_kind;
        self.last_flags = checkpoint.last_flags;
        self.last_value = checkpoint.last_value;
    }

    pub fn scan(&mut self) -> Token<'a> {
        let full_start = self.byte_pos;
        if !self.skip_trivia && self.byte_pos == 0 && self.starts_with("#!") {
            while self.peek().is_some_and(|ch| !is_line_break(ch)) {
                self.bump();
            }
        }
        if !self.skip_trivia
            && let Some((kind, flags, start)) = self.scan_trivia_token()
        {
            self.last_flags = flags;
            self.last_value = None;
            return self.finish_token(kind, full_start, start);
        }
        let mut flags = if self.skip_trivia {
            self.skip_trivia()
        } else {
            TokenFlags::NONE
        };
        if self.skip_jsdoc_leading_asterisks != 0
            && flags.contains(TokenFlags::PRECEDING_LINE_BREAK)
            && self.peek() == Some('*')
        {
            self.bump();
            flags.insert(TokenFlags::PRECEDING_JSDOC_LEADING_ASTERISKS);
            flags.insert(self.skip_trivia());
        }
        let start_byte = self.byte_pos;
        self.last_flags = flags;
        self.last_value = None;
        let Some(ch) = self.peek() else {
            return self.finish_token(SyntaxKind::EndOfFile, full_start, start_byte);
        };

        let kind = if is_identifier_start(ch)
            || ch == '\\'
                && self
                    .peek_unicode_escape()
                    .is_some_and(|(escaped, _, _)| is_identifier_start(escaped))
        {
            self.scan_identifier()
        } else if ch.is_ascii_digit() {
            self.scan_number()
        } else {
            match ch {
                '\'' | '"' => self.scan_string(ch),
                '`' => self.scan_template(),
                '#' => self.scan_private_identifier(),
                '.' if self.peek_next().is_some_and(|next| next.is_ascii_digit()) => {
                    self.scan_number()
                }
                _ => self.scan_punctuation(),
            }
        };

        self.finish_token(kind, full_start, start_byte)
    }

    fn scan_trivia_token(&mut self) -> Option<(SyntaxKind, TokenFlags, usize)> {
        let start = self.byte_pos;
        let ch = self.peek()?;
        let mut flags = TokenFlags::NONE;
        if self.is_conflict_marker_at(start) {
            self.scan_conflict_marker();
            return Some((SyntaxKind::ConflictMarkerTrivia, flags, start));
        }
        if is_line_break(ch) {
            flags.insert(TokenFlags::PRECEDING_LINE_BREAK);
            self.bump();
            if ch == '\r' && self.peek() == Some('\n') {
                self.bump();
            }
            return Some((SyntaxKind::NewLineTrivia, flags, start));
        }
        if is_whitespace_like(ch) {
            while self
                .peek()
                .is_some_and(|next| is_whitespace_like(next) && !is_line_break(next))
            {
                self.bump();
            }
            return Some((SyntaxKind::WhitespaceTrivia, flags, start));
        }
        if self.starts_with("//") {
            self.bump_ascii(2);
            while self.peek().is_some_and(|next| !is_line_break(next)) {
                self.bump();
            }
            return Some((SyntaxKind::SingleLineCommentTrivia, flags, start));
        }
        if self.starts_with("/*") {
            let start = self.byte_pos;
            let is_jsdoc = self.starts_with("/**") && !self.starts_with("/**/");
            self.bump_ascii(2);
            while self.peek().is_some() && !self.starts_with("*/") {
                if self.peek().is_some_and(is_line_break) {
                    flags.insert(TokenFlags::PRECEDING_LINE_BREAK);
                }
                self.bump();
            }
            if self.starts_with("*/") {
                self.bump_ascii(2);
            } else {
                flags.insert(TokenFlags::UNTERMINATED);
                self.error(start, self.byte_pos, "Unterminated comment.");
            }
            if is_jsdoc {
                flags.insert(TokenFlags::PRECEDING_JSDOC_COMMENT);
                self.scan_jsdoc_tags(start, self.byte_pos, &mut flags);
            }
            return Some((SyntaxKind::MultiLineCommentTrivia, flags, start));
        }
        None
    }

    fn finish_token(
        &mut self,
        kind: SyntaxKind,
        full_start: usize,
        start_byte: usize,
    ) -> Token<'a> {
        self.last_full_start = full_start;
        self.last_start = start_byte;
        self.last_kind = kind;
        self.current_token()
    }

    fn current_token(&self) -> Token<'a> {
        Token {
            kind: self.last_kind,
            full_start: text_pos(self.last_full_start),
            range: TextRange::new(text_pos(self.last_start), text_pos(self.byte_pos)),
            text: &self.source[self.last_start..self.byte_pos],
            flags: self.last_flags,
            value: self.last_value.clone(),
        }
    }

    fn skip_trivia(&mut self) -> TokenFlags {
        let mut flags = TokenFlags::default();
        loop {
            let before = self.byte_pos;
            while self.peek().is_some_and(is_whitespace_like) {
                if self.peek().is_some_and(is_line_break) {
                    flags.insert(TokenFlags::PRECEDING_LINE_BREAK);
                }
                self.bump();
            }
            if self.starts_with("//") {
                self.bump_ascii(2);
                while self.peek().is_some_and(|ch| !is_line_break(ch)) {
                    self.bump();
                }
            } else if self.starts_with("/*") {
                let start = self.byte_pos;
                let is_jsdoc = self.starts_with("/**") && !self.starts_with("/**/");
                self.bump_ascii(2);
                while self.peek().is_some() && !self.starts_with("*/") {
                    if self.peek().is_some_and(is_line_break) {
                        flags.insert(TokenFlags::PRECEDING_LINE_BREAK);
                    }
                    self.bump();
                }
                if self.starts_with("*/") {
                    self.bump_ascii(2);
                } else {
                    self.error(start, self.byte_pos, "Unterminated comment.");
                }
                if is_jsdoc {
                    flags.insert(TokenFlags::PRECEDING_JSDOC_COMMENT);
                    self.scan_jsdoc_tags(start, self.byte_pos, &mut flags);
                }
            } else if self.byte_pos == 0 && self.starts_with("#!") {
                while self.peek().is_some_and(|ch| !is_line_break(ch)) {
                    self.bump();
                }
            } else if self.is_conflict_marker_at(self.byte_pos) {
                let marker_start = self.byte_pos;
                self.scan_conflict_marker();
                if self.source[marker_start..self.byte_pos].contains(['\n', '\r']) {
                    flags.insert(TokenFlags::PRECEDING_LINE_BREAK);
                }
            }
            if before == self.byte_pos {
                break;
            }
        }
        flags
    }

    fn scan_jsdoc_tags(&self, start: usize, end: usize, flags: &mut TokenFlags) {
        let text = &self.source[start..end];
        for (tag, flag) in [
            ("deprecated", TokenFlags::PRECEDING_JSDOC_WITH_DEPRECATED),
            ("see", TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK),
            ("link", TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK),
            ("linkcode", TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK),
            ("linkplain", TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK),
        ] {
            let needle = format!("@{tag}");
            if text.match_indices(&needle).any(|(index, _)| {
                text[index + needle.len()..]
                    .chars()
                    .next()
                    .is_none_or(|ch| ch.is_whitespace() || matches!(ch, '}' | '*'))
            }) {
                flags.insert(flag);
            }
        }
    }

    /// Reinterprets a parser-contextual `>` token as a shift or comparison
    /// operator.
    pub fn rescan_greater_than_token(&mut self) -> Token<'a> {
        if self.last_kind != SyntaxKind::GreaterThanToken {
            return self.current_token();
        }
        self.byte_pos = self.last_start + 1;
        self.last_kind = if self.starts_with(">>=") {
            self.bump_ascii(3);
            SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken
        } else if self.starts_with(">>") {
            self.bump_ascii(2);
            SyntaxKind::GreaterThanGreaterThanGreaterThanToken
        } else if self.starts_with(">=") {
            self.bump_ascii(2);
            SyntaxKind::GreaterThanGreaterThanEqualsToken
        } else if self.peek() == Some('>') {
            self.bump_ascii(1);
            SyntaxKind::GreaterThanGreaterThanToken
        } else if self.peek() == Some('=') {
            self.bump_ascii(1);
            SyntaxKind::GreaterThanEqualsToken
        } else {
            SyntaxKind::GreaterThanToken
        };
        self.current_token()
    }

    /// Splits a parser-contextual `<<` token so its first character can begin
    /// type arguments and the second can begin a nested generic function type.
    pub fn rescan_less_than_token(&mut self) -> Token<'a> {
        if self.last_kind != SyntaxKind::LessThanLessThanToken {
            return self.current_token();
        }
        self.byte_pos = self.last_start + 1;
        self.last_kind = SyntaxKind::LessThanToken;
        self.current_token()
    }

    /// Reinterprets `/` or `/=` as a regular-expression literal.
    pub fn rescan_slash_token(&mut self) -> Token<'a> {
        if !matches!(
            self.last_kind,
            SyntaxKind::SlashToken | SyntaxKind::SlashEqualsToken
        ) {
            return self.current_token();
        }
        self.byte_pos = self.last_start;
        self.bump();
        let mut in_character_class = false;
        let mut terminated = false;
        while let Some(ch) = self.peek() {
            match ch {
                '\\' => {
                    self.bump();
                    if self.peek().is_some() {
                        self.bump();
                    }
                }
                '[' => {
                    in_character_class = true;
                    self.bump();
                }
                ']' => {
                    in_character_class = false;
                    self.bump();
                }
                '/' if !in_character_class => {
                    self.bump();
                    terminated = true;
                    break;
                }
                ch if is_line_break(ch) => break,
                _ => {
                    self.bump();
                }
            }
        }
        if terminated {
            while self.peek().is_some_and(is_identifier_part) {
                self.bump();
            }
        } else {
            self.last_flags.insert(TokenFlags::UNTERMINATED);
            self.error(
                self.last_start,
                self.byte_pos,
                "Unterminated regular expression literal.",
            );
        }
        self.last_kind = SyntaxKind::RegularExpressionLiteral;
        self.current_token()
    }

    /// Reinterprets a closing brace as the start of a template middle or tail
    /// after the parser finishes a `${ ... }` substitution.
    pub fn rescan_template_token(&mut self) -> Token<'a> {
        if self.last_kind != SyntaxKind::CloseBraceToken {
            return self.current_token();
        }
        self.byte_pos = self.last_start;
        self.bump();
        let mut value = JsString::default();
        let kind = loop {
            match self.peek() {
                Some('`') => {
                    self.bump();
                    break SyntaxKind::TemplateTail;
                }
                Some('$') if self.peek_next() == Some('{') => {
                    self.bump_ascii(2);
                    break SyntaxKind::TemplateMiddle;
                }
                Some('\\') => {
                    self.bump();
                    self.scan_escape_sequence(&mut value);
                }
                Some(ch) => {
                    value.push_char(ch);
                    self.bump();
                }
                None => {
                    self.last_flags.insert(TokenFlags::UNTERMINATED);
                    self.error(
                        self.last_start,
                        self.byte_pos,
                        "Unterminated template literal.",
                    );
                    break SyntaxKind::TemplateTail;
                }
            }
        };
        self.last_kind = kind;
        self.last_value = Some(value);
        self.current_token()
    }

    /// Reinterprets the leading `#` of a private identifier as a standalone
    /// hash token in a `JSDoc` parser context.
    pub fn rescan_hash_token(&mut self) -> Token<'a> {
        if self.last_kind != SyntaxKind::PrivateIdentifier {
            return self.current_token();
        }
        self.byte_pos = self.last_start + 1;
        self.last_kind = SyntaxKind::HashToken;
        self.last_value = None;
        self.current_token()
    }

    pub fn scan_jsx_token(&mut self) -> Token<'a> {
        self.scan_jsx_token_ex(true)
    }

    pub fn scan_jsx_token_ex(&mut self, allow_multiline_jsx_text: bool) -> Token<'a> {
        let full_start = self.byte_pos;
        let start = self.byte_pos;
        self.last_flags = TokenFlags::NONE;
        self.last_value = None;
        let kind = match self.peek() {
            None => SyntaxKind::EndOfFile,
            Some('<') if self.is_conflict_marker_at(start) => {
                self.scan_conflict_marker();
                SyntaxKind::ConflictMarkerTrivia
            }
            Some('<') if self.peek_next() == Some('/') => {
                self.bump_ascii(2);
                SyntaxKind::LessThanSlashToken
            }
            Some('<') => {
                self.bump();
                SyntaxKind::LessThanToken
            }
            Some('{') => {
                self.bump();
                SyntaxKind::OpenBraceToken
            }
            Some(_) => {
                let mut saw_line_break_before_content = false;
                let mut saw_non_whitespace = false;
                while let Some(ch) = self.peek() {
                    if matches!(ch, '<' | '{') {
                        break;
                    }
                    if ch == '>' {
                        self.error(
                            self.byte_pos,
                            self.byte_pos + 1,
                            "Unexpected token. Did you mean `&gt;`?",
                        );
                    } else if ch == '}' {
                        self.error(
                            self.byte_pos,
                            self.byte_pos + 1,
                            "Unexpected token. Did you mean `&rbrace;`?",
                        );
                    }
                    if is_line_break(ch) {
                        if !allow_multiline_jsx_text && saw_non_whitespace {
                            break;
                        }
                        if !saw_non_whitespace {
                            saw_line_break_before_content = true;
                        }
                    } else if !is_whitespace_like(ch) {
                        saw_non_whitespace = true;
                    }
                    self.bump();
                }
                let value = &self.source[start..self.byte_pos];
                self.last_value = Some(JsString::from_utf8(value));
                if saw_line_break_before_content && !saw_non_whitespace {
                    SyntaxKind::JsxTextAllWhiteSpaces
                } else {
                    SyntaxKind::JsxText
                }
            }
        };
        self.finish_token(kind, full_start, start)
    }

    pub fn rescan_jsx_token(&mut self, allow_multiline_jsx_text: bool) -> Token<'a> {
        self.byte_pos = self.last_full_start;
        self.scan_jsx_token_ex(allow_multiline_jsx_text)
    }

    pub fn scan_jsx_identifier(&mut self) -> Token<'a> {
        if self.last_kind == SyntaxKind::Identifier || self.last_kind.is_keyword() {
            let mut value = self
                .last_value
                .clone()
                .unwrap_or_else(|| JsString::from_utf8(self.current_token().text));
            loop {
                if self.peek() == Some('-') {
                    value.push_char('-');
                    self.bump();
                } else if !self.scan_identifier_character(&mut value, is_identifier_part) {
                    break;
                }
            }
            let decoded = value.to_string_lossy();
            self.last_value = Some(value);
            self.last_kind = keyword(&decoded).unwrap_or(SyntaxKind::Identifier);
        }
        self.current_token()
    }

    pub fn scan_jsx_attribute_value(&mut self) -> Token<'a> {
        let full_start = self.byte_pos;
        while self.peek().is_some_and(is_whitespace_like) {
            self.bump();
        }
        let start = self.byte_pos;
        self.last_flags = TokenFlags::NONE;
        self.last_value = None;
        if matches!(self.peek(), Some('\'' | '"')) {
            let Some(quote) = self.bump() else {
                return self.finish_token(SyntaxKind::EndOfFile, full_start, start);
            };
            let value_start = self.byte_pos;
            while self.peek().is_some_and(|ch| ch != quote) {
                self.bump();
            }
            let value = JsString::from_utf8(&self.source[value_start..self.byte_pos]);
            if self.peek() == Some(quote) {
                self.bump();
            } else {
                self.last_flags.insert(TokenFlags::UNTERMINATED);
                self.error(start, self.byte_pos, "Unterminated string literal.");
            }
            self.last_value = Some(value);
            return self.finish_token(SyntaxKind::StringLiteral, full_start, start);
        }
        self.scan();
        self.last_full_start = full_start;
        self.current_token()
    }

    pub fn rescan_jsx_attribute_value(&mut self) -> Token<'a> {
        self.byte_pos = self.last_full_start;
        self.scan_jsx_attribute_value()
    }

    #[must_use]
    pub fn can_follow_jsdoc_at(&self) -> bool {
        self.peek()
            .is_none_or(|ch| is_identifier_start(ch) || is_whitespace_like(ch))
    }

    pub fn scan_jsdoc_comment_text_token(&mut self, in_backticks: bool) -> Token<'a> {
        let full_start = self.byte_pos;
        let start = self.byte_pos;
        while let Some(ch) = self.peek() {
            if is_line_break(ch) || ch == '`' || !in_backticks && ch == '{' {
                break;
            }
            if !in_backticks && ch == '@' {
                let preceded_by_whitespace = self.source[..self.byte_pos]
                    .chars()
                    .next_back()
                    .is_some_and(is_whitespace_like);
                let followed_by_identifier = self.peek_next().is_some_and(is_identifier_start);
                if preceded_by_whitespace && followed_by_identifier {
                    break;
                }
            }
            self.bump();
        }
        if self.byte_pos == start {
            return self.scan_jsdoc_token();
        }
        self.last_flags = TokenFlags::NONE;
        self.last_value = Some(JsString::from_utf8(&self.source[start..self.byte_pos]));
        self.finish_token(SyntaxKind::JsDocCommentTextToken, full_start, start)
    }

    pub fn scan_jsdoc_token(&mut self) -> Token<'a> {
        let full_start = self.byte_pos;
        let start = self.byte_pos;
        self.last_flags = TokenFlags::NONE;
        self.last_value = None;
        let Some(ch) = self.bump() else {
            return self.finish_token(SyntaxKind::EndOfFile, full_start, start);
        };
        let kind = match ch {
            '\t' | '\u{000b}' | '\u{000c}' | ' ' => {
                while self
                    .peek()
                    .is_some_and(|next| is_whitespace_like(next) && !is_line_break(next))
                {
                    self.bump();
                }
                SyntaxKind::WhitespaceTrivia
            }
            '\r' | '\n' | '\u{2028}' | '\u{2029}' => {
                if ch == '\r' && self.peek() == Some('\n') {
                    self.bump();
                }
                self.last_flags.insert(TokenFlags::PRECEDING_LINE_BREAK);
                SyntaxKind::NewLineTrivia
            }
            '@' => SyntaxKind::AtToken,
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
                self.byte_pos = start;
                if self
                    .peek_unicode_escape()
                    .is_some_and(|(escaped, _, _)| is_identifier_start(escaped))
                {
                    return self.scan_jsdoc_identifier(full_start, start);
                }
                self.bump();
                SyntaxKind::Unknown
            }
            _ if is_identifier_start(ch) => {
                self.byte_pos = start;
                return self.scan_jsdoc_identifier(full_start, start);
            }
            _ => SyntaxKind::Unknown,
        };
        self.finish_token(kind, full_start, start)
    }

    fn scan_jsdoc_identifier(&mut self, full_start: usize, start: usize) -> Token<'a> {
        let mut value = JsString::default();
        self.scan_identifier_character(&mut value, is_identifier_start);
        loop {
            if self.peek() == Some('-') {
                value.push_char('-');
                self.bump();
            } else if !self.scan_identifier_character(&mut value, is_identifier_part) {
                break;
            }
        }
        let decoded = value.to_string_lossy();
        self.last_value = Some(value);
        self.finish_token(
            keyword(&decoded).unwrap_or(SyntaxKind::Identifier),
            full_start,
            start,
        )
    }

    fn scan_identifier(&mut self) -> SyntaxKind {
        let mut value = JsString::default();
        self.scan_identifier_character(&mut value, is_identifier_start);
        while self.scan_identifier_character(&mut value, is_identifier_part) {}
        let decoded = value.to_string_lossy();
        self.last_value = Some(value);
        keyword(&decoded).unwrap_or(SyntaxKind::Identifier)
    }

    fn scan_private_identifier(&mut self) -> SyntaxKind {
        let start = self.byte_pos;
        self.bump();
        let mut value = JsString::from_utf8("#");
        if self.scan_identifier_character(&mut value, is_identifier_start) {
            while self.scan_identifier_character(&mut value, is_identifier_part) {}
        } else {
            self.error(
                start,
                self.byte_pos,
                "Invalid character in private identifier.",
            );
        }
        self.last_value = Some(value);
        SyntaxKind::PrivateIdentifier
    }

    fn scan_identifier_character(
        &mut self,
        value: &mut JsString,
        predicate: fn(char) -> bool,
    ) -> bool {
        if let Some(ch) = self.peek()
            && predicate(ch)
        {
            value.push_char(ch);
            self.bump();
            return true;
        }
        let Some((escaped, end, extended)) = self.peek_unicode_escape() else {
            return false;
        };
        if !predicate(escaped) {
            return false;
        }
        self.byte_pos = end;
        self.last_flags.insert(if extended {
            TokenFlags::EXTENDED_UNICODE_ESCAPE
        } else {
            TokenFlags::UNICODE_ESCAPE
        });
        value.push_char(escaped);
        true
    }

    fn peek_unicode_escape(&self) -> Option<(char, usize, bool)> {
        let rest = self.source.get(self.byte_pos..)?;
        if !rest.starts_with("\\u") {
            return None;
        }
        let mut pos = self.byte_pos + 2;
        let extended = self.source.as_bytes().get(pos) == Some(&b'{');
        if extended {
            pos += 1;
            let digits_start = pos;
            while self
                .source
                .as_bytes()
                .get(pos)
                .is_some_and(u8::is_ascii_hexdigit)
            {
                pos += 1;
            }
            let digits = self.source.get(digits_start..pos)?;
            if digits.is_empty()
                || digits.len() > 6
                || self.source.as_bytes().get(pos) != Some(&b'}')
            {
                return None;
            }
            let code_point = u32::from_str_radix(digits, 16).ok()?;
            Some((char::from_u32(code_point)?, pos + 1, true))
        } else {
            let end = pos + 4;
            let digits = self.source.get(pos..end)?;
            if !digits.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                return None;
            }
            let code_point = u32::from_str_radix(digits, 16).ok()?;
            Some((char::from_u32(code_point)?, end, false))
        }
    }

    fn scan_number(&mut self) -> SyntaxKind {
        let start = self.byte_pos;
        if self.starts_with("0x") || self.starts_with("0X") {
            return self.scan_radix_number(16, TokenFlags::HEX_SPECIFIER);
        }
        if self.starts_with("0b") || self.starts_with("0B") {
            return self.scan_radix_number(2, TokenFlags::BINARY_SPECIFIER);
        }
        if self.starts_with("0o") || self.starts_with("0O") {
            return self.scan_radix_number(8, TokenFlags::OCTAL_SPECIFIER);
        }

        let started_with_zero = self.peek() == Some('0');
        let separator_after_leading_zero = self.starts_with("0_");
        let mut normalized = self.scan_digit_sequence(|ch| ch.is_ascii_digit());
        let mut can_be_bigint = true;
        if separator_after_leading_zero {
            self.last_flags
                .insert(TokenFlags::CONTAINS_INVALID_SEPARATOR);
            self.error(
                start + 1,
                start + 2,
                "Numeric separators are not allowed here.",
            );
        }
        if started_with_zero
            && normalized.len() > 1
            && !self.last_flags.contains(TokenFlags::CONTAINS_SEPARATOR)
        {
            if normalized.bytes().all(|byte| matches!(byte, b'0'..=b'7')) {
                self.last_flags.insert(TokenFlags::OCTAL);
                self.error(start, self.byte_pos, "Octal literals are not allowed.");
            } else {
                self.last_flags.insert(TokenFlags::CONTAINS_LEADING_ZERO);
                self.error(
                    start,
                    self.byte_pos,
                    "Decimals with leading zeros are not allowed.",
                );
            }
        }
        if self.peek() == Some('.') {
            can_be_bigint = false;
            normalized.push('.');
            self.bump();
            normalized.push_str(&self.scan_digit_sequence(|ch| ch.is_ascii_digit()));
        }
        if matches!(self.peek(), Some('e' | 'E')) {
            can_be_bigint = false;
            self.last_flags.insert(TokenFlags::SCIENTIFIC);
            let mut preamble = String::new();
            preamble.push(self.bump().expect("checked exponent marker"));
            if matches!(self.peek(), Some('+' | '-')) {
                preamble.push(self.bump().expect("checked exponent sign"));
            }
            let exponent = self.scan_digit_sequence(|ch| ch.is_ascii_digit());
            if exponent.is_empty() {
                self.error(self.byte_pos, self.byte_pos, "Digit expected.");
            } else {
                normalized.push_str(&preamble);
                normalized.push_str(&exponent);
            }
        }

        let kind = if self.peek() == Some('n') && can_be_bigint {
            normalized.push('n');
            self.bump();
            SyntaxKind::BigIntLiteral
        } else if self.peek() == Some('n') {
            self.bump();
            self.error(
                start,
                self.byte_pos,
                if self.last_flags.contains(TokenFlags::SCIENTIFIC) {
                    "A bigint literal cannot use exponential notation."
                } else {
                    "A bigint literal must be an integer."
                },
            );
            SyntaxKind::NumericLiteral
        } else {
            SyntaxKind::NumericLiteral
        };
        self.last_value = Some(JsString::from_utf8(&normalized));
        self.report_identifier_after_number();
        kind
    }

    fn scan_radix_number(&mut self, radix: u32, specifier: TokenFlags) -> SyntaxKind {
        let mut normalized = self.source[self.byte_pos..self.byte_pos + 2].to_owned();
        self.bump_ascii(2);
        self.last_flags.insert(specifier);
        normalized.push_str(&self.scan_digit_sequence(|ch| is_radix_digit(ch, radix)));
        if normalized.len() == 2 {
            let name = match radix {
                2 => "Binary digit expected.",
                8 => "Octal digit expected.",
                _ => "Hexadecimal digit expected.",
            };
            self.error(self.byte_pos, self.byte_pos, name);
        }
        let kind = if self.peek() == Some('n') {
            normalized.push('n');
            self.bump();
            SyntaxKind::BigIntLiteral
        } else {
            SyntaxKind::NumericLiteral
        };
        self.last_value = Some(JsString::from_utf8(&normalized));
        kind
    }

    fn scan_digit_sequence(&mut self, valid: impl Fn(char) -> bool) -> String {
        let mut normalized = String::new();
        let mut saw_digit = false;
        let mut previous_was_separator = false;
        while let Some(ch) = self.peek() {
            if valid(ch) {
                normalized.push(ch);
                saw_digit = true;
                previous_was_separator = false;
                self.bump();
            } else if ch == '_' {
                self.last_flags.insert(TokenFlags::CONTAINS_SEPARATOR);
                if saw_digit && !previous_was_separator {
                    previous_was_separator = true;
                } else {
                    self.last_flags
                        .insert(TokenFlags::CONTAINS_INVALID_SEPARATOR);
                    self.error(
                        self.byte_pos,
                        self.byte_pos + 1,
                        if previous_was_separator {
                            "Multiple consecutive numeric separators are not permitted."
                        } else {
                            "Numeric separators are not allowed here."
                        },
                    );
                }
                self.bump();
            } else {
                break;
            }
        }
        if previous_was_separator {
            self.last_flags
                .insert(TokenFlags::CONTAINS_INVALID_SEPARATOR);
            self.error(
                self.byte_pos - 1,
                self.byte_pos,
                "Numeric separators are not allowed here.",
            );
        }
        normalized
    }

    fn report_identifier_after_number(&mut self) {
        if self.peek().is_some_and(is_identifier_start) {
            self.error(
                self.byte_pos,
                self.byte_pos,
                "An identifier or keyword cannot immediately follow a numeric literal.",
            );
        }
    }

    fn scan_string(&mut self, quote: char) -> SyntaxKind {
        let start = self.byte_pos;
        let mut value = JsString::default();
        if quote == '\'' {
            self.last_flags.insert(TokenFlags::SINGLE_QUOTE);
        }
        self.bump();
        let mut terminated = false;
        while let Some(ch) = self.peek() {
            match ch {
                ch if ch == quote => {
                    self.bump();
                    terminated = true;
                    break;
                }
                '\\' => {
                    self.bump();
                    self.scan_escape_sequence(&mut value);
                }
                '\n' | '\r' => break,
                _ => {
                    value.push_char(ch);
                    self.bump();
                }
            }
        }
        if !terminated {
            self.last_flags.insert(TokenFlags::UNTERMINATED);
            self.error(start, self.byte_pos, "Unterminated string literal.");
        }
        self.last_value = Some(value);
        SyntaxKind::StringLiteral
    }

    fn scan_escape_sequence(&mut self, value: &mut JsString) {
        let Some(ch) = self.bump() else {
            return;
        };
        match ch {
            'b' => value.push_unit(u16::from(b'\x08')),
            't' => value.push_unit(u16::from(b'\t')),
            'n' => value.push_unit(u16::from(b'\n')),
            'v' => value.push_unit(u16::from(b'\x0b')),
            'f' => value.push_unit(u16::from(b'\x0c')),
            'r' => value.push_unit(u16::from(b'\r')),
            '\r' => {
                if self.peek() == Some('\n') {
                    self.bump();
                }
            }
            ch if is_line_break(ch) => {}
            'x' => self.scan_fixed_hex_escape(2, value),
            'u' if self.peek() == Some('{') => {
                self.last_flags.insert(TokenFlags::EXTENDED_UNICODE_ESCAPE);
                self.bump();
                let digits_start = self.byte_pos;
                while self.peek().is_some_and(|digit| digit.is_ascii_hexdigit()) {
                    self.bump();
                }
                let parsed =
                    u32::from_str_radix(&self.source[digits_start..self.byte_pos], 16).ok();
                let closed = self.peek() == Some('}');
                if closed {
                    self.bump();
                }
                if let Some(code_point) = parsed
                    .filter(|point| *point <= 0x10_ffff)
                    .filter(|_| closed)
                {
                    push_code_point(value, code_point);
                } else {
                    self.last_flags.insert(TokenFlags::CONTAINS_INVALID_ESCAPE);
                    self.error(
                        digits_start,
                        self.byte_pos,
                        "Invalid Unicode escape sequence.",
                    );
                }
            }
            'u' => {
                self.last_flags.insert(TokenFlags::UNICODE_ESCAPE);
                self.scan_fixed_hex_escape(4, value);
            }
            '0' => value.push_unit(0),
            other => value.push_char(other),
        }
    }

    fn scan_fixed_hex_escape(&mut self, count: usize, value: &mut JsString) {
        let start = self.byte_pos;
        for _ in 0..count {
            if self.peek().is_some_and(|ch| ch.is_ascii_hexdigit()) {
                self.bump();
            } else {
                self.last_flags.insert(TokenFlags::CONTAINS_INVALID_ESCAPE);
                self.error(start, self.byte_pos, "Hexadecimal digit expected.");
                return;
            }
        }
        let unit = u16::from_str_radix(&self.source[start..self.byte_pos], 16)
            .expect("validated hexadecimal escape fits in u16");
        if count == 2 {
            self.last_flags.insert(TokenFlags::HEX_ESCAPE);
        }
        value.push_unit(unit);
    }

    fn scan_template(&mut self) -> SyntaxKind {
        let start = self.byte_pos;
        let mut value = JsString::default();
        self.bump();
        while let Some(ch) = self.peek() {
            match ch {
                '`' => {
                    self.bump();
                    self.last_value = Some(value);
                    return SyntaxKind::NoSubstitutionTemplateLiteral;
                }
                '$' if self.peek_next() == Some('{') => {
                    self.bump_ascii(2);
                    self.last_value = Some(value);
                    return SyntaxKind::TemplateHead;
                }
                '\\' => {
                    self.bump();
                    self.scan_escape_sequence(&mut value);
                }
                _ => {
                    value.push_char(ch);
                    self.bump();
                }
            }
        }
        self.last_flags.insert(TokenFlags::UNTERMINATED);
        self.error(start, self.byte_pos, "Unterminated template literal.");
        self.last_value = Some(value);
        SyntaxKind::NoSubstitutionTemplateLiteral
    }

    #[allow(clippy::too_many_lines)]
    fn scan_punctuation(&mut self) -> SyntaxKind {
        const PUNCTUATION: &[(&str, SyntaxKind)] = &[
            ("===", SyntaxKind::EqualsEqualsEqualsToken),
            ("!==", SyntaxKind::ExclamationEqualsEqualsToken),
            ("**=", SyntaxKind::AsteriskAsteriskEqualsToken),
            ("<<=", SyntaxKind::LessThanLessThanEqualsToken),
            ("...", SyntaxKind::DotDotDotToken),
            ("&&=", SyntaxKind::AmpersandAmpersandEqualsToken),
            ("||=", SyntaxKind::BarBarEqualsToken),
            ("??=", SyntaxKind::QuestionQuestionEqualsToken),
            ("<=", SyntaxKind::LessThanEqualsToken),
            ("==", SyntaxKind::EqualsEqualsToken),
            ("!=", SyntaxKind::ExclamationEqualsToken),
            ("=>", SyntaxKind::EqualsGreaterThanToken),
            ("++", SyntaxKind::PlusPlusToken),
            ("--", SyntaxKind::MinusMinusToken),
            ("**", SyntaxKind::AsteriskAsteriskToken),
            ("<<", SyntaxKind::LessThanLessThanToken),
            ("&&", SyntaxKind::AmpersandAmpersandToken),
            ("||", SyntaxKind::BarBarToken),
            ("??", SyntaxKind::QuestionQuestionToken),
            ("+=", SyntaxKind::PlusEqualsToken),
            ("-=", SyntaxKind::MinusEqualsToken),
            ("*=", SyntaxKind::AsteriskEqualsToken),
            ("/=", SyntaxKind::SlashEqualsToken),
            ("%=", SyntaxKind::PercentEqualsToken),
            ("&=", SyntaxKind::AmpersandEqualsToken),
            ("|=", SyntaxKind::BarEqualsToken),
            ("^=", SyntaxKind::CaretEqualsToken),
        ];
        if self.language_variant == LanguageVariant::Jsx && self.starts_with("</") {
            self.bump_ascii(2);
            return SyntaxKind::LessThanSlashToken;
        }
        if self.starts_with("?.")
            && !self.source[self.byte_pos + 2..]
                .chars()
                .next()
                .is_some_and(|ch| ch.is_ascii_digit())
        {
            self.bump_ascii(2);
            return SyntaxKind::QuestionDotToken;
        }
        for &(text, kind) in PUNCTUATION {
            if self.starts_with(text) {
                self.bump_ascii(text.len());
                return kind;
            }
        }

        let invalid_start = self.byte_pos;
        let kind = match self.peek() {
            Some('{') => SyntaxKind::OpenBraceToken,
            Some('}') => SyntaxKind::CloseBraceToken,
            Some('(') => SyntaxKind::OpenParenToken,
            Some(')') => SyntaxKind::CloseParenToken,
            Some('[') => SyntaxKind::OpenBracketToken,
            Some(']') => SyntaxKind::CloseBracketToken,
            Some('.') => SyntaxKind::DotToken,
            Some(';') => SyntaxKind::SemicolonToken,
            Some(',') => SyntaxKind::CommaToken,
            Some('<') => SyntaxKind::LessThanToken,
            Some('>') => SyntaxKind::GreaterThanToken,
            Some('+') => SyntaxKind::PlusToken,
            Some('-') => SyntaxKind::MinusToken,
            Some('*') => SyntaxKind::AsteriskToken,
            Some('/') => SyntaxKind::SlashToken,
            Some('%') => SyntaxKind::PercentToken,
            Some('&') => SyntaxKind::AmpersandToken,
            Some('|') => SyntaxKind::BarToken,
            Some('^') => SyntaxKind::CaretToken,
            Some('!') => SyntaxKind::ExclamationToken,
            Some('~') => SyntaxKind::TildeToken,
            Some('?') => SyntaxKind::QuestionToken,
            Some(':') => SyntaxKind::ColonToken,
            Some('@') => SyntaxKind::AtToken,
            Some('#') => SyntaxKind::HashToken,
            Some('=') => SyntaxKind::EqualsToken,
            Some('`') => SyntaxKind::BacktickToken,
            Some(_) => SyntaxKind::Unknown,
            None => return SyntaxKind::EndOfFile,
        };
        self.bump();
        if kind == SyntaxKind::Unknown {
            self.error(invalid_start, self.byte_pos, "Invalid character.");
        }
        kind
    }

    fn peek(&self) -> Option<char> {
        self.source[self.byte_pos..].chars().next()
    }

    fn peek_next(&self) -> Option<char> {
        self.source[self.byte_pos..].chars().nth(1)
    }

    fn starts_with(&self, value: &str) -> bool {
        self.source[self.byte_pos..].starts_with(value)
    }

    fn bump(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.byte_pos += ch.len_utf8();
        Some(ch)
    }

    fn bump_ascii(&mut self, count: usize) {
        debug_assert!(self.source[self.byte_pos..self.byte_pos + count].is_ascii());
        self.byte_pos += count;
    }

    fn is_conflict_marker_at(&self, pos: usize) -> bool {
        const MARKER_LENGTH: usize = 7;
        if pos >= self.source.len()
            || (pos != 0
                && !self.source[..pos]
                    .chars()
                    .next_back()
                    .is_some_and(is_line_break))
        {
            return false;
        }
        let bytes = self.source.as_bytes();
        let Some(&marker) = bytes.get(pos) else {
            return false;
        };
        if !matches!(marker, b'<' | b'|' | b'=' | b'>')
            || bytes.get(pos..pos.saturating_add(MARKER_LENGTH))
                != Some([marker; MARKER_LENGTH].as_slice())
        {
            return false;
        }
        marker == b'=' || bytes.get(pos + MARKER_LENGTH) == Some(&b' ')
    }

    fn scan_conflict_marker(&mut self) {
        const MARKER_LENGTH: usize = 7;
        let start = self.byte_pos;
        let marker = self.source.as_bytes()[start];
        self.error(
            start,
            start.saturating_add(MARKER_LENGTH),
            "Merge conflict marker encountered.",
        );
        if matches!(marker, b'<' | b'>') {
            while self.peek().is_some_and(|ch| !is_line_break(ch)) {
                self.bump();
            }
            return;
        }
        while self.byte_pos < self.source.len() {
            let current = self.source.as_bytes()[self.byte_pos];
            if matches!(current, b'=' | b'>')
                && current != marker
                && self.is_conflict_marker_at(self.byte_pos)
            {
                break;
            }
            self.bump();
        }
    }

    fn error(&mut self, start: usize, end: usize, message: &str) {
        let range = TextRange::new(
            TextPos::new(u32::try_from(start).expect("source exceeds 4 GiB")),
            TextPos::new(u32::try_from(end).expect("source exceeds 4 GiB")),
        );
        self.diagnostics
            .push(scanner_diagnostic_code(message).map_or_else(
                || Diagnostic::new(range, message),
                |code| {
                    let catalog = message_by_code(code).expect("scanner diagnostic code exists");
                    Diagnostic::typescript(
                        range,
                        code,
                        diagnostic_category(catalog.category()),
                        catalog.text(),
                    )
                },
            ));
    }
}

fn scanner_diagnostic_code(message: &str) -> Option<u32> {
    match message {
        "Unterminated string literal." => Some(1002),
        "Unterminated comment." => Some(1010),
        "Digit expected." => Some(1124),
        "Hexadecimal digit expected." => Some(1125),
        "Invalid character." => Some(1127),
        "Merge conflict marker encountered." => Some(1185),
        "Unterminated template literal." => Some(1160),
        "Unterminated regular expression literal." => Some(1161),
        "Binary digit expected." => Some(1177),
        "Octal digit expected." => Some(1178),
        "An identifier or keyword cannot immediately follow a numeric literal." => Some(1351),
        "A bigint literal cannot use exponential notation." => Some(1352),
        "A bigint literal must be an integer." => Some(1353),
        "Decimals with leading zeros are not allowed." => Some(1489),
        "Numeric separators are not allowed here." => Some(6188),
        "Multiple consecutive numeric separators are not permitted." => Some(6189),
        _ => None,
    }
}

const fn diagnostic_category(category: Category) -> DiagnosticCategory {
    match category {
        Category::Warning => DiagnosticCategory::Warning,
        Category::Error => DiagnosticCategory::Error,
        Category::Suggestion => DiagnosticCategory::Suggestion,
        Category::Message => DiagnosticCategory::Message,
    }
}

fn is_identifier_start(ch: char) -> bool {
    matches!(ch, '$' | '_') || unicode_ident::is_xid_start(ch)
}

fn text_pos(byte_pos: usize) -> TextPos {
    TextPos::new(u32::try_from(byte_pos).expect("source exceeds 4 GiB"))
}

fn push_code_point(value: &mut JsString, code_point: u32) {
    if let Ok(unit) = u16::try_from(code_point) {
        value.push_unit(unit);
    } else if let Some(ch) = char::from_u32(code_point) {
        value.push_char(ch);
    }
}

fn is_radix_digit(ch: char, radix: u32) -> bool {
    match radix {
        2 => matches!(ch, '0' | '1'),
        8 => matches!(ch, '0'..='7'),
        16 => ch.is_ascii_hexdigit(),
        _ => false,
    }
}

fn is_identifier_part(ch: char) -> bool {
    matches!(ch, '$' | '\u{200c}' | '\u{200d}') || unicode_ident::is_xid_continue(ch)
}

fn is_line_break(ch: char) -> bool {
    matches!(ch, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

fn is_whitespace_like(ch: char) -> bool {
    ch.is_whitespace()
        || matches!(
            ch,
            '\u{0085}' | '\u{00a0}' | '\u{1680}' | '\u{2000}'
                ..='\u{200b}' | '\u{202f}' | '\u{205f}' | '\u{3000}' | '\u{feff}'
        )
}

#[allow(clippy::too_many_lines)]
fn keyword(text: &str) -> Option<SyntaxKind> {
    Some(match text {
        "break" => SyntaxKind::BreakKeyword,
        "case" => SyntaxKind::CaseKeyword,
        "catch" => SyntaxKind::CatchKeyword,
        "class" => SyntaxKind::ClassKeyword,
        "const" => SyntaxKind::ConstKeyword,
        "continue" => SyntaxKind::ContinueKeyword,
        "debugger" => SyntaxKind::DebuggerKeyword,
        "default" => SyntaxKind::DefaultKeyword,
        "delete" => SyntaxKind::DeleteKeyword,
        "do" => SyntaxKind::DoKeyword,
        "else" => SyntaxKind::ElseKeyword,
        "enum" => SyntaxKind::EnumKeyword,
        "export" => SyntaxKind::ExportKeyword,
        "extends" => SyntaxKind::ExtendsKeyword,
        "false" => SyntaxKind::FalseKeyword,
        "finally" => SyntaxKind::FinallyKeyword,
        "for" => SyntaxKind::ForKeyword,
        "function" => SyntaxKind::FunctionKeyword,
        "if" => SyntaxKind::IfKeyword,
        "import" => SyntaxKind::ImportKeyword,
        "in" => SyntaxKind::InKeyword,
        "instanceof" => SyntaxKind::InstanceOfKeyword,
        "new" => SyntaxKind::NewKeyword,
        "null" => SyntaxKind::NullKeyword,
        "return" => SyntaxKind::ReturnKeyword,
        "super" => SyntaxKind::SuperKeyword,
        "switch" => SyntaxKind::SwitchKeyword,
        "this" => SyntaxKind::ThisKeyword,
        "throw" => SyntaxKind::ThrowKeyword,
        "true" => SyntaxKind::TrueKeyword,
        "try" => SyntaxKind::TryKeyword,
        "typeof" => SyntaxKind::TypeOfKeyword,
        "var" => SyntaxKind::VarKeyword,
        "void" => SyntaxKind::VoidKeyword,
        "while" => SyntaxKind::WhileKeyword,
        "with" => SyntaxKind::WithKeyword,
        "implements" => SyntaxKind::ImplementsKeyword,
        "interface" => SyntaxKind::InterfaceKeyword,
        "let" => SyntaxKind::LetKeyword,
        "package" => SyntaxKind::PackageKeyword,
        "private" => SyntaxKind::PrivateKeyword,
        "protected" => SyntaxKind::ProtectedKeyword,
        "public" => SyntaxKind::PublicKeyword,
        "static" => SyntaxKind::StaticKeyword,
        "yield" => SyntaxKind::YieldKeyword,
        "abstract" => SyntaxKind::AbstractKeyword,
        "accessor" => SyntaxKind::AccessorKeyword,
        "as" => SyntaxKind::AsKeyword,
        "asserts" => SyntaxKind::AssertsKeyword,
        "assert" => SyntaxKind::AssertKeyword,
        "any" => SyntaxKind::AnyKeyword,
        "async" => SyntaxKind::AsyncKeyword,
        "await" => SyntaxKind::AwaitKeyword,
        "boolean" => SyntaxKind::BooleanKeyword,
        "constructor" => SyntaxKind::ConstructorKeyword,
        "declare" => SyntaxKind::DeclareKeyword,
        "get" => SyntaxKind::GetKeyword,
        "immediate" => SyntaxKind::ImmediateKeyword,
        "infer" => SyntaxKind::InferKeyword,
        "intrinsic" => SyntaxKind::IntrinsicKeyword,
        "is" => SyntaxKind::IsKeyword,
        "keyof" => SyntaxKind::KeyOfKeyword,
        "module" => SyntaxKind::ModuleKeyword,
        "namespace" => SyntaxKind::NamespaceKeyword,
        "never" => SyntaxKind::NeverKeyword,
        "out" => SyntaxKind::OutKeyword,
        "readonly" => SyntaxKind::ReadonlyKeyword,
        "require" => SyntaxKind::RequireKeyword,
        "number" => SyntaxKind::NumberKeyword,
        "object" => SyntaxKind::ObjectKeyword,
        "satisfies" => SyntaxKind::SatisfiesKeyword,
        "set" => SyntaxKind::SetKeyword,
        "string" => SyntaxKind::StringKeyword,
        "symbol" => SyntaxKind::SymbolKeyword,
        "type" => SyntaxKind::TypeKeyword,
        "undefined" => SyntaxKind::UndefinedKeyword,
        "unique" => SyntaxKind::UniqueKeyword,
        "unknown" => SyntaxKind::UnknownKeyword,
        "using" => SyntaxKind::UsingKeyword,
        "from" => SyntaxKind::FromKeyword,
        "global" => SyntaxKind::GlobalKeyword,
        "bigint" => SyntaxKind::BigIntKeyword,
        "override" => SyntaxKind::OverrideKeyword,
        "of" => SyntaxKind::OfKeyword,
        "defer" => SyntaxKind::DeferKeyword,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use ts_core::DiagnosticCategory;

    use super::{LanguageVariant, Scanner, SyntaxKind, TokenFlags};

    fn kinds(source: &str) -> Vec<SyntaxKind> {
        let mut scanner = Scanner::new(source);
        let mut result = Vec::new();
        loop {
            let kind = scanner.scan().kind;
            result.push(kind);
            if kind == SyntaxKind::EndOfFile {
                return result;
            }
        }
    }

    #[test]
    fn scans_a_typed_declaration() {
        assert_eq!(
            kinds("const answer: number = 42;"),
            vec![
                SyntaxKind::ConstKeyword,
                SyntaxKind::Identifier,
                SyntaxKind::ColonToken,
                SyntaxKind::NumberKeyword,
                SyntaxKind::EqualsToken,
                SyntaxKind::NumericLiteral,
                SyntaxKind::SemicolonToken,
                SyntaxKind::EndOfFile,
            ]
        );
    }

    #[test]
    fn uses_utf8_source_positions() {
        let mut scanner = Scanner::new("😀 const π = 1");
        assert_eq!(scanner.scan().kind, SyntaxKind::Unknown);
        let token = scanner.scan();
        assert_eq!(token.kind, SyntaxKind::ConstKeyword);
        assert_eq!(token.range.start.get(), 5);
        assert_eq!(token.range.end.get(), 10);
    }

    #[test]
    fn scans_longest_punctuation_first() {
        assert_eq!(
            kinds("a?.b ??= c !== d"),
            vec![
                SyntaxKind::Identifier,
                SyntaxKind::QuestionDotToken,
                SyntaxKind::Identifier,
                SyntaxKind::QuestionQuestionEqualsToken,
                SyntaxKind::Identifier,
                SyntaxKind::ExclamationEqualsEqualsToken,
                SyntaxKind::Identifier,
                SyntaxKind::EndOfFile,
            ]
        );
    }

    #[test]
    fn reports_unterminated_literals() {
        let mut scanner = Scanner::new("'oops");
        assert_eq!(scanner.scan().kind, SyntaxKind::StringLiteral);
        assert_eq!(scanner.diagnostics().len(), 1);
        assert_eq!(scanner.diagnostics()[0].code, Some(1002));
        assert_eq!(scanner.diagnostics()[0].category, DiagnosticCategory::Error);
        assert_eq!(
            scanner.diagnostics()[0].message,
            "Unterminated string literal."
        );
    }

    #[test]
    fn reports_catalog_codes_for_invalid_characters_and_literals() {
        for (source, code, message) in [
            ("😀", 1127, "Invalid character."),
            ("0x", 1125, "Hexadecimal digit expected."),
            ("0b", 1177, "Binary digit expected."),
            ("1e+", 1124, "Digit expected."),
            (
                "1__0",
                6189,
                "Multiple consecutive numeric separators are not permitted.",
            ),
            ("1.0n", 1353, "A bigint literal must be an integer."),
        ] {
            let mut scanner = Scanner::new(source);
            scanner.scan();
            let diagnostic = &scanner.diagnostics()[0];
            assert_eq!(diagnostic.code, Some(code), "source: {source}");
            assert_eq!(diagnostic.category, DiagnosticCategory::Error);
            assert_eq!(diagnostic.message, message);
        }
    }

    #[test]
    fn ordinary_scan_preserves_parser_context() {
        assert_eq!(
            kinds("</ >> >="),
            vec![
                SyntaxKind::LessThanToken,
                SyntaxKind::SlashToken,
                SyntaxKind::GreaterThanToken,
                SyntaxKind::GreaterThanToken,
                SyntaxKind::GreaterThanToken,
                SyntaxKind::EqualsToken,
                SyntaxKind::EndOfFile,
            ]
        );
        assert_eq!(
            kinds("a?.3:0"),
            vec![
                SyntaxKind::Identifier,
                SyntaxKind::QuestionToken,
                SyntaxKind::NumericLiteral,
                SyntaxKind::ColonToken,
                SyntaxKind::NumericLiteral,
                SyntaxKind::EndOfFile,
            ]
        );
    }

    #[test]
    fn handles_ecmascript_trivia_and_identifier_parts() {
        assert_eq!(
            kinds("\u{feff}let a\u{0301} = 1 // comment\u{2028}const b = 2"),
            vec![
                SyntaxKind::LetKeyword,
                SyntaxKind::Identifier,
                SyntaxKind::EqualsToken,
                SyntaxKind::NumericLiteral,
                SyntaxKind::ConstKeyword,
                SyntaxKind::Identifier,
                SyntaxKind::EqualsToken,
                SyntaxKind::NumericLiteral,
                SyntaxKind::EndOfFile,
            ]
        );
    }

    #[test]
    fn rejects_fractional_bigint_suffix() {
        let mut scanner = Scanner::new("1.0n");
        let token = scanner.scan();
        assert_eq!(token.kind, SyntaxKind::NumericLiteral);
        assert_eq!(token.text, "1.0n");
        assert_eq!(scanner.scan().kind, SyntaxKind::EndOfFile);
        assert_eq!(scanner.diagnostics().len(), 1);
    }

    #[test]
    fn mark_and_rewind_restore_scanner_state() {
        let mut scanner = Scanner::new("const value");
        let checkpoint = scanner.mark();
        assert_eq!(scanner.scan().kind, SyntaxKind::ConstKeyword);
        scanner.rewind(checkpoint);
        assert_eq!(scanner.scan().kind, SyntaxKind::ConstKeyword);
    }

    #[test]
    fn records_full_start_and_line_break_trivia() {
        let mut scanner = Scanner::new("const\n  value");
        scanner.scan();
        let token = scanner.scan();
        assert_eq!(token.full_start.get(), 5);
        assert_eq!(token.range.start.get(), 8);
        assert!(token.flags.contains(TokenFlags::PRECEDING_LINE_BREAK));
    }

    #[test]
    fn contextually_rescans_greater_than_and_regex_tokens() {
        let mut scanner = Scanner::new(">>= /a[\\/]b/gi");
        assert_eq!(scanner.scan().kind, SyntaxKind::GreaterThanToken);
        assert_eq!(
            scanner.rescan_greater_than_token().kind,
            SyntaxKind::GreaterThanGreaterThanEqualsToken
        );
        assert_eq!(scanner.scan().kind, SyntaxKind::SlashToken);
        let regex = scanner.rescan_slash_token();
        assert_eq!(regex.kind, SyntaxKind::RegularExpressionLiteral);
        assert_eq!(regex.text, "/a[\\/]b/gi");
    }

    #[test]
    fn string_values_preserve_lone_surrogates() {
        let mut scanner = Scanner::new(r#""🦀\ud7ff\ud800\ud801\uD83E\uDD80""#);
        let token = scanner.scan();
        assert_eq!(token.kind, SyntaxKind::StringLiteral);
        assert_eq!(
            token.value.unwrap().as_units(),
            &[0xd83e, 0xdd80, 0xd7ff, 0xd800, 0xd801, 0xd83e, 0xdd80]
        );
        assert!(scanner.diagnostics().is_empty());
    }

    #[test]
    fn contextually_rescans_template_middle_and_tail() {
        let mut scanner = Scanner::new("`a${x}b${y}c`");
        assert_eq!(scanner.scan().kind, SyntaxKind::TemplateHead);
        assert_eq!(scanner.scan().kind, SyntaxKind::Identifier);
        assert_eq!(scanner.scan().kind, SyntaxKind::CloseBraceToken);
        assert_eq!(
            scanner.rescan_template_token().kind,
            SyntaxKind::TemplateMiddle
        );
        assert_eq!(scanner.scan().kind, SyntaxKind::Identifier);
        assert_eq!(scanner.scan().kind, SyntaxKind::CloseBraceToken);
        let tail = scanner.rescan_template_token();
        assert_eq!(tail.kind, SyntaxKind::TemplateTail);
        assert_eq!(tail.text, "}c`");
        assert_eq!(tail.value.unwrap().as_units(), &[u16::from(b'c')]);
    }

    #[test]
    fn reports_invalid_characters_and_rescans_hash() {
        let mut scanner = Scanner::new("# §");
        let private = scanner.scan();
        assert_eq!(private.kind, SyntaxKind::PrivateIdentifier);
        assert_eq!(scanner.rescan_hash_token().kind, SyntaxKind::HashToken);
        assert_eq!(scanner.scan().kind, SyntaxKind::Unknown);
        assert_eq!(scanner.diagnostics().len(), 2);
    }

    #[test]
    fn decodes_unicode_escapes_in_identifiers_and_keywords() {
        let mut scanner = Scanner::new(r"\u0069f #\u{61} a\u200c");

        let keyword = scanner.scan();
        assert_eq!(keyword.kind, SyntaxKind::IfKeyword);
        assert_eq!(keyword.text, r"\u0069f");
        assert_eq!(keyword.value.unwrap().to_string_lossy(), "if");
        assert!(keyword.flags.contains(TokenFlags::UNICODE_ESCAPE));

        let private = scanner.scan();
        assert_eq!(private.kind, SyntaxKind::PrivateIdentifier);
        assert_eq!(private.value.unwrap().to_string_lossy(), "#a");
        assert!(private.flags.contains(TokenFlags::EXTENDED_UNICODE_ESCAPE));

        let identifier = scanner.scan();
        assert_eq!(identifier.kind, SyntaxKind::Identifier);
        assert_eq!(identifier.value.unwrap().as_units(), &[b'a'.into(), 0x200c]);
        assert!(identifier.flags.contains(TokenFlags::UNICODE_ESCAPE));
        assert!(scanner.diagnostics().is_empty());
    }

    #[test]
    fn scans_unicode_identifier_continue_categories() {
        let name = "才能ソЫⅨर्क";
        let mut scanner = Scanner::new(name);

        let identifier = scanner.scan();
        assert_eq!(identifier.kind, SyntaxKind::Identifier);
        assert_eq!(identifier.text, name);
        assert_eq!(scanner.scan().kind, SyntaxKind::EndOfFile);
        assert!(scanner.diagnostics().is_empty());
    }

    #[test]
    fn records_numeric_values_and_specifier_flags() {
        let mut scanner = Scanner::new("1_000 0xCA_FE 0b1010_0101 0o7_7 1e+2");
        let cases = [
            ("1000", TokenFlags::CONTAINS_SEPARATOR),
            ("0xCAFE", TokenFlags::HEX_SPECIFIER),
            ("0b10100101", TokenFlags::BINARY_SPECIFIER),
            ("0o77", TokenFlags::OCTAL_SPECIFIER),
            ("1e+2", TokenFlags::SCIENTIFIC),
        ];
        for (expected_value, expected_flag) in cases {
            let token = scanner.scan();
            assert_eq!(token.kind, SyntaxKind::NumericLiteral);
            assert_eq!(token.value.unwrap().to_string_lossy(), expected_value);
            assert!(token.flags.contains(expected_flag));
        }
        assert!(scanner.diagnostics().is_empty());
    }

    #[test]
    fn diagnoses_invalid_numeric_spellings() {
        let cases = [
            ("0x", TokenFlags::HEX_SPECIFIER),
            ("0b_1", TokenFlags::CONTAINS_INVALID_SEPARATOR),
            ("0o", TokenFlags::OCTAL_SPECIFIER),
            ("1__0", TokenFlags::CONTAINS_INVALID_SEPARATOR),
            ("1_", TokenFlags::CONTAINS_INVALID_SEPARATOR),
            ("0_1", TokenFlags::CONTAINS_INVALID_SEPARATOR),
            ("1e+", TokenFlags::SCIENTIFIC),
            ("123abc", TokenFlags::NONE),
        ];
        for (source, expected_flag) in cases {
            let mut scanner = Scanner::new(source);
            let token = scanner.scan();
            assert_eq!(token.kind, SyntaxKind::NumericLiteral, "source: {source}");
            assert!(
                token.flags.contains(expected_flag),
                "missing {expected_flag:?} for {source}"
            );
            assert!(!scanner.diagnostics().is_empty(), "source: {source}");
        }
    }

    #[test]
    fn invalid_bigint_suffix_is_consumed_with_numeric_token() {
        for source in ["1.0n", "1e2n"] {
            let mut scanner = Scanner::new(source);
            let token = scanner.scan();
            assert_eq!(token.kind, SyntaxKind::NumericLiteral);
            assert_eq!(token.text, source);
            assert_eq!(scanner.scan().kind, SyntaxKind::EndOfFile);
            assert_eq!(scanner.diagnostics().len(), 1);
        }
    }

    #[test]
    fn emits_trivia_tokens_when_requested() {
        let mut scanner = Scanner::new("  // one\r\n/** @deprecated */value");
        scanner.set_skip_trivia(false);
        assert_eq!(scanner.scan().kind, SyntaxKind::WhitespaceTrivia);
        assert_eq!(scanner.scan().kind, SyntaxKind::SingleLineCommentTrivia);
        let newline = scanner.scan();
        assert_eq!(newline.kind, SyntaxKind::NewLineTrivia);
        assert!(newline.flags.contains(TokenFlags::PRECEDING_LINE_BREAK));
        let jsdoc = scanner.scan();
        assert_eq!(jsdoc.kind, SyntaxKind::MultiLineCommentTrivia);
        assert!(jsdoc.flags.contains(TokenFlags::PRECEDING_JSDOC_COMMENT));
        assert!(
            jsdoc
                .flags
                .contains(TokenFlags::PRECEDING_JSDOC_WITH_DEPRECATED)
        );
        assert_eq!(scanner.scan().kind, SyntaxKind::Identifier);
    }

    #[test]
    fn skips_conflict_markers_and_discarded_merge_sections() {
        let mut scanner = Scanner::new(concat!(
            "left\n",
            "<<<<<<< HEAD\n",
            "head\n",
            "||||||| merged common ancestors\n",
            "base\n",
            "=======\n",
            "branch\n",
            ">>>>>>> topic\n",
            "right",
        ));
        assert_eq!(scanner.scan().text, "left");
        assert_eq!(scanner.scan().text, "head");
        assert_eq!(scanner.scan().text, "right");
        assert_eq!(scanner.scan().kind, SyntaxKind::EndOfFile);
        assert_eq!(scanner.diagnostics().len(), 4);
        assert!(
            scanner
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code == Some(1185))
        );
    }

    #[test]
    fn exposes_conflict_markers_as_trivia_tokens_when_requested() {
        let mut scanner = Scanner::new("<<<<<<< HEAD\nvalue");
        scanner.set_skip_trivia(false);
        let marker = scanner.scan();
        assert_eq!(marker.kind, SyntaxKind::ConflictMarkerTrivia);
        assert_eq!(marker.text, "<<<<<<< HEAD");
        assert_eq!(scanner.scan().kind, SyntaxKind::NewLineTrivia);
        assert_eq!(scanner.scan().text, "value");
    }

    #[test]
    fn reports_conflict_marker_tokens_while_scanning_jsx_text() {
        let mut scanner = Scanner::new("<<<<<<< HEAD");
        scanner.set_language_variant(LanguageVariant::Jsx);
        assert_eq!(
            scanner.scan_jsx_token().kind,
            SyntaxKind::ConflictMarkerTrivia
        );
        assert_eq!(scanner.scan_jsx_token().kind, SyntaxKind::EndOfFile);
    }

    #[test]
    fn resets_text_position_and_token_state() {
        let mut scanner = Scanner::new("let first");
        assert_eq!(scanner.scan().kind, SyntaxKind::LetKeyword);
        scanner.reset_token_state(4);
        assert_eq!(scanner.scan().text, "first");
        scanner.set_text("const second");
        assert_eq!(scanner.scan().kind, SyntaxKind::ConstKeyword);
        scanner.reset();
        assert_eq!(scanner.scan().kind, SyntaxKind::EndOfFile);
    }

    #[test]
    fn scans_jsx_text_identifiers_and_attributes() {
        let mut scanner = Scanner::new("</ custom-element = \"a\\nb\" >hello {name}");
        scanner.set_language_variant(LanguageVariant::Jsx);
        assert_eq!(scanner.scan().kind, SyntaxKind::LessThanSlashToken);
        let identifier = scanner.scan();
        assert_eq!(identifier.kind, SyntaxKind::Identifier);
        let identifier = scanner.scan_jsx_identifier();
        assert_eq!(identifier.text, "custom-element");
        assert_eq!(scanner.scan().kind, SyntaxKind::EqualsToken);
        let attribute = scanner.scan_jsx_attribute_value();
        assert_eq!(attribute.kind, SyntaxKind::StringLiteral);
        assert_eq!(attribute.value.unwrap().to_string_lossy(), "a\\nb");
        assert_eq!(scanner.scan().kind, SyntaxKind::GreaterThanToken);
        let text = scanner.scan_jsx_token();
        assert_eq!(text.kind, SyntaxKind::JsxText);
        assert_eq!(text.text, "hello ");
        assert_eq!(scanner.scan_jsx_token().kind, SyntaxKind::OpenBraceToken);
    }

    #[test]
    fn rescans_jsx_and_classifies_multiline_whitespace() {
        let mut scanner = Scanner::new("\n  <div");
        let ordinary = scanner.scan();
        assert_eq!(ordinary.kind, SyntaxKind::LessThanToken);
        let jsx = scanner.rescan_jsx_token(true);
        assert_eq!(jsx.kind, SyntaxKind::JsxTextAllWhiteSpaces);
        assert_eq!(jsx.text, "\n  ");
        assert_eq!(scanner.scan_jsx_token().kind, SyntaxKind::LessThanToken);
    }

    #[test]
    fn scans_jsdoc_text_tags_and_hyphenated_names() {
        let mut scanner = Scanner::new("summary text @custom-tag {value}\n");
        let text = scanner.scan_jsdoc_comment_text_token(false);
        assert_eq!(text.kind, SyntaxKind::JsDocCommentTextToken);
        assert_eq!(text.text, "summary text ");
        assert_eq!(scanner.scan_jsdoc_token().kind, SyntaxKind::AtToken);
        let tag = scanner.scan_jsdoc_token();
        assert_eq!(tag.kind, SyntaxKind::Identifier);
        assert_eq!(tag.text, "custom-tag");
        assert_eq!(
            scanner.scan_jsdoc_token().kind,
            SyntaxKind::WhitespaceTrivia
        );
        assert_eq!(scanner.scan_jsdoc_token().kind, SyntaxKind::OpenBraceToken);
        assert!(scanner.can_follow_jsdoc_at());
    }

    #[test]
    fn skips_jsdoc_leading_asterisk_after_line_break() {
        let mut scanner = Scanner::new("\n * value");
        scanner.set_skip_jsdoc_leading_asterisks(true);
        let token = scanner.scan();
        assert_eq!(token.kind, SyntaxKind::Identifier);
        assert_eq!(token.text, "value");
        assert!(
            token
                .flags
                .contains(TokenFlags::PRECEDING_JSDOC_LEADING_ASTERISKS)
        );
    }
}
