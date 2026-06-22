use ts_ast::SyntaxKind;
use ts_core::{Diagnostic, JsString, TextPos, TextRange};

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
pub struct TokenFlags(u16);

impl TokenFlags {
    pub const NONE: Self = Self(0);
    pub const PRECEDING_LINE_BREAK: Self = Self(1 << 0);

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
    diagnostics: Vec<Diagnostic>,
    last_full_start: usize,
    last_start: usize,
    last_kind: SyntaxKind,
    last_flags: TokenFlags,
    last_value: Option<JsString>,
}

impl<'a> Scanner<'a> {
    #[must_use]
    pub const fn new(source: &'a str) -> Self {
        Self {
            source,
            byte_pos: 0,
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
        let flags = self.skip_trivia();
        let start_byte = self.byte_pos;
        self.last_value = None;
        let Some(ch) = self.peek() else {
            return self.finish_token(SyntaxKind::EndOfFile, full_start, start_byte, flags);
        };

        let kind = if is_identifier_start(ch) {
            self.scan_identifier()
        } else if ch.is_ascii_digit() {
            self.scan_number()
        } else {
            match ch {
                '\'' | '"' => self.scan_string(ch),
                '`' => self.scan_template(),
                '#' => {
                    self.bump();
                    if !self.peek().is_some_and(is_identifier_start) {
                        self.error(
                            start_byte,
                            self.byte_pos,
                            "Invalid character in private identifier.",
                        );
                    }
                    while self.peek().is_some_and(is_identifier_part) {
                        self.bump();
                    }
                    SyntaxKind::PrivateIdentifier
                }
                '.' if self.peek_next().is_some_and(|next| next.is_ascii_digit()) => {
                    self.scan_number()
                }
                _ => self.scan_punctuation(),
            }
        };

        self.finish_token(kind, full_start, start_byte, flags)
    }

    fn finish_token(
        &mut self,
        kind: SyntaxKind,
        full_start: usize,
        start_byte: usize,
        flags: TokenFlags,
    ) -> Token<'a> {
        self.last_full_start = full_start;
        self.last_start = start_byte;
        self.last_kind = kind;
        self.last_flags = flags;
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
            } else if self.byte_pos == 0 && self.starts_with("#!") {
                while self.peek().is_some_and(|ch| !is_line_break(ch)) {
                    self.bump();
                }
            }
            if before == self.byte_pos {
                break;
            }
        }
        flags
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

    fn scan_identifier(&mut self) -> SyntaxKind {
        let start = self.byte_pos;
        self.bump();
        while self.peek().is_some_and(is_identifier_part) {
            self.bump();
        }
        let text = &self.source[start..self.byte_pos];
        self.last_value = Some(JsString::from_utf8(text));
        keyword(text).unwrap_or(SyntaxKind::Identifier)
    }

    fn scan_number(&mut self) -> SyntaxKind {
        let mut can_be_bigint = true;
        if self.starts_with("0x") || self.starts_with("0X") {
            self.bump_ascii(2);
            self.scan_digits(|ch| ch.is_ascii_hexdigit());
        } else if self.starts_with("0b") || self.starts_with("0B") {
            self.bump_ascii(2);
            self.scan_digits(|ch| matches!(ch, '0' | '1'));
        } else if self.starts_with("0o") || self.starts_with("0O") {
            self.bump_ascii(2);
            self.scan_digits(|ch| matches!(ch, '0'..='7'));
        } else {
            self.scan_digits(|ch| ch.is_ascii_digit());
            if self.peek() == Some('.') {
                can_be_bigint = false;
                self.bump();
                self.scan_digits(|ch| ch.is_ascii_digit());
            }
            if matches!(self.peek(), Some('e' | 'E')) {
                can_be_bigint = false;
                self.bump();
                if matches!(self.peek(), Some('+' | '-')) {
                    self.bump();
                }
                self.scan_digits(|ch| ch.is_ascii_digit());
            }
        }
        if self.peek() == Some('n') && can_be_bigint {
            self.bump();
            SyntaxKind::BigIntLiteral
        } else {
            if self.peek() == Some('n') {
                self.error(
                    self.byte_pos,
                    self.byte_pos + 1,
                    "A bigint literal must be an integer.",
                );
            }
            SyntaxKind::NumericLiteral
        }
    }

    fn scan_digits(&mut self, valid: impl Fn(char) -> bool) {
        while self.peek().is_some_and(|ch| valid(ch) || ch == '_') {
            self.bump();
        }
    }

    fn scan_string(&mut self, quote: char) -> SyntaxKind {
        let start = self.byte_pos;
        let mut value = JsString::default();
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
                self.bump();
                let digits_start = self.byte_pos;
                while self.peek().is_some_and(|digit| digit.is_ascii_hexdigit()) {
                    self.bump();
                }
                let parsed =
                    u32::from_str_radix(&self.source[digits_start..self.byte_pos], 16).ok();
                if self.peek() == Some('}') {
                    self.bump();
                }
                if let Some(code_point) = parsed.and_then(char::from_u32) {
                    value.push_char(code_point);
                } else {
                    self.error(
                        digits_start,
                        self.byte_pos,
                        "Invalid Unicode escape sequence.",
                    );
                }
            }
            'u' => self.scan_fixed_hex_escape(4, value),
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
                self.error(start, self.byte_pos, "Hexadecimal digit expected.");
                return;
            }
        }
        let unit = u16::from_str_radix(&self.source[start..self.byte_pos], 16)
            .expect("validated hexadecimal escape fits in u16");
        value.push_unit(unit);
    }

    fn scan_template(&mut self) -> SyntaxKind {
        let start = self.byte_pos;
        self.bump();
        while let Some(ch) = self.peek() {
            match ch {
                '`' => {
                    self.bump();
                    return SyntaxKind::NoSubstitutionTemplateLiteral;
                }
                '$' if self.peek_next() == Some('{') => {
                    self.bump_ascii(2);
                    return SyntaxKind::TemplateHead;
                }
                '\\' => {
                    self.bump();
                    if self.peek().is_some() {
                        self.bump();
                    }
                }
                _ => {
                    self.bump();
                }
            }
        }
        self.error(start, self.byte_pos, "Unterminated template literal.");
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

    fn error(&mut self, start: usize, end: usize, message: &str) {
        self.diagnostics.push(Diagnostic::new(
            TextRange::new(
                TextPos::new(u32::try_from(start).expect("source exceeds 4 GiB")),
                TextPos::new(u32::try_from(end).expect("source exceeds 4 GiB")),
            ),
            message,
        ));
    }
}

fn is_identifier_start(ch: char) -> bool {
    matches!(ch, '$' | '_') || ch.is_alphabetic()
}

fn text_pos(byte_pos: usize) -> TextPos {
    TextPos::new(u32::try_from(byte_pos).expect("source exceeds 4 GiB"))
}

fn is_identifier_part(ch: char) -> bool {
    is_identifier_start(ch)
        || ch.is_alphanumeric()
        || is_combining_mark(ch)
        || matches!(ch, '\u{200c}' | '\u{200d}')
}

fn is_combining_mark(ch: char) -> bool {
    matches!(
        ch,
        '\u{0300}'..='\u{036f}'
            | '\u{1ab0}'..='\u{1aff}'
            | '\u{1dc0}'..='\u{1dff}'
            | '\u{20d0}'..='\u{20ff}'
            | '\u{fe20}'..='\u{fe2f}'
    )
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
    use super::{Scanner, SyntaxKind, TokenFlags};

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
        assert_eq!(scanner.scan().kind, SyntaxKind::NumericLiteral);
        assert_eq!(scanner.scan().kind, SyntaxKind::Identifier);
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
}
