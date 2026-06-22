use std::collections::BTreeMap;

use crate::{ConfigDiagnostic, JsonNumber, JsonValue, ParseResult, diagnostic};

/// Parses the JSON-with-comments syntax accepted by tsconfig files.
#[must_use]
pub fn parse_jsonc(file_name: &str, source: &str) -> ParseResult<JsonValue> {
    let mut parser = Parser::new(file_name, source);
    let value = if parser.skip_trivia() && parser.is_eof() {
        Some(JsonValue::Object(BTreeMap::new()))
    } else {
        parser.parse_value()
    };
    if value.is_some() && parser.skip_trivia() && !parser.is_eof() {
        parser.error(1127, std::iter::empty());
    }
    ParseResult {
        value: if parser.diagnostics.is_empty() {
            value
        } else {
            None
        },
        diagnostics: parser.diagnostics,
    }
}

struct Parser<'a> {
    file_name: &'a str,
    source: &'a str,
    position: usize,
    diagnostics: Vec<ConfigDiagnostic>,
}

impl<'a> Parser<'a> {
    const fn new(file_name: &'a str, source: &'a str) -> Self {
        Self {
            file_name,
            source,
            position: 0,
            diagnostics: Vec::new(),
        }
    }

    fn parse_value(&mut self) -> Option<JsonValue> {
        if !self.skip_trivia() {
            return None;
        }
        match self.peek()? {
            b'{' => self.parse_object(),
            b'[' => self.parse_array(),
            b'"' => self.parse_string().map(JsonValue::String),
            b't' => self.parse_keyword("true", JsonValue::Bool(true)),
            b'f' => self.parse_keyword("false", JsonValue::Bool(false)),
            b'n' => self.parse_keyword("null", JsonValue::Null),
            b'-' | b'0'..=b'9' => self.parse_number().map(JsonValue::Number),
            _ => {
                self.error(1127, std::iter::empty());
                None
            }
        }
    }

    fn parse_object(&mut self) -> Option<JsonValue> {
        self.position += 1;
        let mut properties = BTreeMap::new();
        if !self.skip_trivia() {
            return None;
        }
        if self.consume(b'}') {
            return Some(JsonValue::Object(properties));
        }

        loop {
            if self.peek() != Some(b'"') {
                self.error(1136, std::iter::empty());
                return None;
            }
            let key = self.parse_string()?;
            if !self.skip_trivia() {
                return None;
            }
            if !self.consume(b':') {
                self.expected(":");
                return None;
            }
            let value = self.parse_value()?;
            properties.insert(key, value);

            if !self.skip_trivia() {
                return None;
            }
            if self.consume(b'}') {
                break;
            }
            if !self.consume(b',') {
                self.expected(",");
                return None;
            }
            if !self.skip_trivia() {
                return None;
            }
            if self.consume(b'}') {
                break;
            }
        }
        Some(JsonValue::Object(properties))
    }

    fn parse_array(&mut self) -> Option<JsonValue> {
        self.position += 1;
        let mut values = Vec::new();
        if !self.skip_trivia() {
            return None;
        }
        if self.consume(b']') {
            return Some(JsonValue::Array(values));
        }

        loop {
            values.push(self.parse_value()?);
            if !self.skip_trivia() {
                return None;
            }
            if self.consume(b']') {
                break;
            }
            if !self.consume(b',') {
                self.expected(",");
                return None;
            }
            if !self.skip_trivia() {
                return None;
            }
            if self.consume(b']') {
                break;
            }
        }
        Some(JsonValue::Array(values))
    }

    fn parse_string(&mut self) -> Option<String> {
        let start = self.position;
        self.position += 1;
        let mut result = String::new();
        while let Some(byte) = self.peek() {
            match byte {
                b'"' => {
                    self.position += 1;
                    return Some(result);
                }
                b'\\' => {
                    self.position += 1;
                    let Some(escape) = self.peek() else {
                        self.error_at(1002, start, std::iter::empty());
                        return None;
                    };
                    self.position += 1;
                    match escape {
                        b'"' => result.push('"'),
                        b'\\' => result.push('\\'),
                        b'/' => result.push('/'),
                        b'b' => result.push('\u{0008}'),
                        b'f' => result.push('\u{000c}'),
                        b'n' => result.push('\n'),
                        b'r' => result.push('\r'),
                        b't' => result.push('\t'),
                        b'u' => self.parse_unicode_escape(&mut result)?,
                        _ => {
                            self.error_at(1127, self.position - 1, std::iter::empty());
                            return None;
                        }
                    }
                }
                0..=0x1f => {
                    self.error(1127, std::iter::empty());
                    return None;
                }
                _ => {
                    let character = self.source[self.position..].chars().next()?;
                    result.push(character);
                    self.position += character.len_utf8();
                }
            }
        }
        self.error_at(1002, start, std::iter::empty());
        None
    }

    fn parse_unicode_escape(&mut self, result: &mut String) -> Option<()> {
        let first = self.read_hex_quad()?;
        if (0xd800..=0xdbff).contains(&first) && self.source[self.position..].starts_with("\\u") {
            let checkpoint = self.position;
            self.position += 2;
            let second = self.read_hex_quad()?;
            if (0xdc00..=0xdfff).contains(&second) {
                let scalar =
                    0x1_0000 + ((u32::from(first) - 0xd800) << 10) + u32::from(second) - 0xdc00;
                result.push(char::from_u32(scalar).unwrap_or(char::REPLACEMENT_CHARACTER));
                return Some(());
            }
            self.position = checkpoint;
        }
        result.push(char::from_u32(u32::from(first)).unwrap_or(char::REPLACEMENT_CHARACTER));
        Some(())
    }

    fn read_hex_quad(&mut self) -> Option<u16> {
        let Some(end) = self.position.checked_add(4) else {
            self.error(1127, std::iter::empty());
            return None;
        };
        let Some(digits) = self.source.get(self.position..end) else {
            self.error(1127, std::iter::empty());
            return None;
        };
        if !digits.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            self.error(1127, std::iter::empty());
            return None;
        }
        self.position = end;
        u16::from_str_radix(digits, 16).ok()
    }

    fn parse_number(&mut self) -> Option<JsonNumber> {
        let start = self.position;
        self.consume(b'-');
        match self.peek()? {
            b'0' => self.position += 1,
            b'1'..=b'9' => {
                self.position += 1;
                while self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
                    self.position += 1;
                }
            }
            _ => {
                self.error(1127, std::iter::empty());
                return None;
            }
        }
        if self.consume(b'.') {
            if !self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
                self.error(1127, std::iter::empty());
                return None;
            }
            while self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
                self.position += 1;
            }
        }
        if self.peek().is_some_and(|byte| matches!(byte, b'e' | b'E')) {
            self.position += 1;
            if self.peek().is_some_and(|byte| matches!(byte, b'+' | b'-')) {
                self.position += 1;
            }
            if !self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
                self.error(1127, std::iter::empty());
                return None;
            }
            while self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
                self.position += 1;
            }
        }
        Some(JsonNumber::new(
            self.source[start..self.position].to_owned(),
        ))
    }

    fn parse_keyword(&mut self, keyword: &str, value: JsonValue) -> Option<JsonValue> {
        if self.source[self.position..].starts_with(keyword) {
            self.position += keyword.len();
            Some(value)
        } else {
            self.error(1127, std::iter::empty());
            None
        }
    }

    fn skip_trivia(&mut self) -> bool {
        loop {
            if self.position == 0 && self.source.starts_with('\u{feff}') {
                self.position += '\u{feff}'.len_utf8();
            }
            while self.peek().is_some_and(|byte| byte.is_ascii_whitespace()) {
                self.position += 1;
            }
            if self.source[self.position..].starts_with("//") {
                self.position += 2;
                while self
                    .peek()
                    .is_some_and(|byte| !matches!(byte, b'\r' | b'\n'))
                {
                    self.position += 1;
                }
                continue;
            }
            if self.source[self.position..].starts_with("/*") {
                let comment_start = self.position;
                self.position += 2;
                if let Some(end) = self.source[self.position..].find("*/") {
                    self.position += end + 2;
                    continue;
                }
                self.position = self.source.len();
                self.error_at(1010, comment_start, std::iter::empty());
                return false;
            }
            return true;
        }
    }

    fn expected(&mut self, token: &str) {
        self.error(1005, [token.to_owned()]);
    }

    fn error(&mut self, code: u32, arguments: impl IntoIterator<Item = String>) {
        self.error_at(code, self.position, arguments);
    }

    fn error_at(
        &mut self,
        code: u32,
        position: usize,
        arguments: impl IntoIterator<Item = String>,
    ) {
        if self.diagnostics.is_empty() {
            self.diagnostics
                .push(diagnostic(self.file_name, position, code, arguments));
        }
    }

    fn peek(&self) -> Option<u8> {
        self.source.as_bytes().get(self.position).copied()
    }

    fn consume(&mut self, byte: u8) -> bool {
        if self.peek() == Some(byte) {
            self.position += 1;
            true
        } else {
            false
        }
    }

    fn is_eof(&self) -> bool {
        self.position == self.source.len()
    }
}
