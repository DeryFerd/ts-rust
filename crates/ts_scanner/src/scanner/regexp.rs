//! Decimal quantifier bounds from `internal/scanner/regexp.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
//! Keep escape and character-class boundaries when locating each quantifier.

use std::cmp::Ordering;

use super::Scanner;

#[derive(Clone, Copy, Eq, PartialEq)]
enum EscapeContext {
    Atom,
    Class,
    ClassString,
}

pub(super) fn out_of_order_quantifier_bounds(
    source: &str,
    start: usize,
    end: usize,
    unicode_flag: Option<u8>,
) -> Vec<(usize, usize)> {
    let mut scan = QuantifierScan {
        source,
        pos: start,
        end,
        unicode: unicode_flag.is_some(),
        unicode_sets: unicode_flag == Some(b'v'),
        errors: Vec::new(),
    };
    while let Some(ch) = scan.peek() {
        match ch {
            b'\\' => scan.escape(EscapeContext::Atom),
            b'[' => scan.character_class(),
            b'{' => scan.quantifier(),
            b'(' if scan.source[scan.pos..scan.end].starts_with("(?<")
                && !matches!(scan.source.as_bytes().get(scan.pos + 3), Some(b'=' | b'!')) =>
            {
                scan.pos += 3;
                scan.group_name();
            }
            _ => scan.advance(),
        }
    }
    scan.errors
}

struct QuantifierScan<'a> {
    source: &'a str,
    pos: usize,
    end: usize,
    unicode: bool,
    unicode_sets: bool,
    errors: Vec<(usize, usize)>,
}

impl QuantifierScan<'_> {
    fn peek(&self) -> Option<u8> {
        (self.pos < self.end).then(|| self.source.as_bytes()[self.pos])
    }

    fn advance(&mut self) {
        if let Some(ch) = self.source[self.pos..self.end].chars().next() {
            self.pos += ch.len_utf8();
        }
    }

    fn digits(&mut self) {
        while self.peek().is_some_and(|ch| ch.is_ascii_digit()) {
            self.pos += 1;
        }
    }

    fn quantifier(&mut self) {
        self.pos += 1;
        let start = self.pos;
        self.digits();
        let minimum_end = self.pos;
        if self.peek() == Some(b',') {
            self.pos += 1;
            let maximum_start = self.pos;
            self.digits();
            if minimum_end != start
                && maximum_start != self.pos
                && (self.unicode || self.peek() == Some(b'}'))
                && compare_decimal_strings(
                    &self.source[start..minimum_end],
                    &self.source[maximum_start..self.pos],
                ) == Ordering::Greater
            {
                self.errors.push((start, self.pos));
            }
        }
        if self.peek() == Some(b'}') {
            self.pos += 1;
        }
    }

    fn character_class(&mut self) {
        self.pos += 1;
        let mut depth = 1usize;
        while let Some(ch) = self.peek() {
            match ch {
                b'\\' => self.escape(EscapeContext::Class),
                b'[' if self.unicode_sets => {
                    depth += 1;
                    self.pos += 1;
                }
                b']' => {
                    self.pos += 1;
                    depth -= 1;
                    if depth == 0 {
                        return;
                    }
                }
                _ => self.advance(),
            }
        }
    }

    fn escape(&mut self, context: EscapeContext) {
        self.pos += 1;
        let Some(ch) = self.peek() else {
            return;
        };
        self.advance();
        match ch {
            b'u' if self.peek() == Some(b'{') => {
                self.pos += 1;
                while self.peek().is_some_and(|ch| ch.is_ascii_hexdigit()) {
                    self.pos += 1;
                }
                if self.peek() == Some(b'}') {
                    self.pos += 1;
                }
            }
            b'p' | b'P' if context != EscapeContext::ClassString && self.peek() == Some(b'{') => {
                self.pos += 1;
                self.word_characters();
                if self.peek() == Some(b'=') {
                    self.pos += 1;
                    self.word_characters();
                }
                if self.peek() == Some(b'}') {
                    self.pos += 1;
                }
            }
            b'k' if context == EscapeContext::Atom && self.peek() == Some(b'<') => {
                self.pos += 1;
                self.group_name();
            }
            b'q' if context == EscapeContext::Class
                && self.unicode_sets
                && self.peek() == Some(b'{') =>
            {
                self.pos += 1;
                while let Some(ch) = self.peek() {
                    match ch {
                        b'}' => {
                            self.pos += 1;
                            break;
                        }
                        b'\\' => self.escape(EscapeContext::ClassString),
                        _ => self.advance(),
                    }
                }
            }
            _ => {}
        }
    }

    fn group_name(&mut self) {
        let mut name = Scanner::new(&self.source[self.pos..self.end]);
        name.scan_identifier();
        self.pos += name.byte_pos;
        if self.peek() == Some(b'>') {
            self.pos += 1;
        }
    }

    fn word_characters(&mut self) {
        while self
            .peek()
            .is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == b'_')
        {
            self.pos += 1;
        }
    }
}

fn compare_decimal_strings(left: &str, right: &str) -> Ordering {
    let left = left.trim_start_matches('0');
    let right = right.trim_start_matches('0');
    let left = if left.is_empty() { "0" } else { left };
    let right = if right.is_empty() { "0" } else { right };
    left.len().cmp(&right.len()).then_with(|| left.cmp(right))
}

#[cfg(test)]
mod tests {
    use super::Scanner;
    use ts_ast::SyntaxKind;

    fn errors(source: &str) -> Vec<String> {
        let mut scanner = Scanner::new(source);
        scanner.scan();
        assert_eq!(
            scanner.rescan_slash_token_with_quantifier_checks().kind,
            SyntaxKind::RegularExpressionLiteral
        );
        scanner
            .diagnostics()
            .iter()
            .map(|diagnostic| {
                assert_eq!(diagnostic.code, Some(1_506));
                source[diagnostic.range.start.get() as usize..diagnostic.range.end.get() as usize]
                    .to_owned()
            })
            .collect()
    }

    #[test]
    fn quantifier_bounds_preserve_large_and_zero_padded_decimals() {
        for bounds in [
            "8,7",
            "0008,0007",
            "1,000",
            "9223372036854775808,9223372036854775807",
        ] {
            assert_eq!(errors(&format!("/a{{{bounds}}}/")), [bounds]);
        }
        let bounds = format!("1{},{}", "0".repeat(100), "9".repeat(100));
        assert_eq!(errors(&format!("/a{{{bounds}}}/")), [bounds]);
        assert_eq!(errors("/a{8,7}b{4,2}/"), ["8,7", "4,2"]);
    }

    #[test]
    fn quantifier_bounds_accept_increasing_equal_and_open_ranges() {
        for source in [
            "/a{7,8}/",
            "/a{8,8}/",
            "/a{000,0}/",
            "/a{0,000}/",
            "/a{0007,08}/",
            "/a{8,}/",
            "/a{8}/",
            "/a{,8}/",
            "/a{9223372036854775807,9223372036854775808}/",
            "/a{9223372036854775808,9223372036854775808}/",
        ] {
            assert!(errors(source).is_empty(), "{source}");
        }
    }

    #[test]
    fn quantifier_bounds_keep_escapes_and_character_classes_separate() {
        for source in [
            r"/a\{8,7\}/",
            r"/[{8,7}]/",
            r"/[[{8,7}]]/v",
            r"/[\q{\{8,7\}}]/v",
            r"/\u{8,7}/",
            r"/\u{8,7}/u",
            r"/\p{8,7}/",
            r"/\p{8,7}/u",
        ] {
            assert!(errors(source).is_empty(), "{source}");
        }
        for source in [
            r"/\\{8,7}/",
            r"/[a]{8,7}/",
            r"/[\q{\]}]{8,7}/v",
            r"/(?<\u{61}>x){8,7}/u",
            r"/\k<\u{61}>{8,7}/u",
            "/={8,7}/",
        ] {
            assert_eq!(errors(source), ["8,7"], "{source}");
        }
    }

    #[test]
    fn quantifier_bounds_follow_unicode_closing_brace_rules() {
        assert!(errors("/a{8,7x}/").is_empty());
        assert_eq!(errors("/a{8,7x}/u"), ["8,7"]);
        assert_eq!(errors("/a{8,7/v"), ["8,7"]);
        assert_eq!(errors("/[[a]{8,7}]/uv"), ["8,7"]);
        assert!(errors("/[[a]{8,7}]/vu").is_empty());
    }

    #[test]
    fn quantifier_checks_preserve_tokens_and_utf8_byte_ranges() {
        let source = "/\u{1f600}a{8,7}/g; rest";
        let mut parser = Scanner::new(source);
        let mut checker = Scanner::new(source);
        assert_eq!(parser.scan(), checker.scan());
        let expected = parser.rescan_slash_token();
        assert_eq!(
            checker.rescan_slash_token_with_quantifier_checks(),
            expected
        );
        assert_eq!(
            checker.rescan_slash_token_with_quantifier_checks(),
            expected
        );
        assert!(parser.diagnostics().is_empty());
        assert_eq!(checker.diagnostics().len(), 1);
        assert_eq!(checker.diagnostics()[0].range.start.get(), 7);
        assert_eq!(checker.diagnostics()[0].range.end.get(), 10);
        assert_eq!(parser.scan(), checker.scan());
        assert_eq!(parser.scan(), checker.scan());
    }
}
