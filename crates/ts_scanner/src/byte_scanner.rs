use ts_ast::SyntaxKind;
use ts_core::{Diagnostic, JsString, SourceText, TextPos, TextRange};

use crate::{LanguageVariant, Scanner, Token, TokenFlags};

/// A token whose spelling is a lossless slice of the original source bytes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ByteToken<'a> {
    pub kind: SyntaxKind,
    pub full_start: TextPos,
    pub range: TextRange,
    pub text: &'a [u8],
    pub flags: TokenFlags,
    pub value: Option<JsString>,
}

/// Scanner entry point for source files that may contain invalid UTF-8.
///
/// Valid text follows the regular scanner exactly. Invalid bytes are scanned
/// through `SourceText`'s same-length sentinel view, while token spellings and
/// offsets continue to reference the original bytes.
pub struct ByteScanner<'a> {
    source: &'a SourceText,
    inner: Scanner<'a>,
    diagnostics: Vec<Diagnostic>,
    copied_inner_diagnostics: usize,
}

impl<'a> ByteScanner<'a> {
    #[must_use]
    pub fn new(source: &'a SourceText) -> Self {
        let diagnostics = source
            .invalid_byte_ranges()
            .iter()
            .map(|range| {
                Diagnostic::new(
                    TextRange::new(text_pos(range.start), text_pos(range.end)),
                    "Invalid UTF-8 byte sequence.",
                )
            })
            .collect();
        Self {
            source,
            inner: Scanner::new(source.as_scannable_str()),
            diagnostics,
            copied_inner_diagnostics: 0,
        }
    }

    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub fn set_skip_trivia(&mut self, skip: bool) {
        self.inner.set_skip_trivia(skip);
    }

    pub fn set_language_variant(&mut self, variant: LanguageVariant) {
        self.inner.set_language_variant(variant);
    }

    pub fn scan(&mut self) -> ByteToken<'a> {
        let token = self.inner.scan();
        let token = self.map_token(token);
        self.sync_diagnostics();
        token
    }

    pub fn rescan_greater_than_token(&mut self) -> ByteToken<'a> {
        let token = self.inner.rescan_greater_than_token();
        let token = self.map_token(token);
        self.sync_diagnostics();
        token
    }

    pub fn rescan_less_than_token(&mut self) -> ByteToken<'a> {
        let token = self.inner.rescan_less_than_token();
        let token = self.map_token(token);
        self.sync_diagnostics();
        token
    }

    pub fn rescan_slash_token(&mut self) -> ByteToken<'a> {
        let token = self.inner.rescan_slash_token();
        let token = self.map_token(token);
        self.sync_diagnostics();
        token
    }

    pub fn rescan_template_token(&mut self) -> ByteToken<'a> {
        let token = self.inner.rescan_template_token();
        let token = self.map_token(token);
        self.sync_diagnostics();
        token
    }

    fn map_token(&self, token: Token<'_>) -> ByteToken<'a> {
        let start = usize::try_from(token.range.start.get()).unwrap();
        let end = usize::try_from(token.range.end.get()).unwrap();
        ByteToken {
            kind: token.kind,
            full_start: token.full_start,
            range: token.range,
            text: &self.source.as_bytes()[start..end],
            flags: token.flags,
            value: token.value,
        }
    }

    fn sync_diagnostics(&mut self) {
        for diagnostic in &self.inner.diagnostics()[self.copied_inner_diagnostics..] {
            if !self
                .diagnostics
                .iter()
                .any(|existing| existing.range == diagnostic.range)
            {
                self.diagnostics.push(diagnostic.clone());
            }
        }
        self.copied_inner_diagnostics = self.inner.diagnostics().len();
    }
}

fn text_pos(position: usize) -> TextPos {
    TextPos::new(u32::try_from(position).unwrap_or(u32::MAX))
}

#[cfg(test)]
mod tests {
    use ts_ast::SyntaxKind;
    use ts_core::SourceText;

    use super::ByteScanner;

    #[test]
    fn invalid_bytes_are_lossless_and_do_not_panic() {
        let source = SourceText::from_bytes(vec![b'a', b' ', 0x80, b' ', b'b']);
        let mut scanner = ByteScanner::new(&source);
        assert_eq!(scanner.scan().kind, SyntaxKind::Identifier);
        let invalid = scanner.scan();
        assert_eq!(invalid.kind, SyntaxKind::Unknown);
        assert_eq!(invalid.text, &[0x80]);
        assert_eq!(invalid.range.start.get(), 2);
        assert_eq!(invalid.range.end.get(), 3);
        assert_eq!(scanner.scan().kind, SyntaxKind::Identifier);
        assert_eq!(scanner.diagnostics().len(), 1);
    }

    #[test]
    fn invalid_byte_inside_regex_is_preserved_during_rescan() {
        let source = SourceText::from_bytes(vec![b'/', 0x80, b'/', b'u']);
        let mut scanner = ByteScanner::new(&source);
        assert_eq!(scanner.scan().kind, SyntaxKind::SlashToken);
        let regex = scanner.rescan_slash_token();
        assert_eq!(regex.kind, SyntaxKind::RegularExpressionLiteral);
        assert_eq!(regex.text, &[b'/', 0x80, b'/', b'u']);
        assert_eq!(regex.range.start.get(), 0);
        assert_eq!(regex.range.end.get(), 4);
        assert_eq!(scanner.diagnostics().len(), 1);
    }

    #[test]
    fn scans_the_upstream_invalid_utf8_regex_fixture_bytes() {
        let source = SourceText::from_bytes(b"// @target: esnext\n/\x80/u\n".to_vec());
        let mut scanner = ByteScanner::new(&source);
        let slash = scanner.scan();
        assert_eq!(slash.kind, SyntaxKind::SlashToken);
        assert_eq!(slash.range.start.get(), 19);
        let regex = scanner.rescan_slash_token();
        assert_eq!(regex.kind, SyntaxKind::RegularExpressionLiteral);
        assert_eq!(regex.text, b"/\x80/u");
        assert_eq!(regex.range.end.get(), 23);
        assert_eq!(scanner.diagnostics()[0].range.start.get(), 20);
    }
}
