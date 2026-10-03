use crate::format::prelude::*;

use crate::flags_macros::go_enum;
use crate::frontend::core_textchange::TextChange;
use crate::frontend::scanner::{Scanner, new_scanner};

// Go: format/scanner.go:12 TextRangeWithKind
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TextRangeWithKind {
    pub loc: TextRange,
    pub kind: SyntaxKind,
}

// PORT: the Go zero value (Loc 0..0, KindUnknown). crate::astdata::SyntaxKind has no
// Default.
impl Default for TextRangeWithKind {
    fn default() -> Self {
        new_text_range_with_kind(0, 0, SyntaxKind::Unknown)
    }
}

// Go: format/scanner.go:17 NewTextRangeWithKind
pub fn new_text_range_with_kind(pos: i32, end: i32, kind: SyntaxKind) -> TextRangeWithKind {
    TextRangeWithKind {
        loc: TextRange::new(pos, end),
        kind,
    }
}

// Go: format/scanner.go:24 tokenInfo
#[derive(Clone, Debug, Default)]
pub struct TokenInfo {
    pub leading_trivia: Vec<TextRangeWithKind>,
    pub token: TextRangeWithKind,
    pub trailing_trivia: Vec<TextRangeWithKind>,
}

// Go: format/scanner.go:30 formattingScanner
// PORT: Go `s *scanner.Scanner` is owned here (the literal
// frontend::scanner::Scanner port, which has the JSX rescans).
pub struct FormattingScanner<'t> {
    pub s: Scanner<'t>,
    pub start_pos: i32,
    pub end_pos: i32,
    pub saved_pos: i32,
    pub has_last_token_info: bool,
    pub last_token_info: TokenInfo,
    pub last_scan_action: ScanAction,
    pub leading_trivia: Vec<TextRangeWithKind>,
    pub trailing_trivia: Vec<TextRangeWithKind>,
    pub was_new_line: bool,
}

// Go: format/scanner.go:43 newFormattingScanner
// PORT: Go passes `*formatSpanWorker` and the worker keeps a pointer to the
// formatting scanner. Here the worker is moved in, `execute` moves the
// formatting scanner into the worker, and the worker's edits are returned.
pub fn new_formatting_scanner<'t>(
    text: &'t str,
    language_variant: LanguageVariant,
    start_pos: i32,
    end_pos: i32,
    mut worker: FormatSpanWorker<'t>,
) -> Vec<TextChange> {
    let mut scan = new_scanner();
    scan.set_skip_trivia(false);
    scan.set_language_variant(language_variant);
    scan.set_text(text);
    scan.reset_token_state(start_pos);

    let fmt_scn = FormattingScanner {
        s: scan,
        start_pos,
        end_pos,
        saved_pos: 0,
        has_last_token_info: false,
        last_token_info: TokenInfo::default(),
        last_scan_action: ScanAction::ACTION_SCAN,
        leading_trivia: Vec::new(),
        trailing_trivia: Vec::new(),
        was_new_line: true,
    };

    let res = worker.execute(fmt_scn);

    // PORT: Go `fmtScn` and `scan` are the pointers the worker holds.
    let fmt_scn = worker.formatting_scanner();
    fmt_scn.has_last_token_info = false;
    fmt_scn.s.reset();

    res
}

impl<'t> FormattingScanner<'t> {
    // Go: format/scanner.go:65 advance
    pub fn advance(&mut self) {
        self.has_last_token_info = false;
        let is_started = self.s.token_full_start() != self.start_pos;

        if is_started {
            self.was_new_line = !self.trailing_trivia.is_empty()
                && self.trailing_trivia.last().expect("non-empty").kind
                    == SyntaxKind::NewLineTrivia;
        } else {
            self.s.scan();
        }

        self.leading_trivia = Vec::new();
        self.trailing_trivia = Vec::new();

        let mut pos = self.s.token_full_start();

        // Read leading trivia and token
        while pos < self.end_pos {
            let t = self.s.token();
            if !is_trivia(t) {
                break;
            }

            // consume leading trivia
            self.s.scan();
            let item = new_text_range_with_kind(pos, self.s.token_full_start(), t);

            pos = self.s.token_full_start();

            self.leading_trivia.push(item);
        }

        self.saved_pos = self.s.token_full_start();
    }
}

// Go: format/scanner.go:99 shouldRescanGreaterThanToken
pub fn should_rescan_greater_than_token(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::GreaterThanEqualsToken
            | SyntaxKind::GreaterThanGreaterThanEqualsToken
            | SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken
            | SyntaxKind::GreaterThanGreaterThanGreaterThanToken
            | SyntaxKind::GreaterThanGreaterThanToken
    )
}

// Go: format/scanner.go:111 shouldRescanJsxIdentifier
pub fn should_rescan_jsx_identifier(node: Node) -> bool {
    if node.parent().is_some() {
        match node.parent().kind() {
            SyntaxKind::JsxAttribute
            | SyntaxKind::JsxOpeningElement
            | SyntaxKind::JsxClosingElement
            | SyntaxKind::JsxSelfClosingElement
            | SyntaxKind::JsxNamespacedName => {
                // May parse an identifier like `module-layout`; that will be scanned as a keyword at first, but we should parse the whole thing to get an identifier.
                return is_keyword_kind(node.kind()) || node.kind() == SyntaxKind::Identifier;
            }
            SyntaxKind::PropertyAccessExpression => {
                // The leftmost name of a dotted JSX tag name (e.g. `a-b` in `<a-b.c>`) may contain hyphens, so rescan it as a JSX identifier.
                return (is_keyword_kind(node.kind()) || node.kind() == SyntaxKind::Identifier)
                    && is_leftmost_jsx_tag_name(node);
            }
            _ => {}
        }
    }
    false
}

// Go: format/scanner.go:129 isLeftmostJsxTagName
fn is_leftmost_jsx_tag_name(node: Node) -> bool {
    find_ancestor_or_quit(node, |n| {
        if n.parent().is_nil() {
            FindAncestorResult::FIND_ANCESTOR_QUIT
        } else if is_jsx_tag_name(n) {
            FindAncestorResult::FIND_ANCESTOR_TRUE
        } else if is_property_access_expression(n.parent()) && n.parent().expression() == n {
            FindAncestorResult::FIND_ANCESTOR_FALSE
        } else {
            FindAncestorResult::FIND_ANCESTOR_QUIT
        }
    })
    .is_some()
}

impl<'t> FormattingScanner<'t> {
    // Go: format/scanner.go:144 shouldRescanJsxText
    pub fn should_rescan_jsx_text(&self, node: Node) -> bool {
        if is_jsx_text(node) {
            return true;
        }
        if !is_jsx_element(node) || !self.has_last_token_info {
            return false;
        }

        self.last_token_info.token.kind == SyntaxKind::JsxText
    }
}

// Go: format/scanner.go:155 shouldRescanSlashToken
pub fn should_rescan_slash_token(container: Node) -> bool {
    container.kind() == SyntaxKind::RegularExpressionLiteral
}

// Go: format/scanner.go:159 shouldRescanTemplateToken
pub fn should_rescan_template_token(container: Node) -> bool {
    container.kind() == SyntaxKind::TemplateMiddle || container.kind() == SyntaxKind::TemplateTail
}

// Go: format/scanner.go:164 shouldRescanJsxAttributeValue
pub fn should_rescan_jsx_attribute_value(node: Node) -> bool {
    node.parent().is_some()
        && is_jsx_attribute(node.parent())
        && node.parent().initializer() == node
}

// Go: format/scanner.go:168 startsWithSlashToken
pub fn starts_with_slash_token(t: SyntaxKind) -> bool {
    t == SyntaxKind::SlashToken || t == SyntaxKind::SlashEqualsToken
}

// Go: format/scanner.go:172 scanAction
go_enum!(ScanAction, i32 {
    ACTION_SCAN = 0; // actionScan
    ACTION_RESCAN_GREATER_THAN_TOKEN = 1; // actionRescanGreaterThanToken
    ACTION_RESCAN_SLASH_TOKEN = 2; // actionRescanSlashToken
    ACTION_RESCAN_TEMPLATE_TOKEN = 3; // actionRescanTemplateToken
    ACTION_RESCAN_JSX_IDENTIFIER = 4; // actionRescanJsxIdentifier
    ACTION_RESCAN_JSX_TEXT = 5; // actionRescanJsxText
    ACTION_RESCAN_JSX_ATTRIBUTE_VALUE = 6; // actionRescanJsxAttributeValue
});

// Go: format/scanner.go:184 fixTokenKind
pub fn fix_token_kind(mut token_info: TokenInfo, container: Node) -> TokenInfo {
    if is_token_kind(container.kind()) && token_info.token.kind != container.kind() {
        token_info.token.kind = container.kind();
    }
    token_info
}

impl<'t> FormattingScanner<'t> {
    // Go: format/scanner.go:191 readTokenInfo
    // PORT: Go returns the struct by value (the trivia slices are shared);
    // this returns a clone.
    pub fn read_token_info(&mut self, n: Node) -> TokenInfo {
        crate::go_assert!(self.is_on_token());

        // normally scanner returns the smallest available token
        // check the kind of context node to determine if scanner should have more greedy behavior and consume more text.

        let expected_scan_action = if should_rescan_greater_than_token(n) {
            ScanAction::ACTION_RESCAN_GREATER_THAN_TOKEN
        } else if should_rescan_slash_token(n) {
            ScanAction::ACTION_RESCAN_SLASH_TOKEN
        } else if should_rescan_template_token(n) {
            ScanAction::ACTION_RESCAN_TEMPLATE_TOKEN
        } else if should_rescan_jsx_identifier(n) {
            ScanAction::ACTION_RESCAN_JSX_IDENTIFIER
        } else if self.should_rescan_jsx_text(n) {
            ScanAction::ACTION_RESCAN_JSX_TEXT
        } else if should_rescan_jsx_attribute_value(n) {
            ScanAction::ACTION_RESCAN_JSX_ATTRIBUTE_VALUE
        } else {
            ScanAction::ACTION_SCAN
        };

        if self.has_last_token_info && expected_scan_action == self.last_scan_action {
            // readTokenInfo was called before with the same expected scan action.
            // No need to re-scan text, return existing 'lastTokenInfo'
            // it is ok to call fixTokenKind here since it does not affect
            // what portion of text is consumed. In contrast rescanning can change it,
            // i.e. for '>=' when originally scanner eats just one character
            // and rescanning forces it to consume more.
            self.last_token_info = fix_token_kind(std::mem::take(&mut self.last_token_info), n);
            return self.last_token_info.clone();
        }

        if self.s.token_full_start() != self.saved_pos {
            // readTokenInfo was called before but scan action differs - rescan text
            self.s.reset_token_state(self.saved_pos);
            self.s.scan();
        }

        let mut current_token = self.get_next_token(n, expected_scan_action);

        let token =
            new_text_range_with_kind(self.s.token_full_start(), self.s.token_end(), current_token);

        // consume trailing trivia
        self.trailing_trivia = Vec::new();
        while self.s.token_full_start() < self.end_pos {
            current_token = self.s.scan();
            if !is_trivia(current_token) {
                break;
            }
            let trivia = new_text_range_with_kind(
                self.s.token_full_start(),
                self.s.token_end(),
                current_token,
            );

            self.trailing_trivia.push(trivia);

            if current_token == SyntaxKind::NewLineTrivia {
                // move past new line
                self.s.scan();
                break;
            }
        }

        self.has_last_token_info = true;
        self.last_token_info = TokenInfo {
            leading_trivia: self.leading_trivia.clone(),
            token,
            trailing_trivia: self.trailing_trivia.clone(),
        };
        self.last_token_info = fix_token_kind(std::mem::take(&mut self.last_token_info), n);

        self.last_token_info.clone()
    }

    // Go: format/scanner.go:272 getNextToken
    pub fn get_next_token(&mut self, n: Node, expected_scan_action: ScanAction) -> SyntaxKind {
        let token = self.s.token();
        self.last_scan_action = ScanAction::ACTION_SCAN;
        match expected_scan_action {
            ScanAction::ACTION_RESCAN_GREATER_THAN_TOKEN => {
                if token == SyntaxKind::GreaterThanToken {
                    self.last_scan_action = ScanAction::ACTION_RESCAN_GREATER_THAN_TOKEN;
                    let new_token = self.s.re_scan_greater_than_token();
                    crate::go_assert!(n.kind() == new_token);
                    return new_token;
                }
            }
            ScanAction::ACTION_RESCAN_SLASH_TOKEN => {
                if starts_with_slash_token(token) {
                    self.last_scan_action = ScanAction::ACTION_RESCAN_SLASH_TOKEN;
                    // PORT: Go `ReScanSlashToken()` with no argument reports no errors.
                    let new_token = self.s.re_scan_slash_token(false);
                    crate::go_assert!(n.kind() == new_token);
                    return new_token;
                }
            }
            ScanAction::ACTION_RESCAN_TEMPLATE_TOKEN => {
                if token == SyntaxKind::CloseBraceToken {
                    self.last_scan_action = ScanAction::ACTION_RESCAN_TEMPLATE_TOKEN;
                    return self.s.re_scan_template_token(false /*isTaggedTemplate*/);
                }
            }
            ScanAction::ACTION_RESCAN_JSX_IDENTIFIER => {
                self.last_scan_action = ScanAction::ACTION_RESCAN_JSX_IDENTIFIER;
                return self.s.scan_jsx_identifier();
            }
            ScanAction::ACTION_RESCAN_JSX_TEXT => {
                self.last_scan_action = ScanAction::ACTION_RESCAN_JSX_TEXT;
                return self.s.re_scan_jsx_token(false /*allowMultilineJsxText*/);
            }
            ScanAction::ACTION_RESCAN_JSX_ATTRIBUTE_VALUE => {
                self.last_scan_action = ScanAction::ACTION_RESCAN_JSX_ATTRIBUTE_VALUE;
                return self.s.re_scan_jsx_attribute_value();
            }
            ScanAction::ACTION_SCAN => {
                // no rescan needed; the token was already produced by the normal scan
            }
            _ => crate::gostd::debug::assert_never(
                &expected_scan_action.0.to_string(),
                Some("unhandled scan action kind"),
            ),
        }
        token
    }

    // Go: format/scanner.go:312 readEOFTokenRange
    pub fn read_eof_token_range(&self) -> TextRangeWithKind {
        crate::go_assert!(self.is_on_eof());
        new_text_range_with_kind(
            self.s.token_full_start(),
            self.s.token_end(),
            SyntaxKind::EndOfFile,
        )
    }

    // Go: format/scanner.go:321 isOnToken
    pub fn is_on_token(&self) -> bool {
        let mut current = self.s.token();
        if self.has_last_token_info {
            current = self.last_token_info.token.kind;
        }
        current != SyntaxKind::EndOfFile && !is_trivia(current)
    }

    // Go: format/scanner.go:329 isOnEOF
    pub fn is_on_eof(&self) -> bool {
        let mut current = self.s.token();
        if self.has_last_token_info {
            current = self.last_token_info.token.kind;
        }
        current == SyntaxKind::EndOfFile
    }

    // Go: format/scanner.go:337 skipToEndOf
    pub fn skip_to_end_of(&mut self, r: &TextRange) {
        self.s.reset_token_state(r.end());
        self.saved_pos = self.s.token_full_start();
        self.last_scan_action = ScanAction::ACTION_SCAN;
        self.has_last_token_info = false;
        self.was_new_line = false;
        self.leading_trivia = Vec::new();
        self.trailing_trivia = Vec::new();
    }

    // Go: format/scanner.go:347 skipToStartOf
    pub fn skip_to_start_of(&mut self, r: &TextRange) {
        self.s.reset_token_state(r.pos());
        self.saved_pos = self.s.token_full_start();
        self.last_scan_action = ScanAction::ACTION_SCAN;
        self.has_last_token_info = false;
        self.was_new_line = false;
        self.leading_trivia = Vec::new();
        self.trailing_trivia = Vec::new();
    }

    // Go: format/scanner.go:357 getCurrentLeadingTrivia
    pub fn get_current_leading_trivia(&self) -> &[TextRangeWithKind] {
        &self.leading_trivia
    }

    // Go: format/scanner.go:361 lastTrailingTriviaWasNewLine
    pub fn last_trailing_trivia_was_new_line(&self) -> bool {
        self.was_new_line
    }

    // Go: format/scanner.go:365 getTokenFullStart
    pub fn get_token_full_start(&self) -> i32 {
        if self.has_last_token_info {
            return self.last_token_info.token.loc.pos();
        }
        self.s.token_full_start()
    }

    // Go: format/scanner.go:372 getStartPos
    pub fn get_start_pos(&self) -> i32 {
        // TODO: redundant?
        self.get_token_full_start()
    }
}
