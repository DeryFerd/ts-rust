//! Port of `scanner/utilities.go`.

use crate::frontend::prelude::*;

use super::scanner_p1::{rune_to_char, text_to_keyword, utf8_decode_rune_in_string};

// Go: scanner/utilities.go:14 tokenIsIdentifierOrKeyword
// PORT: private, as in Go. `checker/utilities_p1.rs` has a pub function with
// the same name, so a pub one here would make the prelude glob ambiguous.
fn token_is_identifier_or_keyword(token: SyntaxKind) -> bool {
    token as u16 >= SyntaxKind::Identifier as u16
}

// Go: scanner/utilities.go:18 IdentifierToKeywordKind
pub fn identifier_to_keyword_kind(node: Node) -> SyntaxKind {
    text_to_keyword(node.text())
}

// Go: scanner/utilities.go:22 GetSourceTextOfNodeFromSourceFile
pub fn get_source_text_of_node_from_source_file(
    source_file: Node,
    node: Node,
    include_trivia: bool,
) -> String {
    get_text_of_node_from_source_text(source_file_text(source_file), node, include_trivia)
}

// Go: scanner/utilities.go:26 isJSDocTypeExpressionOrChild
fn is_js_doc_type_expression_or_child(node: Node) -> bool {
    if is_js_doc_type_expression(node) {
        return true;
    }
    if !node
        .flags()
        .intersects(NodeFlags::JS_DOC | NodeFlags::REPARSED)
    {
        return false;
    }
    let mut current = node;
    while current.is_some() {
        if is_type_node(current) {
            return true;
        }
        current = current.parent();
    }
    false
}

// Go: scanner/utilities.go:41 normalizeJSDocTypeSourceText
fn normalize_js_doc_type_source_text(text: &str) -> String {
    let line_starts = compute_ecma_line_starts(text);
    if line_starts.len() == 1 {
        return strip_leading_js_doc_comment(text).to_string();
    }

    let mut result = String::with_capacity(text.len());
    let new_line = NewLineKind::LF.get_new_line_character();
    for (i, &line_start) in line_starts.iter().enumerate() {
        if i > 0 {
            result.push_str(new_line);
        }
        let mut line_end = text.len();
        if i + 1 < line_starts.len() {
            line_end = line_starts[i + 1] as usize;
        }
        let line = text[line_start as usize..line_end].trim_end_matches(is_line_break);
        result.push_str(strip_leading_js_doc_comment(line));
    }
    result
}

// Go: scanner/utilities.go:64 stripLeadingJSDocComment
fn strip_leading_js_doc_comment(line: &str) -> &str {
    let mut line = line.trim_start_matches(is_white_space_like);
    if let Some(rest) = line.strip_prefix('*') {
        line = rest;
    }
    line.trim_start_matches(is_white_space_like)
}

// Go: scanner/utilities.go:72 GetTextOfNodeFromSourceText
pub fn get_text_of_node_from_source_text(
    source_text: &str,
    node: Node,
    include_trivia: bool,
) -> String {
    if node_is_missing(node) {
        return String::new();
    }
    let mut pos = node.pos();
    if !include_trivia {
        pos = skip_trivia(source_text, pos);
    }
    let mut text: std::borrow::Cow<'_, str> =
        std::borrow::Cow::Borrowed(&source_text[pos as usize..node.end() as usize]);
    if is_js_doc_type_expression_or_child(node) {
        text = std::borrow::Cow::Owned(normalize_js_doc_type_source_text(&text));
    }
    if node
        .flags()
        .intersects(NodeFlags::REPARSER_TRANSFORMED_LITERAL)
    {
        // This is similar to `getLiteralTextOfNode` in the printer, but without the context of an `emitContext` to provide overrides
        if is_string_literal(node) {
            if node.token_flags().intersects(TokenFlags::SINGLE_QUOTE) {
                return format!("'{text}'");
            }
            return format!("\"{text}\"");
        } else if is_identifier(node) {
            return node.text().to_string();
        }
        // Only the above node kinds are currently transformed into one another by the reparser, requiring the textual remapping.
        // (Any reamppings done by emit transforms are handled by `getLiteralTextOfNode` in the printer)
        // Fail on any other kinds.
        // PORT: Go `debug.FailBadSyntaxKind` panics.
        panic!(
            "Unexpected reparser-transformed node kind: {:?}",
            node.kind()
        );
    }
    text.into_owned()
}

// Go: scanner/utilities.go:102 GetTextOfNode
pub fn get_text_of_node(node: Node) -> String {
    get_source_text_of_node_from_source_file(
        get_source_file_of_node(node),
        node,
        false, /*includeTrivia*/
    )
}

// Go: scanner/utilities.go:106 GetTextOfJSDocComment
pub fn get_text_of_js_doc_comment(comment: NodeList) -> String {
    if comment.is_nil() {
        return String::new();
    }
    let mut b = String::new();
    for n in comment.nodes().iter() {
        match n.kind() {
            SyntaxKind::JsDocText => b.push_str(n.text()),
            SyntaxKind::JsDocLink | SyntaxKind::JsDocLinkCode | SyntaxKind::JsDocLinkPlain => {
                b.push_str(&get_text_of_node(n));
            }
            _ => {}
        }
    }
    // PORT: Go `unicode.IsSpace` matches Rust `char::is_whitespace` (White_Space).
    b.trim_end_matches(char::is_whitespace).to_string()
}

// Go: scanner/utilities.go:122 DeclarationNameToString
pub fn declaration_name_to_string(name: Node) -> String {
    if name.is_nil() || name.pos() == name.end() {
        return "(Missing)".to_string();
    }
    get_text_of_node(name)
}

// Go: scanner/utilities.go:129 IsIdentifierText
pub fn is_identifier_text(name: &str, language_variant: LanguageVariant) -> bool {
    let (mut ch, mut size) = utf8_decode_rune_in_string(name, 0);
    if !is_identifier_start(rune_to_char(ch)) {
        return false;
    }
    let mut i = size as usize;
    while i < name.len() {
        (ch, size) = utf8_decode_rune_in_string(name, i);
        if !is_identifier_part_ex(rune_to_char(ch), language_variant) {
            return false;
        }
        i += size as usize;
    }
    true
}

// Go: scanner/utilities.go:144 IsIntrinsicJsxName
pub fn is_intrinsic_jsx_name(name: &str) -> bool {
    let bytes = name.as_bytes();
    !name.is_empty() && (bytes[0] >= b'a' && bytes[0] <= b'z' || name.contains('-'))
}
