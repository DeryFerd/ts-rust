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
// PORT: Go scanner/utilities.go:72 GetTextOfNodeFromSourceText and its
// helpers are in `crate::scanner_util` only (one copy, which cuts a node
// inside a char as Go does).
pub fn get_source_text_of_node_from_source_file(
    source_file: Node,
    node: Node,
    include_trivia: bool,
) -> String {
    crate::scanner_util::get_text_of_node_from_source_text(
        &source_file_text(source_file),
        node,
        include_trivia,
    )
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
