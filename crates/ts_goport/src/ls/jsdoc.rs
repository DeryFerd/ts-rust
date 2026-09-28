use crate::ls::prelude::*;

// Port of Go `internal/ls/jsdoc.go` (tsgo#4424): the symbol documentation
// comment and JSDoc tags that the API returns.

// Go: ls/jsdoc.go:17 JSDocTagInfo
/// JSDocTagInfo mirrors Strada's `JSDocTagInfo`, but renders the tag's text as a
/// plain string instead of `SymbolDisplayPart[]`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct JSDocTagInfo {
    pub name: String,
    pub text: String,
}

impl LanguageService {
    // Go: ls/jsdoc.go:27 GetSymbolDocumentationComment
    /// GetSymbolDocumentationComment renders a symbol's documentation comment as plain text.
    /// It backs the API's Symbol.getDocumentationComment and mirrors Strada's
    /// getJsDocCommentsFromDeclarations: comments are gathered from each unique declaration,
    /// deduplicated, and joined with line breaks. Like Strada, it does not resolve aliases —
    /// consumers resolve aliases themselves (via getAliasedSymbol) and re-query if desired.
    pub fn get_symbol_documentation_comment(&self, c: &mut Checker, symbol: SymbolId) -> String {
        if symbol.is_nil() {
            return String::new();
        }
        let mut parts: Vec<String> = Vec::new();
        let mut seen: FxHashSet<Node> = FxHashSet::default();
        let declarations = c.sym(symbol).declarations.clone();
        for decl in declarations.iter().copied() {
            if decl.is_nil() {
                continue;
            }
            if !seen.insert(decl) {
                continue;
            }
            let doc = self.get_documentation_from_declaration(
                c,
                symbol,
                decl,
                decl,
                &lsproto::MarkupKind::PLAIN_TEXT,
                true, /*commentOnly*/
            );
            if !doc.is_empty() && !parts.contains(&doc) {
                parts.push(doc);
            }
        }
        parts.join("\n")
    }

    // Go: ls/jsdoc.go:48 GetSymbolJSDocTags
    /// GetSymbolJSDocTags collects a symbol's JSDoc tags. It backs the API's Symbol.getJsDocTags
    /// and mirrors Strada's getJsDocTagsFromDeclarations, except each tag's text is rendered as a
    /// plain string rather than SymbolDisplayPart[]. Tags with no text have an empty Text field.
    // PORT: Go reads `symbol.Declarations` with no checker. `c` is the checker
    // whose arena holds `symbol`.
    pub fn get_symbol_js_doc_tags(&self, c: &Checker, symbol: SymbolId) -> Vec<JSDocTagInfo> {
        if symbol.is_nil() {
            return Vec::new();
        }
        let mut infos: Vec<JSDocTagInfo> = Vec::new();
        let mut seen: FxHashSet<Node> = FxHashSet::default();
        for decl in c.sym(symbol).declarations.iter().copied() {
            if decl.is_nil() {
                continue;
            }
            if !seen.insert(decl) {
                continue;
            }
            let tags = declaration_js_doc_tags(decl);
            // Skip comments containing @typedef/@callback since they're not associated with a
            // particular declaration, unless they also carry @param/@return (treated as local docs).
            let has_typedef = tags.iter().any(|t| {
                t.kind() == SyntaxKind::JsDocTypedefTag || t.kind() == SyntaxKind::JsDocCallbackTag
            });
            let has_param_or_return = tags.iter().any(|t| {
                t.kind() == SyntaxKind::JsDocParameterTag || t.kind() == SyntaxKind::JsDocReturnTag
            });
            if has_typedef && !has_param_or_return {
                continue;
            }
            for tag in tags {
                infos.push(JSDocTagInfo {
                    name: tag.tag_name().text().to_string(),
                    text: get_js_doc_tag_text(tag),
                });
            }
        }
        infos
    }
}

// Go: ls/jsdoc.go:83 declarationJSDocTags
/// declarationJSDocTags returns the JSDoc tags associated with a declaration, walking the
/// JSDoc comment location chain like the checker's getAllJSDocTags.
fn declaration_js_doc_tags(node: Node) -> Vec<Node> {
    if !node.flags().intersects(NodeFlags::JS_DOC) {
        let mut current = node;
        while current.is_some() {
            let jsdocs = current.js_doc(Node::NIL);
            if !jsdocs.is_empty() {
                let last_js_doc = jsdocs.get(jsdocs.len() - 1);
                let tags = last_js_doc.tags();
                if !tags.is_nil() {
                    return tags.nodes().to_vec();
                }
            }
            current = get_next_js_doc_comment_location(current);
        }
    }
    Vec::new()
}

// Go: ls/jsdoc.go:101 getJSDocTagText
/// getJSDocTagText renders the text of a single JSDoc tag as a plain string, mirroring
/// Strada's getCommentDisplayParts collapsed from SymbolDisplayPart[] to a string.
fn get_js_doc_tag_text(tag: Node) -> String {
    let comment = get_text_of_js_doc_comment(tag.comment_list());
    let add_comment = |s: String| -> String {
        if comment.is_empty() {
            return s;
        }
        s + " " + &comment
    };
    match tag.kind() {
        SyntaxKind::JsDocThrowsTag => {
            let te = tag.type_expression();
            if te.is_some() {
                return add_comment(get_text_of_node(te));
            }
            comment
        }
        SyntaxKind::JsDocImplementsTag => add_comment(get_text_of_node(tag.class_name())),
        SyntaxKind::JsDocAugmentsTag => add_comment(get_text_of_node(tag.class_name())),
        SyntaxKind::JsDocTemplateTag => {
            let mut b = String::new();
            let constraint = tag.constraint();
            if constraint.is_some() {
                b.push_str(&get_text_of_node(constraint));
            }
            let type_parameters = tag.type_parameter_list();
            if type_parameters.is_some() {
                for (i, tp) in type_parameters.nodes().iter().enumerate() {
                    if i == 0 && !b.is_empty() {
                        b.push(' ');
                    }
                    if i != 0 {
                        b.push_str(", ");
                    }
                    b.push_str(&get_text_of_node(tp));
                }
            }
            if !comment.is_empty() {
                if !b.is_empty() {
                    b.push(' ');
                }
                b.push_str(&comment);
            }
            b
        }
        SyntaxKind::JsDocTypeTag => add_comment(get_text_of_node(tag.type_expression())),
        SyntaxKind::JsDocSatisfiesTag => add_comment(get_text_of_node(tag.type_expression())),
        SyntaxKind::JsDocSeeTag => {
            let ne = tag.name_expression();
            if ne.is_some() {
                return add_comment(get_text_of_node(ne));
            }
            comment
        }
        SyntaxKind::JsDocParameterTag | SyntaxKind::JsDocPropertyTag => {
            let name = tag.name();
            if name.is_some() {
                return add_comment(get_text_of_node(name));
            }
            comment
        }
        _ => comment,
    }
}
