use crate::ls::prelude::*;

// Port of Go `internal/ls/jsdoc.go` (tsgo#4424): the symbol documentation
// comment and JSDoc tags that the API returns, and the JSDoc lookup helpers
// that tsgo#4893 moved here from `hover.go`.

// Go: ls/jsdoc.go:17 JSDocTagInfo
/// JSDocTagInfo mirrors Strada's `JSDocTagInfo`, but renders the tag's text as a
/// plain string instead of `SymbolDisplayPart[]`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct JSDocTagInfo {
    pub name: String,
    pub text: String,
}

// Go: ls/jsdoc.go:27 GetSymbolDocumentationComment
/// GetSymbolDocumentationComment renders a symbol's documentation comment as plain text.
/// It backs the API's Symbol.getDocumentationComment and mirrors Strada's
/// getJsDocCommentsFromDeclarations: comments are gathered from each unique declaration,
/// deduplicated, and joined with line breaks. Like Strada, it does not resolve aliases —
/// consumers resolve aliases themselves (via getAliasedSymbol) and re-query if desired.
pub fn get_symbol_documentation_comment(c: &mut Checker, symbol: SymbolId) -> String {
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
        let doc = get_documentation_from_declaration(
            &no_mapped_location,
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

// Go: ls/jsdoc.go:50 GetSymbolJSDocTags
/// GetSymbolJSDocTags collects a symbol's JSDoc tags. It backs the API's Symbol.getJsDocTags
/// and mirrors Strada's getJsDocTagsFromDeclarations, except each tag's text is rendered as a
/// plain string rather than SymbolDisplayPart[]. Tags with no text have an empty Text field.
// PORT: Go reads `symbol.Declarations` with no checker. `c` is the checker
// whose arena holds `symbol`.
pub fn get_symbol_js_doc_tags(c: &Checker, symbol: SymbolId) -> Vec<JSDocTagInfo> {
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

// Go: ls/jsdoc.go:163 getJSDoc
pub fn get_js_doc(node: Node) -> Node {
    node.js_doc(Node::NIL).last().unwrap_or(Node::NIL)
}

// Go: ls/jsdoc.go:167 getJSDocOrTag
pub fn get_js_doc_or_tag(
    c: &mut Checker,
    node: Node,
    seen_symbols: &mut FxHashSet<SymbolId>,
) -> Node {
    if node.is_nil() {
        return Node::NIL;
    }
    let jsdoc = get_js_doc(node);
    if jsdoc.is_some() {
        return jsdoc;
    }
    if is_parameter_declaration(node) {
        let name = node.name();
        if is_binding_pattern(name) {
            // For binding patterns, match JSDoc @param tags by position rather than by name
            return get_js_doc_parameter_tag_by_position(c, node);
        }
        return get_matching_js_doc_tag(
            c,
            node.parent(),
            name.text(),
            is_matching_parameter_tag,
            seen_symbols,
        );
    } else if is_type_parameter_declaration(node) {
        return get_matching_js_doc_tag(
            c,
            node.parent(),
            node.name().text(),
            is_matching_template_tag,
            seen_symbols,
        );
    } else if is_variable_declaration(node)
        && is_variable_declaration_list(node.parent())
        && node
            .parent()
            .declarations()
            .nodes()
            .first()
            .unwrap_or(Node::NIL)
            == node
    {
        return get_js_doc_or_tag(c, node.parent().parent(), seen_symbols);
    } else if (is_function_expression_or_arrow_function(node) || is_class_expression(node))
        && (is_variable_declaration(node.parent())
            || is_property_declaration(node.parent())
            || is_property_assignment(node.parent()))
        && node.parent().initializer() == node
    {
        return get_js_doc_or_tag(c, node.parent(), seen_symbols);
    } else if is_binding_element(node) && is_object_binding_pattern(node.parent()) {
        let name = node.property_name_or_name();
        if is_identifier(name) {
            let object_type = c.get_type_at_location(node.parent());
            if object_type.is_some() {
                let prop = c.get_property_of_type_exported(object_type, name.text());
                if prop.is_some() {
                    let declarations = c.sym(prop).declarations.clone();
                    for d in declarations {
                        let jsdoc = get_js_doc(d);
                        if jsdoc.is_some() {
                            return jsdoc;
                        }
                    }
                }
            }
        }
    }
    let symbol = node.symbol();
    if symbol.is_some() && node.parent().is_some() {
        if is_function_declaration(node)
            || is_method_declaration(node)
            || is_method_signature_declaration(node)
            || is_constructor_declaration(node)
            || is_construct_signature_declaration(node)
        {
            let first_signature = c
                .sym(symbol)
                .declarations
                .iter()
                .copied()
                .find(|&d| is_function_like(d))
                .unwrap_or(Node::NIL);
            if first_signature.is_some() && node != first_signature {
                let js_doc = get_js_doc_or_tag(c, first_signature, seen_symbols);
                if js_doc.is_some() {
                    return js_doc;
                }
            }
        }
        if is_class_or_interface_like(node.parent()) {
            let is_static = has_static_modifier(node);
            let class_type = c.get_declared_type_of_symbol_exported(node.parent().symbol());
            let symbol_name = c.sym(symbol).name.as_str();
            if is_static {
                // For static members, use the checker's base constructor type resolution.
                // This correctly handles intersection constructor types from mixins
                // (e.g., typeof MixinClass & T) by preserving the full intersection.
                let base_constructor_type =
                    c.get_base_constructor_type_of_class_exported(class_type);
                let static_base_type = c.get_apparent_type_exported(base_constructor_type);
                let prop = c.get_property_of_type_exported(static_base_type, symbol_name);
                if prop.is_some() {
                    let prop_value_declaration = c.sym(prop).value_declaration;
                    if prop_value_declaration.is_some() && seen_symbols.insert(prop) {
                        let js_doc = get_js_doc_or_tag(c, prop_value_declaration, seen_symbols);
                        if js_doc.is_some() {
                            return js_doc;
                        }
                    }
                }
            } else {
                for base_type in c.get_base_types_exported(class_type) {
                    let prop = c.get_property_of_type_exported(base_type, symbol_name);
                    if prop.is_some() {
                        let prop_value_declaration = c.sym(prop).value_declaration;
                        if prop_value_declaration.is_some() && seen_symbols.insert(prop) {
                            let js_doc = get_js_doc_or_tag(c, prop_value_declaration, seen_symbols);
                            if js_doc.is_some() {
                                return js_doc;
                            }
                        }
                    }
                }
            }
        }
    }
    Node::NIL
}

// Go: ls/jsdoc.go:238 getMatchingJSDocTag
pub fn get_matching_js_doc_tag(
    c: &mut Checker,
    node: Node,
    name: &str,
    match_: fn(Node, &str) -> bool,
    seen_symbols: &mut FxHashSet<SymbolId>,
) -> Node {
    let jsdoc = get_js_doc_or_tag(c, node, seen_symbols);
    if jsdoc.is_some() && jsdoc.kind() == SyntaxKind::JsDoc {
        let tags = jsdoc.tags();
        if tags.is_some() {
            for tag in tags.nodes() {
                if match_(tag, name) {
                    return tag;
                }
            }
        }
    }
    Node::NIL
}

// Go: ls/jsdoc.go:253 getJSDocParameterTagByPosition
// getJSDocParameterTagByPosition finds a JSDoc @param tag for a binding pattern parameter by position.
// Since binding patterns don't have a simple name, we match the @param tag at the same index as the parameter.
pub fn get_js_doc_parameter_tag_by_position(c: &mut Checker, param: Node) -> Node {
    let parent = param.parent();
    if parent.is_nil() {
        return Node::NIL;
    }

    // Find the parameter's index in the parent's parameters list
    let params = parent.parameters();
    let mut param_index: i32 = -1;
    for (i, p) in params.iter().enumerate() {
        if p == param {
            param_index = i as i32;
            break;
        }
    }
    if param_index < 0 {
        return Node::NIL;
    }

    // Get the JSDoc for the parent function/method
    let jsdoc = get_js_doc_or_tag(c, parent, &mut FxHashSet::default());
    if jsdoc.is_nil() || jsdoc.kind() != SyntaxKind::JsDoc {
        return Node::NIL;
    }

    // Collect all @param tags in order
    let tags = jsdoc.tags();
    if tags.is_nil() {
        return Node::NIL;
    }

    let mut param_tag_index: i32 = 0;
    for tag in tags.nodes() {
        if tag.kind() == SyntaxKind::JsDocParameterTag {
            if param_tag_index == param_index {
                return tag;
            }
            param_tag_index += 1;
        }
    }
    Node::NIL
}

// Go: ls/jsdoc.go:296 isMatchingParameterTag
pub fn is_matching_parameter_tag(tag: Node, name: &str) -> bool {
    tag.kind() == SyntaxKind::JsDocParameterTag && is_node_with_name(tag, name)
}

// Go: ls/jsdoc.go:300 isMatchingTemplateTag
pub fn is_matching_template_tag(tag: Node, name: &str) -> bool {
    tag.kind() == SyntaxKind::JsDocTemplateTag
        && tag
            .type_parameters()
            .iter()
            .any(|tp| is_node_with_name(tp, name))
}

// Go: ls/jsdoc.go:304 isNodeWithName
pub fn is_node_with_name(node: Node, name: &str) -> bool {
    let node_name = node.name();
    is_identifier(node_name) && node_name.text() == name
}

// Go: ls/jsdoc.go:309 noMappedLocation
pub fn no_mapped_location(_: &str, _: TextRange) -> lsproto::Location {
    lsproto::Location::default()
}
