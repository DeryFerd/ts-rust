use crate::prelude::*;

impl Checker {
    // Go: checker/jsdoc.go:9 checkUnmatchedJSDocParameters
    pub fn check_unmatched_js_doc_parameters(&mut self, node: Node) {
        let mut jsdoc_parameters: Vec<Node> = Vec::new();
        for tag in get_all_js_doc_tags(node) {
            if tag.kind() == SyntaxKind::JsDocParameterTag {
                let name = tag.name();
                if is_identifier(name) && name.text().is_empty() {
                    continue;
                }
                jsdoc_parameters.push(tag);
            }
        }

        if jsdoc_parameters.is_empty() {
            return;
        }

        let is_js = is_in_js_file(node);
        let mut parameters: FxHashSet<String> = FxHashSet::default();
        let mut excluded_parameters: FxHashSet<i32> = FxHashSet::default();

        for (i, param) in node.parameters().iter().enumerate() {
            let name = param.name();
            if is_identifier(name) {
                parameters.insert(name.text().to_string());
            }
            if is_binding_pattern(name) {
                excluded_parameters.insert(i as i32);
            }
        }
        if self.contains_arguments_reference(node) {
            if is_js {
                let last_js_doc_param_index = jsdoc_parameters.len() as i32 - 1;
                let last_js_doc_param = jsdoc_parameters[last_js_doc_param_index as usize];
                if last_js_doc_param.is_nil() || !is_identifier(last_js_doc_param.name()) {
                    return;
                }
                if excluded_parameters.contains(&last_js_doc_param_index)
                    || parameters.contains(last_js_doc_param.name().text())
                {
                    return;
                }
                let type_expression = last_js_doc_param.type_expression();
                if type_expression.is_nil() || type_expression.type_().is_nil() {
                    return;
                }
                let t = self.get_type_from_type_node(type_expression.type_());
                if self.is_array_type(t) {
                    return;
                }
                self.error(
                    last_js_doc_param.name(),
                    diag::JSDoc_param_tag_has_name_0_but_there_is_no_parameter_with_that_name_It_would_match_arguments_if_it_had_an_array_type,
                    args![last_js_doc_param.name().text()],
                );
            }
        } else {
            for (index, tag) in jsdoc_parameters.iter().copied().enumerate() {
                let name = tag.name();
                let is_name_first = tag.is_name_first();

                if excluded_parameters.contains(&(index as i32))
                    || (is_identifier(name) && parameters.contains(name.text()))
                {
                    continue;
                }

                if is_qualified_name(name) {
                    if is_js {
                        // PORT: the checker-package `entityNameToString(name)` is
                        // `ast.EntityNameToString(name, scanner.GetTextOfNode)`; it is
                        // called directly here to avoid the snake-name clash with the
                        // ast function (same approach as checker_p18.rs).
                        self.error(
                            name,
                            diag::Qualified_name_0_is_not_allowed_without_a_leading_param_object_1,
                            args![
                                entity_name_to_string(name, Some(&get_text_of_node)),
                                entity_name_to_string(name.left(), Some(&get_text_of_node))
                            ],
                        );
                    }
                } else if !is_name_first {
                    self.error_or_suggestion(
                        is_js,
                        name,
                        diag::JSDoc_param_tag_has_name_0_but_there_is_no_parameter_with_that_name,
                        args![name.text()],
                    );
                }
            }
        }
    }
}

// Go: checker/jsdoc.go:86 getAllJSDocTags
pub fn get_all_js_doc_tags(node: Node) -> Vec<Node> {
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
