use crate::ls::prelude::*;

// Port of Go `ls/autoinsert.go`.

use crate::astnav;
use crate::gostd::{Context, GoError};
use crate::lsp::lsproto;

impl LanguageService {
    // Go: ls/autoinsert.go:12 ProvideOnAutoInsert
    pub fn provide_on_auto_insert(
        &self,
        _ctx: &Context,
        params: &lsproto::VSOnAutoInsertParams,
    ) -> Result<lsproto::VSOnAutoInsertResponse, GoError> {
        if params.vs_ch != ">" {
            return Ok(lsproto::VSOnAutoInsertResponse::default());
        }

        let (_, source_file) = self.get_program_and_file(&params.vs_text_document.uri);
        let position = self
            .converters
            .line_and_character_to_position(&source_file, &params.vs_position);

        let token = astnav::find_preceding_token(source_file, position);
        if token.is_nil() {
            return Ok(lsproto::VSOnAutoInsertResponse::default());
        }

        let mut closing_text = String::new();
        let mut element = Node::NIL;
        if token.kind() == SyntaxKind::GreaterThanToken && is_jsx_opening_element(token.parent()) {
            element = token.parent().parent();
        } else if is_jsx_text(token) && is_jsx_element(token.parent()) {
            element = token.parent();
        }

        if element.is_some() && is_unclosed_tag(element) {
            let tag_name_node = element.opening_element().tag_name();
            // Slight divergence from Strada - we don't use the verbatim text from the opening tag.
            closing_text = "</".to_string()
                + &entity_name_to_string(tag_name_node, Some(&get_text_of_node))
                + ">";
        } else {
            let mut fragment = Node::NIL;
            if token.kind() == SyntaxKind::GreaterThanToken
                && is_jsx_opening_fragment(token.parent())
            {
                fragment = token.parent().parent();
            } else if is_jsx_text(token) && is_jsx_fragment(token.parent()) {
                fragment = token.parent();
            }

            if fragment.is_some() && is_unclosed_fragment(fragment) {
                closing_text = "</>".to_string();
            }
        }

        if closing_text.is_empty() {
            return Ok(lsproto::VSOnAutoInsertResponse::default());
        }

        Ok(lsproto::VSOnAutoInsertResponse {
            vs_on_auto_insert_response_item: Some(lsproto::VSOnAutoInsertResponseItem {
                vs_text_edit_format: lsproto::InsertTextFormat::SNIPPET,
                vs_text_edit: Some(lsproto::TextEdit {
                    range: lsproto::Range {
                        start: params.vs_position,
                        end: params.vs_position,
                    },
                    // Tag names can contain `$` (valid JSX identifier characters), so
                    // escape the closing text to avoid being interpreted as a snippet
                    // placeholder/variable.
                    new_text: "$0".to_string() + &escape_snippet_text(&closing_text),
                }),
            }),
        })
    }
}

// Go: ls/autoinsert.go:68 isUnclosedTag
// PORT: Go takes `*ast.JsxElement`; the node handle is the JsxElement node.
fn is_unclosed_tag(node: Node) -> bool {
    let opening_element = node.opening_element();
    let closing_element = node.closing_element();
    if !tag_names_are_equivalent(opening_element.tag_name(), closing_element.tag_name()) {
        return true;
    }

    let parent = node.parent();
    if is_jsx_element(parent) {
        return tag_names_are_equivalent(
            opening_element.tag_name(),
            parent.opening_element().tag_name(),
        ) && is_unclosed_tag(parent);
    }

    false
}

// Go: ls/autoinsert.go:84 isUnclosedFragment
// PORT: Go takes `*ast.JsxFragment`; the node handle is the JsxFragment node.
fn is_unclosed_fragment(node: Node) -> bool {
    let closing_fragment = node.closing_fragment();
    if closing_fragment
        .flags()
        .intersects(NodeFlags::THIS_NODE_HAS_ERROR)
    {
        return true;
    }

    let parent = node.parent();
    if is_jsx_fragment(parent) && is_unclosed_fragment(parent) {
        return true;
    }

    false
}
