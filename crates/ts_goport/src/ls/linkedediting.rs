//! Port of Go `ls/linkedediting.go`.

use crate::ls::prelude::*;

// Go: ls/linkedediting.go:15 jsxTagWordPattern
// allow the client to match more than valid tag names. This allows linked editing when typing is in progress or tag name is incomplete
// PORT: Go `*string` built with `new(...)`; the value never changes, so a
// `&'static str` holds it and each response copies it into `word_pattern`.
pub static JSX_TAG_WORD_PATTERN: &str = "[a-zA-Z0-9:\\-\\._$]*";

impl LanguageService {
    // Go: ls/linkedediting.go:17 ProvideLinkedEditingRange
    pub fn provide_linked_editing_range(
        &self,
        _ctx: &Context,
        params: &lsproto::LinkedEditingRangeParams,
    ) -> Result<lsproto::LinkedEditingRangeResponse, GoError> {
        let (_, source_file) = self.get_program_and_file(&params.text_document.uri);
        let position = self
            .converters
            .line_and_character_to_position(&source_file, &params.position);
        let token = astnav::find_preceding_token(source_file, position);

        if token.is_nil() || token.parent().kind() == SyntaxKind::SourceFile {
            return Ok(lsproto::LinkedEditingRangeResponse::default());
        }

        if is_jsx_fragment(token.parent().parent()) {
            let fragment = token.parent().parent();
            let open_fragment = fragment.opening_fragment();
            let close_fragment = fragment.closing_fragment();
            if open_fragment
                .flags()
                .intersects(NodeFlags::THIS_NODE_OR_ANY_SUB_NODES_HAS_ERROR)
                || close_fragment
                    .flags()
                    .intersects(NodeFlags::THIS_NODE_OR_ANY_SUB_NODES_HAS_ERROR)
            {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }

            let open_pos =
                astnav::get_start_of_node(open_fragment, source_file, false) + "<".len() as i32;
            let close_pos =
                astnav::get_start_of_node(close_fragment, source_file, false) + "</".len() as i32;

            // only allows linked editing right after opening bracket: <| ></| >
            if (position != open_pos) && (position != close_pos) {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }

            let open_line_char = self
                .converters
                .position_to_line_and_character(&source_file, open_pos);
            let close_line_char = self
                .converters
                .position_to_line_and_character(&source_file, close_pos);
            Ok(lsproto::LinkedEditingRangeResponse {
                linked_editing_ranges: Some(lsproto::LinkedEditingRanges {
                    ranges: vec![
                        // only return start position for opening tag since the length of a fragment is always 3 and it is unlikely user will type in the middle of a fragment tag
                        lsproto::Range {
                            start: open_line_char,
                            end: open_line_char,
                        },
                        lsproto::Range {
                            start: close_line_char,
                            end: close_line_char,
                        },
                    ],
                    word_pattern: Some(JSX_TAG_WORD_PATTERN.to_string()),
                }),
            })
        } else {
            // determines if the cursor is in an element tag
            let tag = find_ancestor(token.parent(), |n| {
                if is_jsx_opening_element(n) || is_jsx_closing_element(n) {
                    return true;
                }
                false
            });
            if tag.is_nil() {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }
            crate::go_assert!(
                is_jsx_opening_element(tag) || is_jsx_closing_element(tag),
                "tag should be opening or closing element"
            );

            let jsx_element = tag.parent();
            let open_tag = jsx_element.opening_element();
            let close_tag = jsx_element.closing_element();

            let open_tag_name_start =
                astnav::get_start_of_node(open_tag.tag_name(), source_file, false);
            let open_tag_name_end = open_tag.tag_name().end();
            let close_tag_name_start =
                astnav::get_start_of_node(close_tag.tag_name(), source_file, false);
            let close_tag_name_end = close_tag.tag_name().end();
            // do not return linked cursors if tags are not well-formed
            if open_tag_name_start == astnav::get_start_of_node(open_tag, source_file, false)
                || close_tag_name_start == astnav::get_start_of_node(close_tag, source_file, false)
                || open_tag_name_end == open_tag.end()
                || close_tag_name_end == close_tag.end()
            {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }
            // only return linked cursors if the cursor is within a tag name
            let position_int = position;
            if !(open_tag_name_start <= position_int && position_int <= open_tag_name_end
                || close_tag_name_start <= position_int && position_int <= close_tag_name_end)
            {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }

            // only return linked cursors if text in both tags is identical
            let opening_tag_text = get_text_of_node(open_tag.tag_name());
            if opening_tag_text != get_text_of_node(close_tag.tag_name()) {
                return Ok(lsproto::LinkedEditingRangeResponse::default());
            }

            Ok(lsproto::LinkedEditingRangeResponse {
                linked_editing_ranges: Some(lsproto::LinkedEditingRanges {
                    ranges: vec![
                        lsproto::Range {
                            start: self
                                .converters
                                .position_to_line_and_character(&source_file, open_tag_name_start),
                            end: self
                                .converters
                                .position_to_line_and_character(&source_file, open_tag_name_end),
                        },
                        lsproto::Range {
                            start: self
                                .converters
                                .position_to_line_and_character(&source_file, close_tag_name_start),
                            end: self
                                .converters
                                .position_to_line_and_character(&source_file, close_tag_name_end),
                        },
                    ],
                    word_pattern: Some(JSX_TAG_WORD_PATTERN.to_string()),
                }),
            })
        }
    }
}
