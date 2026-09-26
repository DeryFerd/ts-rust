use crate::ls::prelude::*;

// Go `internal/ls/selectionranges.go`: textDocument/selectionRange.

use crate::frontend::scanner::get_trailing_comment_ranges;
use std::cell::Cell;

impl LanguageService {
    // Go: ls/selectionranges.go:13 ProvideSelectionRanges
    pub fn provide_selection_ranges(
        &self,
        ctx: &Context,
        params: &lsproto::SelectionRangeParams,
    ) -> Result<lsproto::SelectionRangeResponse, GoError> {
        let (_, source_file) = self.get_program_and_file(&params.text_document.uri);
        if source_file.is_nil() {
            return Ok(lsproto::SelectionRangesOrNull::default());
        }

        let mut results: Vec<lsproto::SelectionRange> = Vec::new();
        for position in &params.positions {
            let pos = self
                .converters
                .line_and_character_to_position(&source_file, position);
            let selection_range = get_smart_selection_range(self, source_file, pos);
            if let Some(selection_range) = selection_range {
                results.push(selection_range);
            }
        }

        Ok(lsproto::SelectionRangesOrNull {
            selection_ranges: Some(results),
        })
    }
}

// Go: ls/selectionranges.go:31 getSmartSelectionRange
// PORT: Go builds a linked list of `*lsproto.SelectionRange` through their
// `Parent` pointers. Here the chain is `Option<Box<lsproto::SelectionRange>>`
// (Go nil is `None`). The closures share `result` and `next` through
// `RefCell` and `Cell`, as Go closures share the locals.
fn get_smart_selection_range(
    l: &LanguageService,
    source_file: Node,
    pos: i32,
) -> Option<lsproto::SelectionRange> {
    let factory = NodeFactory::default();

    let node_contains_position = |node: Node| -> bool {
        if node.is_nil() {
            return false;
        }
        let start = get_token_pos_of_node(node, source_file, true /*includeJSDoc*/);
        let end = node.end();
        start <= pos && pos < end
    };

    let push_selection_range = |current: Option<Box<lsproto::SelectionRange>>,
                                start: i32,
                                end: i32|
     -> Option<Box<lsproto::SelectionRange>> {
        if start == end {
            return current;
        }

        if !(start <= pos && pos <= end) {
            return current;
        }

        let lsp_range = l
            .converters
            .to_lsp_range(&source_file, TextRange::new(start, end));

        if current.as_ref().is_some_and(|c| c.range == lsp_range) {
            return current;
        }

        Some(Box::new(lsproto::SelectionRange {
            range: lsp_range,
            parent: current,
        }))
    };

    let push_selection_comment_range = |current: Option<Box<lsproto::SelectionRange>>,
                                        start: i32,
                                        end: i32|
     -> Option<Box<lsproto::SelectionRange>> {
        let current = push_selection_range(current, start, end);

        let mut comment_pos = start;
        let text = source_file_text(source_file).as_bytes();
        while comment_pos < end
            && (comment_pos as usize) < text.len()
            && text[comment_pos as usize] == b'/'
        {
            comment_pos += 1;
        }
        push_selection_range(current, comment_pos, end)
    };

    let positions_are_on_same_line = |pos1: i32, pos2: i32| -> bool {
        if pos1 == pos2 {
            return true;
        }
        let lsp_pos1 = l
            .converters
            .position_to_line_and_character(&source_file, pos1);
        let lsp_pos2 = l
            .converters
            .position_to_line_and_character(&source_file, pos2);
        lsp_pos1.line == lsp_pos2.line
    };

    let should_skip_node = |node: Node, parent: Node| -> bool {
        if is_block(node) {
            return true;
        }

        // PORT: Go calls `ast.IsTemplateHead` and `ast.IsTemplateTail`; the ls
        // package has helpers with the same snake names.
        if is_template_span(node)
            || crate::ast::is_template_head(node)
            || crate::ast::is_template_tail(node)
        {
            return true;
        }

        if parent.is_some() && is_variable_declaration_list(node) && is_variable_statement(parent) {
            return true;
        }

        // Skip lone variable declarations
        if parent.is_some() && is_variable_declaration(node) && is_variable_declaration_list(parent)
        {
            let decl = parent;
            if decl.is_some() && decl.declarations().nodes().len() == 1 {
                return true;
            }
        }

        if is_js_doc_type_expression(node)
            || is_js_doc_signature(node)
            || is_js_doc_type_literal(node)
        {
            return true;
        }

        false
    };

    let full_range = l.converters.to_lsp_range(
        &source_file,
        TextRange::new(source_file.pos(), source_file.end()),
    );
    let result: RefCell<Option<Box<lsproto::SelectionRange>>> =
        RefCell::new(Some(Box::new(lsproto::SelectionRange {
            range: full_range,
            parent: None,
        })));

    let mut current = source_file;
    while current.is_some() {
        let next: Cell<Node> = Cell::new(Node::NIL);
        let parent = current;

        let visit = |node: Node| -> Node {
            if node.is_some() && next.get().is_nil() {
                let mut found_comment: Option<CommentRange> = None;
                // PORT: Go reads only the first item of the lazy iterator.
                for comment in
                    get_trailing_comment_ranges(&factory, source_file_text(source_file), node.end())
                {
                    found_comment = Some(comment);
                    break;
                }
                if let Some(found_comment) = found_comment {
                    if found_comment.kind == SyntaxKind::SingleLineCommentTrivia {
                        let r = result.take();
                        *result.borrow_mut() = push_selection_comment_range(
                            r,
                            found_comment.pos(),
                            found_comment.end(),
                        );
                    }
                }

                if node_contains_position(node) {
                    // Add range for multi-line function bodies before skipping the block
                    if is_block(node) && is_function_like_declaration(parent) {
                        if !positions_are_on_same_line(
                            astnav::get_start_of_node(node, source_file, false),
                            node.end(),
                        ) {
                            let start = astnav::get_start_of_node(node, source_file, false);
                            let end = node.end();
                            let r = result.take();
                            *result.borrow_mut() = push_selection_range(r, start, end);
                        }
                    }

                    // Synthesize a stop for '${ ... }' since '${' and '}' actually belong to siblings.
                    if is_template_span(parent) {
                        let template_span = parent;
                        if template_span.literal().is_some() {
                            // Start from just before the '${' and end after the '}'
                            // The '${' is 2 characters before the expression start
                            let span_start = node.pos() - 2;
                            // The '}' is the first character of the template literal (middle or tail)
                            let span_end = astnav::get_start_of_node(
                                template_span.literal(),
                                source_file,
                                false,
                            ) + 1;
                            // Validate the positions are reasonable
                            let text = source_file_text(source_file);
                            if span_start >= 0
                                && span_end as usize <= text.len()
                                && span_start < span_end
                            {
                                let r = result.take();
                                *result.borrow_mut() =
                                    push_selection_range(r, span_start, span_end);
                            }
                        }
                    }

                    if !should_skip_node(node, parent) {
                        let start = astnav::get_start_of_node(node, source_file, false);
                        let end = node.end();
                        let r = result.take();
                        *result.borrow_mut() = push_selection_range(r, start, end);

                        // String literals should have a stop both inside and outside their quotes.
                        if is_string_literal(node)
                            || node.kind() == SyntaxKind::TemplateExpression
                            || node.kind() == SyntaxKind::NoSubstitutionTemplateLiteral
                        {
                            // Only add inner content range if there's actually content (handles unterminated literals)
                            if start + 1 < end - 1 {
                                let r = result.take();
                                *result.borrow_mut() = push_selection_range(r, start + 1, end - 1);
                            }
                        }
                    }

                    next.set(node);
                }
            }
            node
        };

        let visit_nodes = |nodes: NodeList, v: &mut NodeVisitor<'_, ()>| -> NodeList {
            if nodes.is_some() && !nodes.nodes().is_empty() {
                let should_skip_list = parent.is_some()
                    && (is_variable_declaration_list(parent) || is_template_expression(parent));

                if !should_skip_list {
                    let start = astnav::get_start_of_node(nodes.nodes().get(0), source_file, false);
                    let end = nodes.nodes().get(nodes.nodes().len() - 1).end();

                    if start <= pos && pos < end {
                        let r = result.take();
                        *result.borrow_mut() = push_selection_range(r, start, end);
                    }
                }
            }
            v.visit_nodes(nodes)
        };

        // Visit JSDoc nodes first if they exist
        for jsdoc in current.js_doc(source_file) {
            visit(jsdoc);
        }

        let mut temp_visitor = new_node_visitor(
            |node: Node, _v: &mut NodeVisitor<'_, ()>| -> Node { visit(node) },
            None,
            NodeVisitorHooks {
                visit_nodes: Some(Rc::new(visit_nodes)),
                ..Default::default()
            },
            (),
        );

        current.visit_each_child(&mut temp_visitor);
        current = next.get();
    }
    result.into_inner().map(|r| *r)
}
