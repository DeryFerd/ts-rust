use crate::ls::prelude::*;

// Go `internal/ls/selectionranges.go`: textDocument/selectionRange.

use crate::frontend::scanner::get_trailing_comment_ranges;
use crate::spanmap::Feature;
use std::cell::Cell;

// Go: ls/selectionranges.go:15 maxSelectionRangeDepth
const MAX_SELECTION_RANGE_DEPTH: usize = 1000;

// Go: ls/selectionranges.go:17 selectionRangeBuilder
// PORT: Go reads the capacity with `cap(b.ranges)`. A Rust `Vec` can hold
// more than it was asked for, so the capacity is a field.
struct SelectionRangeBuilder {
    ranges: Vec<lsproto::Range>,
    oldest_index: usize,
    capacity: usize,
}

// Go: ls/selectionranges.go:22 newSelectionRangeBuilder
fn new_selection_range_builder(capacity: usize) -> SelectionRangeBuilder {
    SelectionRangeBuilder {
        ranges: Vec::with_capacity(capacity),
        oldest_index: 0,
        capacity,
    }
}

impl SelectionRangeBuilder {
    // Go: ls/selectionranges.go:28 push
    fn push(&mut self, selection_range: lsproto::Range) {
        if self.ranges.len() < self.capacity {
            self.ranges.push(selection_range);
            return;
        }

        self.ranges[self.oldest_index] = selection_range;
        self.oldest_index = (self.oldest_index + 1) % self.ranges.len();
    }

    // Go: ls/selectionranges.go:38 build
    fn build(
        &self,
        mut result: Option<lsproto::SelectionRange>,
    ) -> Option<lsproto::SelectionRange> {
        for i in 0..self.ranges.len() {
            let index = (self.oldest_index + i) % self.ranges.len();
            result = Some(lsproto::SelectionRange {
                range: self.ranges[index],
                parent: result.map(Box::new),
            });
        }
        result
    }
}

impl LanguageService {
    // Go: ls/selectionranges.go:49 ProvideSelectionRanges
    pub fn provide_selection_ranges(
        &self,
        ctx: &Context,
        params: &lsproto::SelectionRangeParams,
    ) -> Result<lsproto::SelectionRangeResponse, GoError> {
        let (_, source_file) = self.get_program_and_file(&params.text_document.uri);
        if source_file.is_nil() {
            return Ok(lsproto::SelectionRangesOrNull::default());
        }

        let mut results: Vec<lsproto::SelectionRange> = Vec::with_capacity(params.positions.len());
        for position in &params.positions {
            let positions = lsconv::from_lsp_position_for_source_file(
                &self.converters,
                source_file,
                *position,
                Feature::SELECTION_RANGES,
            );
            if positions.len() != 1 || !positions[0].fidelity.is_single_segment() {
                return Ok(lsproto::SelectionRangesOrNull::default());
            }
            let selection_range =
                get_smart_selection_range(self, positions[0].script, positions[0].position);
            if let Some(selection_range) = selection_range {
                results.push(selection_range);
            }
        }

        Ok(lsproto::SelectionRangesOrNull {
            selection_ranges: Some(results),
        })
    }
}

// Go: ls/selectionranges.go:70 getSelectionChildren
fn get_selection_children(factory: &NodeFactory, node: Node, source_file: Node) -> Vec<Node> {
    if !is_mapped_type_node(node) {
        return get_children_from_non_js_doc_node(node, source_file);
    }

    let children = get_children_from_non_js_doc_node(node, source_file);
    if children.len() < 2 {
        return children;
    }

    let open_brace_token = children[0];
    let close_brace_token = children[children.len() - 1];
    if open_brace_token.kind() != SyntaxKind::OpenBraceToken
        || close_brace_token.kind() != SyntaxKind::CloseBraceToken
    {
        return children;
    }

    let mapped_type = node;
    let children = &children[1..children.len() - 1];

    // Group `-/+readonly` and `-/+?`.
    let grouped_with_plus_minus_tokens = group_children(factory, children, |child| {
        child == mapped_type.readonly_token()
            || child.kind() == SyntaxKind::ReadonlyKeyword
            || child == mapped_type.question_token()
            || child.kind() == SyntaxKind::QuestionToken
    });

    // Group the type parameter with its surrounding brackets.
    let grouped_with_brackets = group_children(factory, &grouped_with_plus_minus_tokens, |child| {
        child.kind() == SyntaxKind::OpenBracketToken
            || child.kind() == SyntaxKind::TypeParameter
            || child.kind() == SyntaxKind::CloseBracketToken
    });

    // Go exposes the trailing semicolon directly, so keep it in the right-hand
    // group to produce the same effective selection tree as Strada.
    vec![
        open_brace_token,
        create_syntax_list(
            factory,
            &split_children(
                factory,
                &grouped_with_brackets,
                |child| child.kind() == SyntaxKind::ColonToken,
                false,
            ),
        ),
        close_brace_token,
    ]
}

// Go: ls/selectionranges.go:115 groupChildren
fn group_children(
    factory: &NodeFactory,
    children: &[Node],
    group_on: impl Fn(Node) -> bool,
) -> Vec<Node> {
    let mut result: Vec<Node> = Vec::new();
    let mut group: Vec<Node> = Vec::new();
    for &child in children {
        if group_on(child) {
            group.push(child);
        } else {
            if !group.is_empty() {
                result.push(create_syntax_list(factory, &group));
                group = Vec::new();
            }
            result.push(child);
        }
    }
    if !group.is_empty() {
        result.push(create_syntax_list(factory, &group));
    }
    result
}

// Go: ls/selectionranges.go:135 splitChildren
fn split_children(
    factory: &NodeFactory,
    children: &[Node],
    pivot_on: impl Fn(Node) -> bool,
    separate_trailing_semicolon: bool,
) -> Vec<Node> {
    if children.len() < 2 {
        return children.to_vec();
    }

    let mut split_token_index: i32 = -1;
    for (i, &child) in children.iter().enumerate() {
        if pivot_on(child) {
            split_token_index = i as i32;
            break;
        }
    }
    if split_token_index == -1 {
        return children.to_vec();
    }
    let split_token_index = split_token_index as usize;

    let left_children = &children[..split_token_index];
    let split_token = children[split_token_index];
    let last_token = children[children.len() - 1];
    let separate_last_token =
        separate_trailing_semicolon && last_token.kind() == SyntaxKind::SemicolonToken;
    let mut right_end = children.len();
    if separate_last_token {
        right_end -= 1;
    }
    let right_children = &children[split_token_index + 1..right_end];

    let mut result: Vec<Node> = Vec::with_capacity(4);
    if !left_children.is_empty() {
        result.push(create_syntax_list(factory, left_children));
    }
    result.push(split_token);
    if !right_children.is_empty() {
        result.push(create_syntax_list(factory, right_children));
    }
    if separate_last_token {
        result.push(last_token);
    }
    result
}

// Go: ls/selectionranges.go:180 createSyntaxList
fn create_syntax_list(factory: &NodeFactory, children: &[Node]) -> Node {
    let list = factory.new_syntax_list(children);
    set_node_loc(
        list,
        TextRange::new(children[0].pos(), children[children.len() - 1].end()),
    );
    list
}

// Go: ls/selectionranges.go:186 getSmartSelectionRange
// PORT: Go builds the `*lsproto.SelectionRange` chain in `ranges.build`. The
// closures share `ranges`, `last_range` and `next` through `RefCell` and
// `Cell`, as Go closures share the locals. Go returns nil for a
// content-mapped file with no ranges; `None` is that nil.
fn get_smart_selection_range(
    l: &LanguageService,
    source_file: Node,
    pos: i32,
) -> Option<lsproto::SelectionRange> {
    let factory = NodeFactory::default();
    // Traversal discovers ranges from broadest to most specific, so retain the newest ranges nearest to the cursor
    let ranges = RefCell::new(new_selection_range_builder(MAX_SELECTION_RANGE_DEPTH - 1));
    let mut root: Option<lsproto::SelectionRange> = None;
    let last_range = Cell::new(lsproto::Range::default());
    if source_file_content_mapper(source_file).is_empty() {
        let (full_range, _) = l.converters.to_lsp_range(
            &source_file,
            TextRange::new(source_file.pos(), source_file.end()),
        );
        root = Some(lsproto::SelectionRange {
            range: full_range,
            parent: None,
        });
        last_range.set(full_range);
    }

    let node_contains_position = |node: Node| -> bool {
        if node.is_nil() {
            return false;
        }
        let start = get_token_pos_of_node(node, source_file, true /*includeJSDoc*/);
        let end = node.end();
        start <= pos && pos < end
    };

    let position_should_snap_to_node = |node: Node| -> bool {
        if pos < node.end() {
            return true;
        }
        if node.end() == pos {
            let touching_property_name = astnav::get_touching_property_name(source_file, pos);
            return touching_property_name.is_some() && touching_property_name.pos() < node.end();
        }
        false
    };

    let push_selection_range = |start: i32, end: i32| {
        if start == end {
            return;
        }

        if !(start <= pos && pos <= end) {
            return;
        }

        let (lsp_range, fidelity) = l.converters.to_lsp_range_for_feature(
            &source_file,
            TextRange::new(start, end),
            Feature::SELECTION_RANGES,
        );
        if fidelity.is_none() {
            return;
        }

        if last_range.get() == lsp_range {
            return;
        }
        last_range.set(lsp_range);

        ranges.borrow_mut().push(lsp_range);
    };

    let push_selection_comment_range = |start: i32, end: i32| {
        push_selection_range(start, end);

        let mut comment_pos = start;
        let text = source_file_text(source_file).as_bytes();
        while comment_pos < end
            && (comment_pos as usize) < text.len()
            && text[comment_pos as usize] == b'/'
        {
            comment_pos += 1;
        }
        push_selection_range(comment_pos, end);
    };

    let positions_are_on_same_line = |pos1: i32, pos2: i32| -> bool {
        if pos1 == pos2 {
            return true;
        }
        let line_starts = &*get_ecma_line_starts(source_file);
        compute_line_of_position(line_starts, pos1) == compute_line_of_position(line_starts, pos2)
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
                        push_selection_comment_range(found_comment.pos(), found_comment.end());
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
                            push_selection_range(start, end);
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
                                push_selection_range(span_start, span_end);
                            }
                        }
                    }

                    if !should_skip_node(node, parent) {
                        let start = astnav::get_start_of_node(node, source_file, false);
                        let end = node.end();
                        push_selection_range(start, end);

                        if is_mapped_type_node(node) {
                            let mut selection_parent = node;
                            loop {
                                let mut selection_child = Node::NIL;
                                for child in
                                    get_selection_children(&factory, selection_parent, source_file)
                                {
                                    let child_start = get_token_pos_of_node(
                                        child,
                                        source_file,
                                        true, /*includeJSDoc*/
                                    );
                                    if child_start > pos {
                                        break;
                                    }
                                    if position_should_snap_to_node(child) {
                                        push_selection_range(child_start, child.end());
                                        selection_child = child;
                                        break;
                                    }
                                }
                                if selection_child.is_nil() || !is_syntax_list(selection_child) {
                                    break;
                                }
                                selection_parent = selection_child;
                            }
                        }

                        // String literals should have a stop both inside and outside their quotes.
                        if is_string_literal(node)
                            || node.kind() == SyntaxKind::TemplateExpression
                            || node.kind() == SyntaxKind::NoSubstitutionTemplateLiteral
                        {
                            // Only add inner content range if there's actually content (handles unterminated literals)
                            if start + 1 < end - 1 {
                                push_selection_range(start + 1, end - 1);
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
                        push_selection_range(start, end);
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
    ranges.borrow().build(root)
}
