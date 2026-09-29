//! Port of Go `ls/change/delete.go`.

use crate::ls::change::prelude::*;

// Go: ls/change/delete.go:18 deleteDeclaration
/// deleteDeclaration deletes a node with smart handling for different node types.
/// This handles special cases like import specifiers in lists, parameters, etc.
// PORT: Go `deletedNodesInLists map[*ast.Node]bool` only ever holds `true`,
// so it is an `IndexSet` (insertion order; Go map order is random).
pub fn delete_declaration(
    t: &mut Tracker,
    deleted_nodes_in_lists: &mut IndexSet<Node>,
    source_file: Node,
    node: Node,
) {
    match node.kind() {
        SyntaxKind::Parameter => {
            let old_function = node.parent();
            if old_function.kind() == SyntaxKind::ArrowFunction
                && old_function.parameters().len() == 1
                && astnav::find_child_of_kind(old_function, SyntaxKind::OpenParenToken, source_file)
                    .is_nil()
            {
                // Lambdas with exactly one parameter are special because, after removal, there
                // must be an empty parameter list (i.e. `()`) and this won't necessarily be the
                // case if the parameter is simply removed (e.g. in `x => 1`).
                let range = t.get_adjusted_range(
                    source_file,
                    node,
                    node,
                    LeadingTriviaOption::INCLUDE_ALL,
                    TrailingTriviaOption::INCLUDE,
                );
                t.replace_range_with_text(source_file, range, "()");
            } else {
                delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
            }
        }

        SyntaxKind::ImportDeclaration | SyntaxKind::ImportEqualsDeclaration => {
            let imports = source_file_imports(source_file);
            // PORT: Go `core.Find` returns nil when nothing matches.
            let first_import_syntax = source_file
                .statements()
                .iter()
                .find(|&s| is_any_import_syntax(s))
                .unwrap_or(Node::NIL);
            let is_first_import =
                imports.len() > 0 && node == imports.get(0).parent() || node == first_import_syntax;
            // For first import, leave header comment in place, otherwise only delete JSDoc comments
            let mut leading_trivia = LeadingTriviaOption::START_LINE;
            if is_first_import {
                leading_trivia = LeadingTriviaOption::EXCLUDE;
            } else if has_js_doc_nodes(node) {
                leading_trivia = LeadingTriviaOption::JS_DOC;
            }
            delete_node(
                t,
                source_file,
                node,
                leading_trivia,
                TrailingTriviaOption::INCLUDE,
            );
        }

        SyntaxKind::BindingElement => {
            let pattern = node.parent();
            let preserve_comma = pattern.kind() == SyntaxKind::ArrayBindingPattern
                && node != pattern.elements().get(pattern.elements().len() - 1);
            if preserve_comma {
                delete_node(
                    t,
                    source_file,
                    node,
                    LeadingTriviaOption::INCLUDE_ALL,
                    TrailingTriviaOption::EXCLUDE,
                );
            } else {
                delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
            }
        }

        SyntaxKind::VariableDeclaration => {
            delete_variable_declaration(t, deleted_nodes_in_lists, source_file, node);
        }

        SyntaxKind::TypeParameter => {
            delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
        }

        SyntaxKind::ImportSpecifier => {
            let named_imports = node.parent();
            if named_imports.elements().len() == 1 {
                delete_import_binding(t, source_file, named_imports);
            } else {
                delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
            }
        }

        SyntaxKind::NamespaceImport => {
            delete_import_binding(t, source_file, node);
        }

        SyntaxKind::SemicolonToken => {
            delete_node(
                t,
                source_file,
                node,
                LeadingTriviaOption::INCLUDE_ALL,
                TrailingTriviaOption::EXCLUDE,
            );
        }

        SyntaxKind::TypeKeyword => {
            // For type keyword in import clauses, we need to delete the keyword and any trailing space
            // The trailing space is part of the next token's leading trivia, so we include it
            delete_node(
                t,
                source_file,
                node,
                LeadingTriviaOption::EXCLUDE,
                TrailingTriviaOption::INCLUDE,
            );
        }

        SyntaxKind::FunctionKeyword => {
            delete_node(
                t,
                source_file,
                node,
                LeadingTriviaOption::EXCLUDE,
                TrailingTriviaOption::INCLUDE,
            );
        }

        SyntaxKind::ClassDeclaration | SyntaxKind::FunctionDeclaration => {
            let mut leading_trivia = LeadingTriviaOption::START_LINE;
            if has_js_doc_nodes(node) {
                leading_trivia = LeadingTriviaOption::JS_DOC;
            }
            delete_node(
                t,
                source_file,
                node,
                leading_trivia,
                TrailingTriviaOption::INCLUDE,
            );
        }

        _ => {
            if node.parent().is_nil() {
                // a misbehaving client can reach here with the SourceFile node
                delete_node(
                    t,
                    source_file,
                    node,
                    LeadingTriviaOption::INCLUDE_ALL,
                    TrailingTriviaOption::INCLUDE,
                );
            } else if node.parent().kind() == SyntaxKind::ImportClause
                && node.parent().name() == node
            {
                delete_default_import(t, source_file, node.parent());
            } else if node.parent().kind() == SyntaxKind::CallExpression
                && node
                    .parent()
                    .arguments()
                    .iter()
                    .any(|argument| argument == node)
            {
                delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
            } else {
                delete_node(
                    t,
                    source_file,
                    node,
                    LeadingTriviaOption::INCLUDE_ALL,
                    TrailingTriviaOption::INCLUDE,
                );
            }
        }
    }
}

// Go: ls/change/delete.go:105 deleteDefaultImport
fn delete_default_import(t: &mut Tracker, source_file: Node, import_clause: Node) {
    if import_clause.named_bindings().is_nil() {
        // Delete the whole import
        delete_node(
            t,
            source_file,
            import_clause.parent(),
            LeadingTriviaOption::INCLUDE_ALL,
            TrailingTriviaOption::INCLUDE,
        );
    } else {
        // import |d,| * as ns from './file'
        let name = import_clause.name();
        let start = astnav::get_start_of_node(name, source_file, false);
        let next_token = astnav::get_token_at_position(source_file, name.end());
        if next_token.is_some() && next_token.kind() == SyntaxKind::CommaToken {
            // shift first non-whitespace position after comma to the start position of the node
            let end = skip_trivia_ex(
                source_file_text(source_file),
                next_token.end(),
                Some(&SkipTriviaOptions {
                    stop_after_line_break: false,
                    stop_at_comments: true,
                    ..SkipTriviaOptions::default()
                }),
            );
            let range = t.to_lsp_edit_range(source_file, TextRange::new(start, end));
            t.replace_range_with_text(source_file, range, "");
        } else {
            delete_node(
                t,
                source_file,
                name,
                LeadingTriviaOption::INCLUDE_ALL,
                TrailingTriviaOption::INCLUDE,
            );
        }
    }
}

// Go: ls/change/delete.go:127 deleteImportBinding
fn delete_import_binding(t: &mut Tracker, source_file: Node, node: Node) {
    let import_clause = node.parent();
    if import_clause.name().is_some() {
        // Delete named imports while preserving the default import
        // import d|, * as ns| from './file'
        // import d|, { a }| from './file'
        let previous_token = astnav::get_token_at_position(source_file, node.pos() - 1);
        crate::go_assert!(previous_token.is_some(), "previousToken should not be nil");
        let start = astnav::get_start_of_node(previous_token, source_file, false);
        let range = t.to_lsp_edit_range(source_file, TextRange::new(start, node.end()));
        t.replace_range_with_text(
            source_file,
            range,
            "",
        );
    } else {
        // Delete the entire import declaration
        // |import * as ns from './file'|
        // |import { a } from './file'|
        let import_decl = find_ancestor_kind(node, SyntaxKind::ImportDeclaration);
        crate::go_assert!(import_decl.is_some(), "importDecl should not be nil");
        delete_node(
            t,
            source_file,
            import_decl,
            LeadingTriviaOption::INCLUDE_ALL,
            TrailingTriviaOption::INCLUDE,
        );
    }
}

// Go: ls/change/delete.go:148 deleteVariableDeclaration
fn delete_variable_declaration(
    t: &mut Tracker,
    deleted_nodes_in_lists: &mut IndexSet<Node>,
    source_file: Node,
    node: Node,
) {
    let parent = node.parent();

    if parent.kind() == SyntaxKind::CatchClause {
        // TODO: There's currently no unused diagnostic for this, could be a suggestion
        let open_paren =
            astnav::find_child_of_kind(parent, SyntaxKind::OpenParenToken, source_file);
        let close_paren =
            astnav::find_child_of_kind(parent, SyntaxKind::CloseParenToken, source_file);
        crate::go_assert!(
            open_paren.is_some() && close_paren.is_some(),
            "catch clause should have parens"
        );
        t.delete_node_range(
            source_file,
            open_paren,
            close_paren,
            LeadingTriviaOption::INCLUDE_ALL,
            TrailingTriviaOption::INCLUDE,
        );
        return;
    }

    if parent.declarations().nodes().len() != 1 {
        delete_node_in_list(t, deleted_nodes_in_lists, source_file, node);
        return;
    }

    let gp = parent.parent();
    match gp.kind() {
        SyntaxKind::ForOfStatement | SyntaxKind::ForInStatement => {
            let properties = t.node_factory().new_node_list(&[]);
            let object_literal = t
                .node_factory()
                .new_object_literal_expression(properties, false);
            t.replace_node(source_file, node, object_literal, None);
        }

        SyntaxKind::ForStatement => {
            delete_node(
                t,
                source_file,
                parent,
                LeadingTriviaOption::INCLUDE_ALL,
                TrailingTriviaOption::INCLUDE,
            );
        }

        SyntaxKind::VariableStatement => {
            let mut leading_trivia = LeadingTriviaOption::START_LINE;
            if has_js_doc_nodes(gp) {
                leading_trivia = LeadingTriviaOption::JS_DOC;
            }
            delete_node(
                t,
                source_file,
                gp,
                leading_trivia,
                TrailingTriviaOption::INCLUDE,
            );
        }

        _ => crate::gostd::debug::fail(&format!(
            "Unexpected grandparent kind: {}",
            crate::gostd::debug::kind_string(gp.kind())
        )),
    }
}

// Go: ls/change/delete.go:187 deleteNode
/// deleteNode deletes a node with the specified trivia options.
/// Warning: This deletes comments too.
fn delete_node(
    t: &mut Tracker,
    source_file: Node,
    node: Node,
    leading_trivia: LeadingTriviaOption,
    trailing_trivia: TrailingTriviaOption,
) {
    let start_position = t.get_adjusted_start_position(source_file, node, leading_trivia, false);
    let end_position = t.get_adjusted_end_position(source_file, node, trailing_trivia);
    let range = t.to_lsp_edit_range(source_file, TextRange::new(start_position, end_position));
    t.replace_range_with_text(
        source_file,
        range,
        "",
    );
}

// Go: ls/change/delete.go:195 deleteNodeInList
fn delete_node_in_list(
    t: &mut Tracker,
    deleted_nodes_in_lists: &mut IndexSet<Node>,
    source_file: Node,
    node: Node,
) {
    let containing_list = format::get_containing_list(node, source_file);
    crate::go_assert!(
        containing_list.is_some(),
        "containingList should not be nil"
    );
    let containing_nodes = containing_list.nodes();
    let index: i32 = containing_nodes
        .iter()
        .position(|n| n == node)
        .map_or(-1, |i| i as i32);
    crate::go_assert!(index != -1, "node should be in containing list");

    if containing_nodes.len() == 1 {
        delete_node(
            t,
            source_file,
            node,
            LeadingTriviaOption::INCLUDE_ALL,
            TrailingTriviaOption::INCLUDE,
        );
        return;
    }

    // Note: We will only delete a comma *after* a node. This will leave a trailing comma if we delete the last node.
    // That's handled in the end by finishTrailingCommaAfterDeletingNodesInList.
    crate::go_assert!(
        !deleted_nodes_in_lists.contains(&node),
        "Deleting a node twice"
    );
    deleted_nodes_in_lists.insert(node);

    let start_pos = t.start_position_to_delete_node_in_list(source_file, node);
    let end_pos: i32;
    if index == containing_nodes.len() as i32 - 1 {
        end_pos = t.get_adjusted_end_position(source_file, node, TrailingTriviaOption::NONE);
    } else {
        let mut prev_node = Node::NIL;
        if index > 0 {
            prev_node = containing_nodes.get((index - 1) as usize);
        }
        end_pos = t.end_position_to_delete_node_in_list(
            source_file,
            node,
            prev_node,
            containing_nodes.get((index + 1) as usize),
        );
    }

    let range = t.to_lsp_edit_range(source_file, TextRange::new(start_pos, end_pos));
    t.replace_range_with_text(source_file, range, "");
}

impl Tracker {
    // Go: ls/change/delete.go:229 startPositionToDeleteNodeInList
    /// startPositionToDeleteNodeInList finds the first non-whitespace position in the leading trivia of the node
    pub fn start_position_to_delete_node_in_list(&self, source_file: Node, node: Node) -> i32 {
        let start = self.get_adjusted_start_position(
            source_file,
            node,
            LeadingTriviaOption::INCLUDE_ALL,
            false,
        );
        skip_trivia_ex(
            source_file_text(source_file),
            start,
            Some(&SkipTriviaOptions {
                stop_after_line_break: false,
                stop_at_comments: true,
                ..SkipTriviaOptions::default()
            }),
        )
    }

    // Go: ls/change/delete.go:234 endPositionToDeleteNodeInList
    fn end_position_to_delete_node_in_list(
        &self,
        source_file: Node,
        node: Node,
        prev_node: Node,
        next_node: Node,
    ) -> i32 {
        let end = self.start_position_to_delete_node_in_list(source_file, next_node);
        if prev_node.is_nil()
            || positions_are_on_same_line(
                self.get_adjusted_end_position(source_file, node, TrailingTriviaOption::INCLUDE),
                end,
                source_file,
            )
        {
            return end;
        }
        let token = astnav::find_preceding_token(
            source_file,
            astnav::get_start_of_node(next_node, source_file, false),
        );
        if is_separator(node, token) {
            let prev_token = astnav::find_preceding_token(
                source_file,
                astnav::get_start_of_node(node, source_file, false),
            );
            if is_separator(prev_node, prev_token) {
                let text = source_file_text(source_file);
                let pos = skip_trivia_ex(
                    text,
                    token.end(),
                    Some(&SkipTriviaOptions {
                        stop_after_line_break: true,
                        stop_at_comments: true,
                        ..SkipTriviaOptions::default()
                    }),
                );
                if positions_are_on_same_line(
                    astnav::get_start_of_node(prev_token, source_file, false),
                    astnav::get_start_of_node(token, source_file, false),
                    source_file,
                ) {
                    if pos > 0 && is_line_break(char::from(text.as_bytes()[(pos - 1) as usize])) {
                        return pos - 1;
                    }
                    return pos;
                }
                if is_line_break(char::from(text.as_bytes()[pos as usize])) {
                    return pos;
                }
            }
        }
        end
    }
}

// Go: ls/change/delete.go:258 positionsAreOnSameLine
pub fn positions_are_on_same_line(pos1: i32, pos2: i32, source_file: Node) -> bool {
    format::get_line_start_position_for_position(pos1, source_file)
        == format::get_line_start_position_for_position(pos2, source_file)
}

// Go: ls/change/delete.go:263 hasJSDocNodes
/// hasJSDocNodes checks if a node has JSDoc comments
fn has_js_doc_nodes(node: Node) -> bool {
    if node.is_nil() {
        return false;
    }
    // nil is ok for JSDoc - it will return empty slice if not available
    let jsdocs = node.js_doc(Node::NIL);
    jsdocs.len() > 0
}
