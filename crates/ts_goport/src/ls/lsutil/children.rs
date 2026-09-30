//! Port of Go `ls/lsutil/children.go`.

use crate::astnav;
use crate::frontend::scanner::scanner_ls;
use crate::ls::lsutil::prelude::*;
use std::cell::Cell;

// Go: ls/lsutil/children.go:11 GetLastChild
/// Replaces last(node.getChildren(sourceFile))
pub fn get_last_child(node: Node, source_file: Node) -> Node {
    let last_child_node = get_last_visited_child(node, source_file);
    if is_js_doc_single_comment_node(node) && last_child_node.is_nil() {
        return Node::NIL;
    }
    let token_start_pos = if last_child_node.is_some() {
        last_child_node.end()
    } else {
        node.pos()
    };
    let mut last_token = Node::NIL;
    let mut scanner = scanner_ls::get_scanner_for_source_file(source_file, token_start_pos);
    let mut start_pos = token_start_pos;
    while start_pos < node.end() {
        let token_kind = scanner.token();
        let token_full_start = scanner.token_full_start();
        let token_end = scanner.token_end();
        last_token = source_file_get_or_create_token(
            source_file,
            token_kind,
            token_full_start,
            token_end,
            node,
            scanner.token_flags(),
        );
        start_pos = token_end;
        scanner.scan();
    }
    if last_token.is_some() {
        last_token
    } else {
        last_child_node
    }
}

// Go: ls/lsutil/children.go:35 GetLastToken
pub fn get_last_token(node: Node, source_file: Node) -> Node {
    if node.is_nil() {
        return Node::NIL;
    }

    if is_token_kind(node.kind()) || is_identifier(node) {
        return Node::NIL;
    }

    assert_has_real_position(node);

    let last_child = get_last_child(node, source_file);
    if last_child.is_nil() {
        return Node::NIL;
    }

    if (last_child.kind() as u16) < (SyntaxKind::FIRST_NODE as u16) {
        last_child
    } else {
        get_last_token(last_child, source_file)
    }
}

// Go: ls/lsutil/children.go:60 GetLastVisitedChild
/// Gets the last visited child of the given node.
/// NOTE: This doesn't include unvisited tokens; for this, use `getLastChild` or `getLastToken`.
pub fn get_last_visited_child(node: Node, source_file: Node) -> Node {
    let last_child: Cell<Node> = Cell::new(Node::NIL);

    let visit_node = |n: Node, _v: &mut NodeVisitor<'_, ()>| -> Node {
        if n.is_some() && !n.flags().intersects(NodeFlags::REPARSED) {
            last_child.set(n);
        }
        n
    };
    let visit_node_list = |node_list: NodeList, _v: &mut NodeVisitor<'_, ()>| -> NodeList {
        if node_list.is_some() && node_list.nodes().len() > 0 {
            let nodes = node_list.nodes();
            for i in (0..nodes.len()).rev() {
                if !nodes.get(i).flags().intersects(NodeFlags::REPARSED) {
                    last_child.set(nodes.get(i));
                    break;
                }
            }
        }
        node_list
    };

    astnav::visit_each_child_and_js_doc(
        node,
        source_file,
        Some(&visit_node),
        Some(&visit_node_list),
    );
    last_child.get()
}

// Go: ls/lsutil/children.go:85 GetFirstToken
pub fn get_first_token(node: Node, source_file: Node) -> Node {
    if is_identifier(node) || is_token_kind(node.kind()) {
        return Node::NIL;
    }
    assert_has_real_position(node);
    let mut first_child = Node::NIL;
    node.for_each_child(|n: Node| -> bool {
        // PORT: Go tests `node.Flags` (the parent), not `n.Flags`; kept as is.
        if n.is_nil() || node.flags().intersects(NodeFlags::REPARSED) {
            return false;
        }
        first_child = n;
        true
    });

    let token_end_position = if first_child.is_some() {
        first_child.pos()
    } else {
        node.end()
    };
    let scanner = scanner_ls::get_scanner_for_source_file(source_file, node.pos());
    let mut first_token = Node::NIL;
    if node.pos() < token_end_position {
        let token_kind = scanner.token();
        let token_full_start = scanner.token_full_start();
        let token_end = scanner.token_end();
        first_token = source_file_get_or_create_token(
            source_file,
            token_kind,
            token_full_start,
            token_end,
            node,
            scanner.token_flags(),
        );
    }

    if first_token.is_some() {
        return first_token;
    }
    if first_child.is_nil() {
        return Node::NIL;
    }
    if (first_child.kind() as u16) < (SyntaxKind::FIRST_NODE as u16) {
        return first_child;
    }
    get_first_token(first_child, source_file)
}

// Go: ls/lsutil/children.go:126 AssertHasRealPosition
pub fn assert_has_real_position(node: Node) {
    if position_is_synthesized(node.pos()) || position_is_synthesized(node.end()) {
        crate::core::go_panic("Node must have a real position for this operation.".to_string());
    }
}
