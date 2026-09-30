//! Port of Go `astnav/tokens.go`.
//!
//! PORT: Go closures that update captured locals become closures over
//! `Cell`/`RefCell` locals, because `ast::NodeVisitor` hooks are `Fn`.
//! Recursive Go closures (`find`) become nested `fn`s that take the captured
//! values as parameters. Scanning uses the literal Go scanner through
//! `scanner_ls::get_scanner_for_source_file`.

use crate::astnav::prelude::*;
use crate::frontend::core_binarysearch::binary_search_unique_func;
use crate::frontend::scanner::Scanner;
use crate::frontend::scanner::scanner_ls;
use std::cell::Cell;

// Go: astnav/tokens.go:11 shouldRescanLessThanLessThanToken
fn should_rescan_less_than_less_than_token(
    s: &Scanner,
    containing_node: Node,
    token: SyntaxKind,
) -> bool {
    token == SyntaxKind::LessThanLessThanToken && is_jsx_child(containing_node)
}

// Go: astnav/tokens.go:15 scanNavigationToken
fn scan_navigation_token(s: &mut Scanner, containing_node: Node) -> SyntaxKind {
    let token = s.token();
    if should_rescan_less_than_less_than_token(s, containing_node, token) {
        return s.re_scan_jsx_token(true /*allowMultilineJsxText*/);
    }
    token
}

// Go: astnav/tokens.go:23 GetTouchingPropertyName
pub fn get_touching_property_name(source_file: Node, position: i32) -> Node {
    get_token_at_position_unexported(
        source_file,
        position,
        false, /*allowPositionInLeadingTrivia*/
        Some(&|node: Node| -> bool {
            is_property_name_literal(node)
                || is_keyword_kind(node.kind())
                || is_private_identifier(node)
        }),
    )
}

// Go: astnav/tokens.go:29 GetTouchingToken
pub fn get_touching_token(source_file: Node, position: i32) -> Node {
    get_token_at_position_unexported(
        source_file,
        position,
        false, /*allowPositionInLeadingTrivia*/
        None,
    )
}

// Go: astnav/tokens.go:33 GetTokenAtPosition
pub fn get_token_at_position(source_file: Node, position: i32) -> Node {
    get_token_at_position_unexported(
        source_file,
        position,
        true, /*allowPositionInLeadingTrivia*/
        None,
    )
}

/// Go `core.BinarySearchUniqueFunc` over a `NodeSlice`, read in place with
/// `NodeSlice::get`. Same steps and result as `binary_search_unique_func`.
fn binary_search_node_slice(x: NodeSlice, mut cmp: impl FnMut(i32, Node) -> i32) -> (i32, bool) {
    let n = x.len() as i32;
    if n == 0 {
        return (0, false);
    }
    let (mut low, mut high) = (0i32, n - 1);
    while low <= high {
        let middle = low + ((high - low) >> 1);
        let value = cmp(middle, x.get(middle as usize));
        if value < 0 {
            low = middle + 1;
        } else if value > 0 {
            high = middle - 1;
        } else {
            return (middle, true);
        }
    }
    (low, false)
}

// PORT: Go `getTokenAtPosition` has the same snake name as the exported
// `GetTokenAtPosition`. The exported one keeps the plain name because other
// packages call it; this private one gets the `_unexported` suffix.
// Go: astnav/tokens.go:37 getTokenAtPosition
fn get_token_at_position_unexported(
    source_file: Node,
    position: i32,
    allow_position_in_leading_trivia: bool,
    include_preceding_token_at_end_position: Option<&dyn Fn(Node) -> bool>,
) -> Node {
    // getTokenAtPosition returns a token at the given position in the source file.
    // The token can be a real node in the AST, or a synthesized token constructed
    // with information from the scanner. Synthesized tokens are only created when
    // needed, and they are stored in the source file's token cache such that multiple
    // calls to getTokenAtPosition with the same position will return the same object
    // in memory. If there is no token at the given position (possible when
    // `allowPositionInLeadingTrivia` is false), the lowest node that encloses the
    // position is returned.

    // `next` tracks the node whose children will be visited on the next iteration.
    // `prevSubtree` is a node whose end position is equal to the target position,
    // only if `includePrecedingTokenAtEndPosition` is provided. Once set, the next
    // iteration of the loop will test the rightmost token of `prevSubtree` to see
    // if it should be returned.
    let next: Cell<Node> = Cell::new(Node::NIL);
    let prev_subtree: Cell<Node> = Cell::new(Node::NIL);
    let mut current = source_file;
    // `left` tracks the lower boundary of the node/token that could be returned,
    // and is eventually the scanner's start position, if the scanner is used.
    let left: Cell<i32> = Cell::new(0);
    // `nodeAfterLeft` tracks the first node we visit after visiting the node that advances `left`.
    // When scanning in between nodes for token, we should only scan up to the start of `nodeAfterLeft`.
    let node_after_left: Cell<Node> = Cell::new(Node::NIL);

    let get_included_preceding_token = |subtree: Node| -> Node {
        let child =
            find_preceding_token_ex(source_file, position, subtree, false /*excludeJSDoc*/);
        // PORT: Go calls this only when the callback is not nil.
        let include = include_preceding_token_at_end_position
            .expect("includePrecedingTokenAtEndPosition is nil");
        if child.is_some() && child.end() == position && include(child) {
            return child;
        }
        Node::NIL
    };

    let test_node = |node: Node| -> i32 {
        if node.kind() != SyntaxKind::EndOfFile
            && node.end() == position
            && include_preceding_token_at_end_position.is_some()
            && !node.flags().intersects(NodeFlags::REPARSED)
        {
            if prev_subtree.get().is_some()
                && get_included_preceding_token(prev_subtree.get()).is_some()
            {
                return 0;
            }
            prev_subtree.set(node);
        }

        // A node "contains" the position if position < end, except nodes at the file end
        // treat end as inclusive (there's nowhere else to look). This applies to the EOF
        // token itself, and to JSDoc nodes reaching EOF (e.g. unterminated JSDoc comments).
        if node.end() < position
            || (node.end() == position
                && node.kind() != SyntaxKind::EndOfFile
                && (!is_js_doc_kind(node.kind())
                    || node.end() != source_file.end_of_file_token().end()))
        {
            return -1;
        }
        let node_pos = get_position(node, source_file, allow_position_in_leading_trivia);
        if node_pos > position {
            return 1;
        }
        0
    };

    // We zero in on the node that contains the target position by visiting each
    // child and JSDoc comment of the current node. Node children are walked in
    // order, while node lists are binary searched.
    let visit_node = |node: Node, _v: &mut NodeVisitor<'_, ()>| -> Node {
        // We can't abort visiting children, so once a match is found, we set `next`
        // and do nothing on subsequent visits.
        if node.is_nil() || node.flags().intersects(NodeFlags::REPARSED) {
            return Node::NIL;
        }
        if node_after_left.get().is_nil() {
            node_after_left.set(node);
        }
        if next.get().is_nil() {
            let result = test_node(node);
            match result {
                -1 => {
                    if !is_js_doc_kind(node.kind()) {
                        // We can't move the left boundary into or beyond JSDoc,
                        // because we may end up returning the token after this JSDoc,
                        // constructing it with the scanner, and we need to include
                        // all its leading trivia in its position.
                        left.set(node.end());
                    }
                    node_after_left.set(Node::NIL);
                }
                0 => {
                    next.set(node);
                }
                _ => {}
            }
        }
        node
    };

    let visit_node_list = |node_list: NodeList, _v: &mut NodeVisitor<'_, ()>| -> NodeList {
        if node_list.is_nil() || node_list.nodes().len() == 0 {
            return node_list;
        }
        if node_after_left.get().is_nil() {
            for node in node_list.nodes() {
                if !node.flags().intersects(NodeFlags::REPARSED) {
                    node_after_left.set(node);
                    break;
                }
            }
        }
        if next.get().is_nil() {
            if node_list.end() == position && include_preceding_token_at_end_position.is_some() {
                left.set(node_list.end());
                node_after_left.set(Node::NIL);
                let list_nodes = node_list.nodes();
                for i in (0..list_nodes.len()).rev() {
                    if !list_nodes.get(i).flags().intersects(NodeFlags::REPARSED) {
                        prev_subtree.set(list_nodes.get(i));
                        break;
                    }
                }
            } else if node_list.end() <= position {
                left.set(node_list.end());
                node_after_left.set(Node::NIL);
            } else if node_list.pos() <= position {
                // PERF: search the list in place, like Go `nodes := nodeList.Nodes`.
                // A `Vec` copy here cost one node lookup per list element at
                // each level of descent.
                let nodes = node_list.nodes();
                let (index, match_) =
                    binary_search_node_slice(nodes, |middle: i32, node: Node| -> i32 {
                        if node.flags().intersects(NodeFlags::REPARSED) {
                            return 0;
                        }
                        let cmp = test_node(node);
                        if cmp < 0 {
                            left.set(node.end());
                            node_after_left.set(Node::NIL);
                            for i in (middle + 1) as usize..nodes.len() {
                                let after = nodes.get(i);
                                if !after.flags().intersects(NodeFlags::REPARSED) {
                                    node_after_left.set(after);
                                    break;
                                }
                            }
                        }
                        cmp
                    });
                if match_
                    && nodes
                        .get(index as usize)
                        .flags()
                        .intersects(NodeFlags::REPARSED)
                {
                    // filter and search again
                    // PORT: only this path collects a `Vec`, like Go `core.Filter`.
                    let filtered: Vec<Node> = nodes
                        .iter()
                        .filter(|node| !node.flags().intersects(NodeFlags::REPARSED))
                        .collect();
                    let (index, match_) =
                        binary_search_unique_func(&filtered, |middle: i32, node: Node| -> i32 {
                            let cmp = test_node(node);
                            if cmp < 0 {
                                left.set(node.end());
                                if ((middle + 1) as usize) < filtered.len() {
                                    node_after_left.set(filtered[(middle + 1) as usize]);
                                } else {
                                    node_after_left.set(Node::NIL);
                                }
                            }
                            cmp
                        });
                    if match_ {
                        next.set(filtered[index as usize]);
                    }
                } else if match_ {
                    next.set(nodes.get(index as usize));
                }
            }
        }
        node_list
    };

    loop {
        visit_each_child_and_js_doc(
            current,
            source_file,
            Some(&visit_node),
            Some(&visit_node_list),
        );
        // If prevSubtree was set on the last iteration, it ends at the target position.
        // Check if the rightmost token of prevSubtree should be returned based on the
        // `includePrecedingTokenAtEndPosition` callback.
        if prev_subtree.get().is_some() {
            let child = get_included_preceding_token(prev_subtree.get());
            if child.is_some() {
                // Optimization: includePrecedingTokenAtEndPosition only ever returns true
                // for real AST nodes, so we don't run the scanner here.
                return child;
            }
            prev_subtree.set(Node::NIL);
        }

        // No node was found that contains the target position, so we've gone as deep as
        // we can in the AST. We've either found a token, or we need to run the scanner
        // to construct one that isn't stored in the AST.
        if next.get().is_nil() {
            if is_token_kind(current.kind()) || should_skip_child(current) {
                return current;
            }
            let sf_text = source_file_text(source_file);
            let mut scanner =
                scanner_ls::get_scanner_for_source_file(source_file, &sf_text, left.get());
            let mut end = current.end();
            // We should only scan up to the start of the next node in the AST after the node ending at position `left`.
            // It is necessary to enforce this invariant in cases where `position` occurs in between two node/tokens,
            // such that we would not find a token in the loop below before we reach the next node.
            // We can fall into this case when `allowPositionInLeadingTrivia` is false and `position` is in a leading trivia,
            // or when `position` would be in the leading trivia of a node but this node is inside JSDoc:
            // ```
            // /**
            //  * @type {{
            //  */*$*/ identifier: boolean;
            //  * }}
            //  */
            // ```
            // The position of marker '$' falls in between the asterisk token and the identifier token, but is not
            // part of the leading trivia for `identifier`.
            if node_after_left.get().is_some() {
                end = node_after_left.get().pos();
            }
            while left.get() < end {
                let token = scan_navigation_token(&mut scanner, current);
                let token_full_start = scanner.token_full_start();
                let token_start = if allow_position_in_leading_trivia {
                    token_full_start
                } else {
                    scanner.token_start()
                };
                let token_end = scanner.token_end();
                let flags = scanner.token_flags();
                if token_end > end {
                    break;
                }
                if token_start <= position && (position < token_end) {
                    if token == SyntaxKind::Identifier || !is_token_kind(token) {
                        if is_js_doc_kind(current.kind()) {
                            return current;
                        }
                        // PORT: Go `Kind.String()` prints "KindX"; this prints the
                        // Rust `Debug` name. Panic text only.
                        panic!(
                            "did not expect {:?} to have {:?} in its trivia",
                            current.kind(),
                            token
                        );
                    }
                    return source_file_get_or_create_token(
                        source_file,
                        token,
                        token_full_start,
                        token_end,
                        current,
                        flags,
                    );
                }
                if let Some(include) = include_preceding_token_at_end_position {
                    if token_end == position {
                        let prev_token = source_file_get_or_create_token(
                            source_file,
                            token,
                            token_full_start,
                            token_end,
                            current,
                            flags,
                        );
                        if include(prev_token) {
                            return prev_token;
                        }
                    }
                }
                left.set(token_end);
                scanner.scan();
            }
            return current;
        }
        current = next.get();
        left.set(current.pos());
        node_after_left.set(Node::NIL);
        next.set(Node::NIL);
    }
}

// Go: astnav/tokens.go:265 getPosition
fn get_position(node: Node, source_file: Node, allow_position_in_leading_trivia: bool) -> i32 {
    if allow_position_in_leading_trivia {
        return node.pos();
    }
    get_token_pos_of_node(node, source_file, true /*includeJSDoc*/)
}

// Go: astnav/tokens.go:272 findRightmostNode
fn find_rightmost_node(node: Node) -> Node {
    let next: Cell<Node> = Cell::new(Node::NIL);
    let mut current = node;
    let visit_node = |node: Node, _v: &mut NodeVisitor<'_, ()>| -> Node {
        if node.is_some() {
            next.set(node);
        }
        node
    };
    let visit_nodes = |node_list: NodeList, _visitor: &mut NodeVisitor<'_, ()>| -> NodeList {
        if node_list.is_some() {
            let rightmost = find_last_visible_node(&node_list.nodes().to_vec());
            if rightmost.is_some() {
                next.set(rightmost);
            }
        }
        node_list
    };
    let mut visitor = get_node_visitor(Some(&visit_node), Some(&visit_nodes));

    loop {
        current.visit_each_child(&mut visitor);
        if next.get().is_nil() {
            return current;
        }
        current = next.get();
        next.set(Node::NIL);
    }
}

// Go: astnav/tokens.go:301 VisitEachChildAndJSDoc
// PORT: Go `func(*ast.Node, *ast.NodeVisitor) *ast.Node` callbacks (nil
// allowed) are `Option<&dyn Fn>`. Keep callback state in `Cell`/`RefCell`.
pub fn visit_each_child_and_js_doc<'a>(
    node: Node,
    source_file: Node,
    visit_node: Option<&'a dyn Fn(Node, &mut NodeVisitor<'a, ()>) -> Node>,
    visit_nodes: Option<&'a dyn Fn(NodeList, &mut NodeVisitor<'a, ()>) -> NodeList>,
) {
    let mut visitor = get_node_visitor(visit_node, visit_nodes);
    for jsdoc in node.js_doc(source_file) {
        if let Some(hook) = visitor.hooks.visit_node.clone() {
            hook(jsdoc, &mut visitor);
        } else {
            visitor.visit_node(jsdoc);
        }
    }
    node.visit_each_child(&mut visitor);
}

// Go: astnav/tokens.go:319 comparisonLessThan
const COMPARISON_LESS_THAN: i32 = -1;
// Go: astnav/tokens.go:320 comparisonEqualTo
const COMPARISON_EQUAL_TO: i32 = 0;
// Go: astnav/tokens.go:321 comparisonGreaterThan
const COMPARISON_GREATER_THAN: i32 = 1;

// Go: astnav/tokens.go:328 FindPrecedingToken
/// Finds the leftmost token satisfying `position < token.End()`.
/// If the leftmost token satisfying `position < token.End()` is invalid, or if position
/// is in the trivia of that leftmost token,
/// we will find the rightmost valid token with `token.End() <= position`.
pub fn find_preceding_token(source_file: Node, position: i32) -> Node {
    find_preceding_token_ex(source_file, position, Node::NIL, false)
}

// Go: astnav/tokens.go:332 FindPrecedingTokenEx
pub fn find_preceding_token_ex(
    source_file: Node,
    position: i32,
    start_node: Node,
    exclude_js_doc: bool,
) -> Node {
    // Go: the recursive closure `find` (tokens.go:334).
    fn find(n: Node, source_file: Node, position: i32, exclude_js_doc: bool) -> Node {
        if is_non_whitespace_token(n) && n.kind() != SyntaxKind::EndOfFile {
            return n;
        }

        // `foundChild` is the leftmost node that contains the target position.
        // `prevChild` is the last visited child of the current node.
        let found_child: Cell<Node> = Cell::new(Node::NIL);
        let prev_child: Cell<Node> = Cell::new(Node::NIL);
        let visit_node = |node: Node, _v: &mut NodeVisitor<'_, ()>| -> Node {
            // skip synthesized nodes (that will exist now because of jsdoc handling)
            if node.is_nil() || node.flags().intersects(NodeFlags::REPARSED) {
                return node;
            }
            if found_child.get().is_some() {
                // We cannot abort visiting children, so once the desired child is found, we do nothing.
                return node;
            }
            if position < node.end()
                && (prev_child.get().is_nil() || prev_child.get().end() <= position)
            {
                found_child.set(node);
            } else {
                prev_child.set(node);
            }
            node
        };
        let visit_nodes = |node_list: NodeList, _v: &mut NodeVisitor<'_, ()>| -> NodeList {
            if found_child.get().is_some() {
                return node_list;
            }
            if node_list.is_some() && node_list.nodes().len() > 0 {
                let nodes: Vec<Node> = node_list.nodes().to_vec();
                let (index, match_) =
                    binary_search_unique_func(&nodes, |middle: i32, _node: Node| -> i32 {
                        let middle = middle as usize;
                        // synthetic jsdoc nodes should have jsdocNode.End() <= n.Pos()
                        if nodes[middle].flags().intersects(NodeFlags::REPARSED) {
                            return COMPARISON_LESS_THAN;
                        }
                        if position < nodes[middle].end() {
                            if middle == 0 || position >= nodes[middle - 1].end() {
                                return COMPARISON_EQUAL_TO;
                            }
                            return COMPARISON_GREATER_THAN;
                        }
                        COMPARISON_LESS_THAN
                    });

                if match_ {
                    found_child.set(nodes[index as usize]);
                }

                let valid_lookup_index = if match_ {
                    index - 1
                } else {
                    nodes.len() as i32 - 1
                };
                for i in (0..=valid_lookup_index).rev() {
                    if nodes[i as usize].flags().intersects(NodeFlags::REPARSED) {
                        continue;
                    }
                    if prev_child.get().is_nil() {
                        prev_child.set(nodes[i as usize]);
                    }
                }
            }
            node_list
        };
        visit_each_child_and_js_doc(n, source_file, Some(&visit_node), Some(&visit_nodes));

        let found_child = found_child.get();
        if found_child.is_some() {
            // Note that the span of a node's tokens is [getStartOfNode(node, ...), node.end).
            // Given that `position < child.end` and child has constituent tokens, we distinguish these cases:
            // 1) `position` precedes `child`'s tokens or `child` has no tokens (ie: in a comment or whitespace preceding `child`):
            // we need to find the last token in a previous child node or child tokens.
            // 2) `position` is within the same span: we recurse on `child`.
            let start = get_start_of_node(
                found_child,
                source_file,
                !exclude_js_doc, /*includeJSDoc*/
            );
            let look_in_previous_child = start >= position // cursor in the leading trivia or preceding tokens
                || !is_valid_preceding_node(found_child, source_file);
            if look_in_previous_child {
                if position >= found_child.pos() {
                    // Find jsdoc preceding the foundChild.
                    let mut js_doc = Node::NIL;
                    let node_js_doc = n.js_doc(source_file);
                    for i in (0..node_js_doc.len()).rev() {
                        if node_js_doc.get(i).pos() >= found_child.pos() {
                            js_doc = node_js_doc.get(i);
                            break;
                        }
                    }
                    if js_doc.is_some() {
                        if !exclude_js_doc && position < js_doc.end() {
                            return find(js_doc, source_file, position, exclude_js_doc);
                        } else {
                            return find_rightmost_valid_token(
                                js_doc.end(),
                                source_file,
                                n,
                                position,
                                exclude_js_doc,
                            );
                        }
                    }
                    return find_rightmost_valid_token(
                        found_child.pos(),
                        source_file,
                        n,
                        -1, /*position*/
                        exclude_js_doc,
                    );
                } else {
                    // Answer is in tokens between two visited children.
                    return find_rightmost_valid_token(
                        found_child.pos(),
                        source_file,
                        n,
                        position,
                        exclude_js_doc,
                    );
                }
            } else {
                // position is in [foundChild.getStart(), foundChild.End): recur.
                return find(found_child, source_file, position, exclude_js_doc);
            }
        }

        // We have two cases here: either the position is at the end of the file,
        // or the desired token is in the unvisited trailing tokens of the current node.
        if position >= n.end() {
            find_rightmost_valid_token(
                n.end(),
                source_file,
                n,
                -1, /*position*/
                exclude_js_doc,
            )
        } else {
            find_rightmost_valid_token(n.end(), source_file, n, position, exclude_js_doc)
        }
    }

    let node = if start_node.is_some() {
        start_node
    } else {
        source_file
    };
    let result = find(node, source_file, position, exclude_js_doc);
    if result.is_some() && is_whitespace_only_jsx_text(result) {
        panic!("Expected result to be a non-whitespace token.");
    }
    result
}

// Go: astnav/tokens.go:454 isValidPrecedingNode
fn is_valid_preceding_node(node: Node, source_file: Node) -> bool {
    if node.kind() == SyntaxKind::EndOfFile {
        return node.js_doc(source_file).len() > 0;
    }
    let start = get_start_of_node(node, source_file, false /*includeJSDoc*/);
    let width = node.end() - start;
    !(is_whitespace_only_jsx_text(node) || width == 0)
}

// Go: astnav/tokens.go:463 GetStartOfNode
pub fn get_start_of_node(node: Node, file: Node, include_js_doc: bool) -> i32 {
    get_token_pos_of_node(node, file, include_js_doc)
}

// Go: astnav/tokens.go:469 findRightmostValidToken
/// Looks for rightmost valid token in the range [startPos, endPos).
/// If position is >= 0, looks for rightmost valid token that precedes or touches that position.
fn find_rightmost_valid_token(
    end_pos: i32,
    source_file: Node,
    containing_node: Node,
    position: i32,
    exclude_js_doc: bool,
) -> Node {
    let mut position = position;
    if position == -1 {
        position = containing_node.end();
    }

    // Go: the recursive closure `find` (tokens.go:474).
    fn find(
        n: Node,
        end_pos: i32,
        source_file: Node,
        containing_node: Node,
        position: i32,
        exclude_js_doc: bool,
    ) -> Node {
        if n.is_nil() {
            return Node::NIL;
        }
        if is_non_whitespace_token(n) {
            return n;
        }

        let rightmost_valid_node: Cell<Node> = Cell::new(Node::NIL);
        // Nodes after the last valid node.
        let rightmost_visited_nodes: RefCell<Vec<Node>> = RefCell::new(Vec::with_capacity(1));
        let has_children: Cell<bool> = Cell::new(false);
        let should_visit_node = |node: Node| -> bool {
            // Node is synthetic or out of the desired range: don't visit it.
            !(node.flags().intersects(NodeFlags::REPARSED)
                || node.end() > end_pos
                || get_start_of_node(node, source_file, !exclude_js_doc /*includeJSDoc*/)
                    >= position)
        };
        let visit_node = |node: Node, _v: &mut NodeVisitor<'_, ()>| -> Node {
            if node.is_nil() || node.flags().intersects(NodeFlags::REPARSED) {
                return node;
            }
            has_children.set(true);
            if !should_visit_node(node) {
                return node;
            }
            rightmost_visited_nodes.borrow_mut().push(node);
            if is_valid_preceding_node(node, source_file) {
                rightmost_valid_node.set(node);
                rightmost_visited_nodes.borrow_mut().clear();
            }
            node
        };
        let visit_nodes = |node_list: NodeList, _v: &mut NodeVisitor<'_, ()>| -> NodeList {
            if node_list.is_some() && node_list.nodes().len() > 0 {
                has_children.set(true);
                let nodes: Vec<Node> = node_list.nodes().to_vec();
                let (index, _) =
                    binary_search_unique_func(&nodes, |_middle: i32, node: Node| -> i32 {
                        if node.end() > end_pos {
                            return COMPARISON_GREATER_THAN;
                        }
                        COMPARISON_LESS_THAN
                    });
                let mut valid_index: i32 = -1;
                for i in (0..index).rev() {
                    if !should_visit_node(nodes[i as usize]) {
                        continue;
                    }
                    if is_valid_preceding_node(nodes[i as usize], source_file) {
                        valid_index = i;
                        rightmost_valid_node.set(nodes[i as usize]);
                        break;
                    }
                }
                for i in (valid_index + 1)..index {
                    if !should_visit_node(nodes[i as usize]) {
                        continue;
                    }
                    rightmost_visited_nodes.borrow_mut().push(nodes[i as usize]);
                }
            }
            node_list
        };
        visit_each_child_and_js_doc(n, source_file, Some(&visit_node), Some(&visit_nodes));
        let rightmost_valid_node = rightmost_valid_node.get();
        let rightmost_visited_nodes: Vec<Node> = rightmost_visited_nodes.take();

        // Three cases:
        // 1. The answer is a token of `rightmostValidNode`.
        // 2. The answer is one of the unvisited tokens that occur after the rightmost valid node.
        // 3. The current node is a childless, token-less node. The answer is the current node.

        // Case 2: Look at unvisited trailing tokens that occur in between the rightmost visited nodes.
        if !should_skip_child(n) {
            // JSDoc nodes don't include trivia tokens as children.
            let mut start_pos = if rightmost_valid_node.is_some() {
                rightmost_valid_node.end()
            } else {
                n.pos()
            };
            let sf_text = source_file_text(source_file);
            let mut scanner =
                scanner_ls::get_scanner_for_source_file(source_file, &sf_text, start_pos);
            let mut tokens: Vec<Node> = Vec::new();
            for visited_node in rightmost_visited_nodes.iter().copied() {
                // Trailing tokens that occur before this node.
                while start_pos < visited_node.pos().min(position) {
                    let token = scan_navigation_token(&mut scanner, n);
                    let token_start = scanner.token_start();
                    if token_start >= visited_node.pos().min(position) {
                        break;
                    }
                    let token_full_start = scanner.token_full_start();
                    let token_end = scanner.token_end();
                    start_pos = token_end;
                    let flags = scanner.token_flags();
                    tokens.push(source_file_get_or_create_token(
                        source_file,
                        token,
                        token_full_start,
                        token_end,
                        n,
                        flags,
                    ));
                    scanner.scan();
                }
                start_pos = visited_node.end();
                scanner.reset_pos(start_pos);
                scanner.scan();
            }
            // Trailing tokens after last visited node.
            while start_pos < end_pos.min(position) {
                let token = scan_navigation_token(&mut scanner, n);
                let token_start = scanner.token_start();
                if token_start >= end_pos.min(position) {
                    break;
                }
                let token_full_start = scanner.token_full_start();
                let token_end = scanner.token_end();
                start_pos = token_end;
                let flags = scanner.token_flags();
                tokens.push(source_file_get_or_create_token(
                    source_file,
                    token,
                    token_full_start,
                    token_end,
                    n,
                    flags,
                ));
                scanner.scan();
            }

            let last_token = tokens.len() as i32 - 1;
            // Find preceding valid token.
            for i in (0..=last_token).rev() {
                if !is_whitespace_only_jsx_text(tokens[i as usize]) {
                    return tokens[i as usize];
                }
            }
        }

        // Case 3: childless node.
        if !has_children.get() {
            if n != containing_node {
                return n;
            }
            return Node::NIL;
        }
        // Case 1: recur on rightmostValidNode.
        let mut end_pos = end_pos;
        if rightmost_valid_node.is_some() {
            end_pos = rightmost_valid_node.end();
        }
        find(
            rightmost_valid_node,
            end_pos,
            source_file,
            containing_node,
            position,
            exclude_js_doc,
        )
    }

    find(
        containing_node,
        end_pos,
        source_file,
        containing_node,
        position,
        exclude_js_doc,
    )
}

// Go: astnav/tokens.go:611 FindNextToken
pub fn find_next_token(previous_token: Node, parent: Node, file: Node) -> Node {
    // Go: the recursive closure `find` (tokens.go:613).
    fn find(n: Node, previous_token: Node, file: Node) -> Node {
        if is_token_kind(n.kind()) && n.pos() == previous_token.end() {
            // this is token that starts at the end of previous token - return it
            return n;
        }
        // Node that contains `previousToken` or occurs immediately after it.
        let found_node: Cell<Node> = Cell::new(Node::NIL);
        let visit_node = |node: Node, _v: &mut NodeVisitor<'_, ()>| -> Node {
            if node.is_some()
                && !node.flags().intersects(NodeFlags::REPARSED)
                && node.pos() <= previous_token.end()
                && node.end() > previous_token.end()
            {
                found_node.set(node);
            }
            node
        };
        let visit_nodes = |node_list: NodeList, _v: &mut NodeVisitor<'_, ()>| -> NodeList {
            if node_list.is_some() && node_list.nodes().len() > 0 && found_node.get().is_nil() {
                let nodes: Vec<Node> = node_list.nodes().to_vec();
                let (index, match_) =
                    binary_search_unique_func(&nodes, |_middle: i32, node: Node| -> i32 {
                        if node.flags().intersects(NodeFlags::REPARSED) {
                            return COMPARISON_LESS_THAN;
                        }
                        if node.pos() > previous_token.end() {
                            return COMPARISON_GREATER_THAN;
                        }
                        if node.end() <= previous_token.pos() {
                            return COMPARISON_LESS_THAN;
                        }
                        COMPARISON_EQUAL_TO
                    });
                if match_ {
                    found_node.set(nodes[index as usize]);
                }
            }
            node_list
        };
        visit_each_child_and_js_doc(n, file, Some(&visit_node), Some(&visit_nodes));
        // Cases:
        // 1. no answer exists
        // 2. answer is an unvisited token
        // 3. answer is in the visited found node

        // Case 3: look for the next token inside the found node.
        if found_node.get().is_some() {
            return find(found_node.get(), previous_token, file);
        }
        let start_pos = previous_token.end();
        // Case 2: look for the next token directly.
        if start_pos >= n.pos() && start_pos < n.end() {
            let sf_text = source_file_text(file);
            let scanner = scanner_ls::get_scanner_for_source_file(file, &sf_text, start_pos);
            let token = scanner.token();
            let token_full_start = scanner.token_full_start();
            let token_end = scanner.token_end();
            let flags = scanner.token_flags();
            // Use tokenFullStart (which includes leading trivia) to match TS's
            // findNextToken behavior where `n.pos === previousToken.end` is checked
            // (TS's pos includes trivia, same as Go's Pos()/tokenFullStart).
            if token_full_start == previous_token.end() {
                return source_file_get_or_create_token(
                    file,
                    token,
                    token_full_start,
                    token_end,
                    n,
                    flags,
                );
            }
            // PORT: Go `%s` of `Kind` prints "KindX"; this prints the Rust
            // `Debug` name. Panic text only.
            panic!(
                "Expected to find next token at {}, got token {:?} at {}",
                previous_token.end(),
                token,
                token_full_start
            );
        }
        // Case 3: no answer.
        Node::NIL
    }
    find(parent, previous_token, file)
}

// Go: astnav/tokens.go:680 getNodeVisitor
// PORT: Go `ast.NewNodeVisitor(core.Identity, nil, hooks)`: the visit
// callback is the identity and the factory is the visitor's default one.
fn get_node_visitor<'a>(
    visit_node: Option<&'a dyn Fn(Node, &mut NodeVisitor<'a, ()>) -> Node>,
    visit_nodes: Option<&'a dyn Fn(NodeList, &mut NodeVisitor<'a, ()>) -> NodeList>,
) -> NodeVisitor<'a, ()> {
    let mut wrapped_visit_node: Option<VisitNodeHook<'a, ()>> = None;
    let mut wrapped_visit_nodes: Option<VisitNodesHook<'a, ()>> = None;
    if let Some(visit_node) = visit_node {
        wrapped_visit_node = Some(Rc::new(
            move |n: Node, v: &mut NodeVisitor<'a, ()>| -> Node {
                if is_js_doc_single_comment_node_comment(n) {
                    return n;
                }
                visit_node(n, v)
            },
        ));
    }

    if let Some(visit_nodes) = visit_nodes {
        wrapped_visit_nodes = Some(Rc::new(
            move |n: NodeList, v: &mut NodeVisitor<'a, ()>| -> NodeList {
                if is_js_doc_single_comment_node_list(n) {
                    return n;
                }
                visit_nodes(n, v)
            },
        ));
    }

    let wrapped_visit_nodes_for_modifiers = wrapped_visit_nodes.clone();
    let visit_modifiers: VisitModifiersHook<'a, ()> = Rc::new(
        move |modifiers: ModifierList, visitor: &mut NodeVisitor<'a, ()>| -> ModifierList {
            if modifiers.is_some() {
                // PORT: Go calls a nil `wrappedVisitNodes` here and panics.
                let wrapped_visit_nodes = wrapped_visit_nodes_for_modifiers
                    .as_ref()
                    .expect("wrappedVisitNodes is nil");
                wrapped_visit_nodes(modifiers.node_list(), visitor);
            }
            modifiers
        },
    );

    new_node_visitor(
        |node: Node, _v: &mut NodeVisitor<'a, ()>| -> Node { node }, /*core.Identity*/
        None,
        NodeVisitorHooks {
            visit_node: wrapped_visit_node.clone(),
            visit_token: wrapped_visit_node,
            visit_nodes: wrapped_visit_nodes,
            visit_modifiers: Some(visit_modifiers),
            ..NodeVisitorHooks::default()
        },
        (),
    )
}

// Go: astnav/tokens.go:717 shouldSkipChild
fn should_skip_child(node: Node) -> bool {
    node.kind() == SyntaxKind::JsDoc
        || node.kind() == SyntaxKind::JsDocText
        || node.kind() == SyntaxKind::JsDocTypeLiteral
        || node.kind() == SyntaxKind::JsDocSignature
        || is_js_doc_link_like(node)
        || is_js_doc_tag(node)
}

// Go: astnav/tokens.go:728 FindChildOfKind
/// FindChildOfKind searches for a child node or token of the specified kind within a containing node.
/// This function scans through both AST nodes and intervening tokens to find the first match.
pub fn find_child_of_kind(containing_node: Node, kind: SyntaxKind, source_file: Node) -> Node {
    let mut last_node_pos = containing_node.pos();
    let sf_text = source_file_text(source_file);
    let mut scan = scanner_ls::get_scanner_for_source_file(source_file, &sf_text, last_node_pos);

    let mut found_child = Node::NIL;
    let mut visit_node = |node: Node| -> bool {
        if node.is_nil() || node.flags().intersects(NodeFlags::REPARSED) {
            return false;
        }
        // Look for child in preceding tokens.
        let mut start_pos = last_node_pos;
        while start_pos < node.pos() {
            let token_kind = scan.token();
            let token_end = scan.token_end();
            if token_kind == kind {
                let token_full_start = scan.token_full_start();
                let flags = scan.token_flags();
                found_child = source_file_get_or_create_token(
                    source_file,
                    token_kind,
                    token_full_start,
                    token_end,
                    containing_node,
                    flags,
                );
                return true;
            }
            start_pos = token_end;
            scan.scan();
        }

        if node.kind() == kind {
            found_child = node;
            return true;
        }

        last_node_pos = node.end();
        scan.reset_pos(last_node_pos);
        false
    };

    for_each_child_and_js_doc(containing_node, source_file, &mut visit_node);

    if found_child.is_some() {
        return found_child;
    }

    // Look for child in trailing tokens.
    let mut start_pos = last_node_pos;
    while start_pos < containing_node.end() {
        let token_kind = scan.token();
        let token_end = scan.token_end();
        if token_kind == kind {
            let token_full_start = scan.token_full_start();
            let flags = scan.token_flags();
            let token = source_file_get_or_create_token(
                source_file,
                token_kind,
                token_full_start,
                token_end,
                containing_node,
                flags,
            );
            return token;
        }
        start_pos = token_end;
        scan.scan();
    }
    Node::NIL
}
