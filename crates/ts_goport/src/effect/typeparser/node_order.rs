//! PORT: not in Effect-TS/tsgo. Each Go rule walks the whole source file
//! with `ForEachChild`, so a file is walked about 20 to 50 times (one walk
//! per enabled rule, plus the type parser's per-file walks). `NodeOrder`
//! keeps the nodes of one file in that walk's order, built with one walk,
//! and the rules read it in their own turn (`TypeParser::node_order`).
//!
//! A rule that reads it still runs alone, in `rules::ALL` order, and visits
//! the same nodes in the same order as its Go walk. So its checker and type
//! parser queries keep effect-tsgo's order (effperf2 item 1; effperf0 F4
//! interleaved the rules and was not taken).

use crate::effect::typeparser::TypeParser;
use crate::prelude::*;

/// The nodes of one subtree in Go `ForEachChild` pre-order (no JSDoc): the
/// root at index 0, then each child's subtree in child order. `end[i]` is
/// the index after the subtree of node `i`.
pub struct NodeOrder {
    nodes: Vec<Node>,
    end: Vec<u32>,
}

/// The index of a node that `NodeOrder::index_under` did not find.
pub const NO_INDEX: u32 = u32::MAX;

/// What `NodeOrder::walk_preorder` does after a node.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Walk {
    /// Visit the node's children next (Go: the walk calls `ForEachChild`).
    Descend,
    /// Do not visit the node's children (Go: the walk returns first).
    SkipChildren,
    /// End the walk (Go: `true` returned through every `ForEachChild`).
    Stop,
}

impl NodeOrder {
    /// The order of `root` and its subtree, from one `for_each_child` walk.
    #[must_use]
    pub fn build(root: Node) -> Self {
        fn visit(n: Node, nodes: &mut Vec<Node>, end: &mut Vec<u32>) {
            let i = nodes.len();
            nodes.push(n);
            end.push(0);
            n.for_each_child(|child| {
                visit(child, nodes, end);
                false
            });
            end[i] = u32::try_from(nodes.len()).expect("node count fits u32");
        }
        let mut order = NodeOrder {
            nodes: Vec::new(),
            end: Vec::new(),
        };
        if root.is_some() {
            visit(root, &mut order.nodes, &mut order.end);
        }
        order
    }

    /// The root node (Node::NIL for an empty order).
    #[must_use]
    pub fn root(&self) -> Node {
        self.nodes.first().copied().unwrap_or(Node::NIL)
    }

    /// Every node in pre-order, the root first.
    #[must_use]
    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    /// The node at index `i`.
    #[must_use]
    pub fn node(&self, i: u32) -> Node {
        self.nodes[i as usize]
    }

    /// The indexes of the children of node `i`, in `for_each_child` order.
    pub fn children(&self, i: u32) -> impl Iterator<Item = u32> + '_ {
        let end = self.end[i as usize];
        let mut next = i + 1;
        std::iter::from_fn(move || {
            (next < end).then(|| {
                let child = next;
                next = self.end[child as usize];
                child
            })
        })
    }

    /// The index of `n` in the subtree of node `i` (`i` included): a child
    /// first, then any node under `i`. `NO_INDEX` when `i` is `NO_INDEX` or
    /// `n` is not there. For the work lists that push nodes under the node
    /// they handle.
    #[must_use]
    pub fn index_under(&self, i: u32, n: Node) -> u32 {
        if i == NO_INDEX || n.is_nil() {
            return NO_INDEX;
        }
        if self.nodes[i as usize] == n {
            return i;
        }
        self.children(i)
            .find(|&c| self.nodes[c as usize] == n)
            .or_else(|| (i + 1..self.end[i as usize]).find(|&c| self.nodes[c as usize] == n))
            .unwrap_or(NO_INDEX)
    }

    /// Calls `f` with each child of `node` and the child's index, in
    /// `for_each_child` order. `i` is the index of `node`; when it is
    /// `NO_INDEX`, the children come from `for_each_child`, with index
    /// `NO_INDEX`.
    pub fn for_each_child_of(&self, i: u32, node: Node, mut f: impl FnMut(Node, u32)) {
        if i == NO_INDEX {
            node.for_each_child(|child| {
                f(child, NO_INDEX);
                false
            });
        } else {
            for child in self.children(i) {
                f(self.nodes[child as usize], child);
            }
        }
    }

    /// Go's recursive rule walk from the root: `f` sees each node in
    /// pre-order and says whether to visit its children.
    pub fn walk_preorder(&self, mut f: impl FnMut(Node) -> Walk) {
        let mut i = 0;
        while i < self.nodes.len() {
            match f(self.nodes[i]) {
                Walk::Descend => i += 1,
                Walk::SkipChildren => i = self.end[i] as usize,
                Walk::Stop => return,
            }
        }
    }
}

impl TypeParser<'_> {
    /// The node order of `sf`, built at the first call for that file. The
    /// rule runner makes one type parser for each file and drops it at the
    /// end of the file, so the order lives for one file's rules.
    pub fn node_order(&mut self, sf: Node) -> Rc<NodeOrder> {
        match &self.node_order {
            Some(order) if order.root() == sf => order.clone(),
            _ => {
                let order = Rc::new(NodeOrder::build(sf));
                self.node_order = Some(order.clone());
                order
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};

    fn parse(source: &'static str) -> Node {
        let opts = SourceFileParseOptions {
            file_name: "/test.ts".to_string(),
            ..Default::default()
        };
        parse_source_file(&opts, source, ScriptKind::TS).root
    }

    fn walk_nodes(n: Node, out: &mut Vec<Node>) {
        out.push(n);
        n.for_each_child(|c| {
            walk_nodes(c, out);
            false
        });
    }

    #[test]
    fn order_matches_the_recursive_walk() {
        let sf = parse(
            "const a = f(1, [2, 3]);\nclass C<T> extends B { m(x: T) { return x ? g() : h; } }\n",
        );
        let order = NodeOrder::build(sf);
        let mut expect = Vec::new();
        walk_nodes(sf, &mut expect);
        assert_eq!(order.nodes(), &expect[..]);
        for (i, &n) in order.nodes().iter().enumerate() {
            let kids: Vec<Node> = order.children(i as u32).map(|c| order.node(c)).collect();
            let want: Vec<Node> = n.iter_children().collect();
            assert_eq!(kids, want);
        }
    }

    #[test]
    fn walks_keep_the_go_orders() {
        let sf = parse("f(a, g(b));\nlet x = [c, d];\n");
        let order = NodeOrder::build(sf);
        // Pre-order with a skip: the subtree of each call is skipped.
        let mut seen = Vec::new();
        order.walk_preorder(|n| {
            seen.push(n);
            if n.kind() == SyntaxKind::CallExpression {
                Walk::SkipChildren
            } else {
                Walk::Descend
            }
        });
        let mut expect = Vec::new();
        fn rec(n: Node, out: &mut Vec<Node>) {
            out.push(n);
            if n.kind() != SyntaxKind::CallExpression {
                n.for_each_child(|c| {
                    rec(c, out);
                    false
                });
            }
        }
        rec(sf, &mut expect);
        assert_eq!(seen, expect);
        // The stack walk of the rules (`nodeToVisit`), on indexes.
        let mut seen = Vec::new();
        let mut stack: Vec<u32> = order.children(0).collect();
        while let Some(i) = stack.pop() {
            seen.push(order.node(i));
            stack.extend(order.children(i));
        }
        let mut expect = Vec::new();
        let mut stack: Vec<Node> = sf.iter_children().collect();
        while let Some(n) = stack.pop() {
            expect.push(n);
            stack.extend(n.iter_children());
        }
        assert_eq!(seen, expect);
    }

    #[test]
    fn index_under_finds_nodes_of_the_subtree() {
        let sf = parse("a.pipe(f)(b);\nc;\n");
        let order = NodeOrder::build(sf);
        let call = order.node(order.children(0).next().unwrap()).expression();
        let i = order.index_under(0, call);
        assert_eq!(order.node(i), call);
        // A child, a node further down, the node itself.
        let callee = call.expression();
        assert_eq!(order.node(order.index_under(i, callee)), callee);
        let subject = callee.expression().expression();
        assert_eq!(order.node(order.index_under(i, subject)), subject);
        assert_eq!(order.index_under(i, call), i);
        // Not under the node, or no index to start from.
        let other = order.node(order.children(0).nth(1).unwrap());
        assert_eq!(order.index_under(i, other), NO_INDEX);
        assert_eq!(order.index_under(NO_INDEX, callee), NO_INDEX);
        // Children with and without an index.
        let mut with = Vec::new();
        order.for_each_child_of(i, call, |c, ci| with.push((c, order.node(ci))));
        assert!(with.iter().all(|(c, n)| c == n));
        let mut without = Vec::new();
        order.for_each_child_of(NO_INDEX, call, |c, ci| without.push((c, ci)));
        assert_eq!(
            with.iter().map(|w| w.0).collect::<Vec<_>>(),
            without.iter().map(|w| w.0).collect::<Vec<_>>()
        );
        assert!(without.iter().all(|w| w.1 == NO_INDEX));
    }
}
