//! Go `*ast.Node` methods, `NodeList`, `ModifierList`, `core.TextRange`,
//! subtree facts, access kinds and the `ast.SourceFile` accessors from pinned
//! typescript-go `internal/ast/ast.go` (and `internal/core/text.go` for
//! `TextRange`).
//!
//! Go reads the AST without a context. So do we: every method reaches the
//! parsed ts_ast arena through `prog()`. Nodes of a ported-parser file are
//! read from its node store (`ast/store.rs`), and factory nodes from the
//! synthetic arena (`ast/synthetic.rs`).
//!
//! PORT: Go methods that panic with "Unhandled case in Node.X" return nil,
//! an empty list or "" here (PORTING.md "AST"). They also cover every node
//! struct that has the Go field of the same name, because `fields.rs` does not
//! generate accessors for names that clash with Go `Node` methods.
//!
//! PORT: the factories (`New*`), `Clone`, `VisitEachChild`, the printer, the
//! `MutableNode` setters and the `AsFlow*` casts are out of scope.

use crate::prelude::*;
use ts_ast::NodeData;

// ──────────────────────────────────────────────────────────────────────
// Arena helpers
// ──────────────────────────────────────────────────────────────────────

/// The ts_ast id of `n`.
// PORT: `Node::node_id` in core.rs passes a usize to `NodeId::new(u32)`, so
// this file computes the id itself.
fn nid(n: Node) -> ts_ast::NodeId {
    ts_ast::NodeId::new(((n.0 & 0xffff_ffff) - 1) as u32)
}

/// The ts_ast node for `n`. Go dereferences the pointer, so nil panics.
fn raw(n: Node) -> &'static ts_ast::Node {
    assert!(n.is_some(), "nil node dereference");
    if n.file_index() == SYNTHETIC_NODE_FILE {
        return synthetic_ast_node(n);
    }
    if has_file_store(n.file_index()) {
        return store_ast_node(n);
    }
    prog().files[n.file_index()]
        .legacy_source()
        .parse
        .arena
        .get(nid(n))
        .expect("node is not in its file arena")
}

/// The ts_ast data for `n`.
fn data(n: Node) -> &'static NodeData {
    &raw(n).data
}

/// Go `nil` for an optional child.
fn opt(file: usize, id: Option<ts_ast::NodeId>) -> Node {
    match id {
        Some(id) => Node::new(file, id),
        None => Node::NIL,
    }
}

/// A required child.
fn req(file: usize, id: ts_ast::NodeId) -> Node {
    Node::new(file, id)
}

/// A required list.
fn list(file: usize, l: &'static ts_ast::NodeList) -> NodeList {
    NodeList {
        file: file as u32,
        list: Some(l),
    }
}

/// An optional list. `None` is Go `nil`.
fn opt_list(file: usize, l: &'static Option<ts_ast::NodeList>) -> NodeList {
    NodeList {
        file: file as u32,
        list: l.as_ref(),
    }
}

/// An optional modifier list. `None` is Go `nil`.
fn mods(file: usize, m: &'static Option<ts_ast::ModifierList>) -> ModifierList {
    ModifierList {
        file: file as u32,
        list: m.as_ref(),
    }
}

/// Matches `n`'s data against the listed `NodeData` variants. Each variant
/// binds `$d` and evaluates `$e`; other variants give `$def`.
macro_rules! by_data {
    ($n:expr, |$file:ident, $d:ident| $e:expr, [$($v:ident),* $(,)?], $def:expr) => {{
        let node: Node = $n;
        #[allow(unused_variables)]
        let $file = node.file_index();
        match data(node) {
            $(NodeData::$v($d) => $e,)*
            _ => $def,
        }
    }};
}

/// Binder data for nodes of a file that is not bound yet.
static NO_BIND: NodeBindData = NodeBindData {
    symbol: SymbolId::NIL,
    local_symbol: SymbolId::NIL,
    locals: SymbolTable::NIL,
    next_container: Node::NIL,
    flow_node: FlowNodeId::NIL,
    end_flow_node: FlowNodeId::NIL,
    return_flow_node: FlowNodeId::NIL,
    added_flags: NodeFlags::NONE,
};

// ──────────────────────────────────────────────────────────────────────
// core.TextRange (internal/core/text.go)
// ──────────────────────────────────────────────────────────────────────

/// Go `core.TextRange`. Positions are Go positions (UTF-8 byte offsets).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct TextRange {
    pos: i32,
    end: i32,
}

impl TextRange {
    // Go: core/text.go:14 NewTextRange
    #[must_use]
    pub const fn new(pos: i32, end: i32) -> Self {
        Self { pos, end }
    }

    // Go: core/text.go:18 UndefinedTextRange
    #[must_use]
    pub const fn undefined() -> Self {
        Self { pos: -1, end: -1 }
    }

    // Go: core/text.go:22 Pos
    #[must_use]
    pub const fn pos(self) -> i32 {
        self.pos
    }

    // Go: core/text.go:26 End
    #[must_use]
    pub const fn end(self) -> i32 {
        self.end
    }

    // Go: core/text.go:30 Len
    #[must_use]
    pub const fn len(self) -> i32 {
        self.end - self.pos
    }

    // Go: core/text.go:34 IsValid
    #[must_use]
    pub const fn is_valid(self) -> bool {
        self.pos >= 0 || self.end >= 0
    }

    // Go: core/text.go:38 Contains
    #[must_use]
    pub const fn contains(self, pos: i32) -> bool {
        pos >= self.pos && pos < self.end
    }

    // Go: core/text.go:42 ContainsInclusive
    #[must_use]
    pub const fn contains_inclusive(self, pos: i32) -> bool {
        pos >= self.pos && pos <= self.end
    }

    // Go: core/text.go:46 ContainsExclusive
    #[must_use]
    pub const fn contains_exclusive(self, pos: i32) -> bool {
        self.pos < pos && pos < self.end
    }

    // Go: core/text.go:50 WithPos
    #[must_use]
    pub const fn with_pos(self, pos: i32) -> Self {
        Self { pos, end: self.end }
    }

    // Go: core/text.go:54 WithEnd
    #[must_use]
    pub const fn with_end(self, end: i32) -> Self {
        Self { pos: self.pos, end }
    }

    // Go: core/text.go:58 ContainedBy
    #[must_use]
    pub const fn contained_by(self, t2: TextRange) -> bool {
        t2.pos <= self.pos && t2.end >= self.end
    }

    // Go: core/text.go:62 Overlaps
    #[must_use]
    pub fn overlaps(self, t2: TextRange) -> bool {
        let start = self.pos.max(t2.pos);
        let end = self.end.min(t2.end);
        start < end
    }

    // Go: core/text.go:70 Intersects
    /// Like `overlaps`, but touching ranges intersect.
    #[must_use]
    pub fn intersects(self, t2: TextRange) -> bool {
        let start = self.pos.max(t2.pos);
        let end = self.end.min(t2.end);
        start <= end
    }
}

// Go: core/text.go:76 CompareTextRanges
#[must_use]
pub fn compare_text_ranges(r1: TextRange, r2: TextRange) -> i32 {
    let c = r1.pos - r2.pos;
    if c != 0 {
        return c;
    }
    r1.end - r2.end
}

/// A ts_ast range as a Go `core.TextRange`.
fn text_range_of(r: &ts_core::TextRange) -> TextRange {
    TextRange::new(r.start.get() as i32, r.end.get() as i32)
}

/// Go `MappedTypeNode.Members`.
// PORT: Go parseMappedType always parses a member list, which is empty
// unless there are (erroneous) members. The Rust parser stores `None` for
// the empty list. For a parsed mapped type we make one leaked empty list per
// node, placed just before the closing brace like Go's.
fn mapped_type_members(n: Node) -> NodeList {
    let NodeData::MappedTypeNode(d) = data(n) else {
        return NodeList::NIL;
    };
    let f = n.file_index();
    // A ported-parser file keeps the Go list as parsed.
    if d.members.is_some() || has_file_store(f) || prog().files.get(f).is_none() {
        return opt_list(f, &d.members);
    }
    let l = MAPPED_TYPE_MEMBERS.with(|cache| {
        *cache.borrow_mut().entry(n).or_insert_with(|| {
            let close = raw(n).range.end.get().saturating_sub(1);
            let at = ts_core::TextPos::new(close);
            Box::leak(Box::new(ts_ast::NodeList {
                range: ts_core::TextRange::new(at, at),
                nodes: Vec::new(),
                has_trailing_comma: false,
            }))
        })
    });
    list(f, l)
}

/// The Go kind of a parsed node whose ts_ast kind differs from Go.
// PORT: the Rust parser reuses node types where the Go parser makes its own:
// - a PropertyDeclaration in an interface, type literal or mapped type is Go
//   `PropertySignature` (parser.go parsePropertyOrMethodSignature);
// - a QualifiedName in an ExpressionWithTypeArguments is Go
//   `PropertyAccessExpression` (parser.go parseExpressionWithTypeArguments
//   parses a left-hand-side expression);
// - an OmittedExpression in an array binding pattern is Go `BindingElement`
//   with nil fields (parser.go parseArrayBindingElement).
// The data stays the same. The accessors in this file and fields.rs read the
// Go fields from it.
fn go_kind(file: usize, id: ts_ast::NodeId, n: &ts_ast::Node) -> SyntaxKind {
    let Some(f) = prog().files.get(file) else {
        return n.kind;
    };
    let arena = &f.legacy_source().parse.arena;
    let Some(parent_id) = n.parent else {
        return n.kind;
    };
    let Some(parent) = arena.get(parent_id) else {
        return n.kind;
    };
    match n.kind {
        SyntaxKind::PropertyDeclaration
            if matches!(
                parent.kind,
                SyntaxKind::InterfaceDeclaration | SyntaxKind::TypeLiteral | SyntaxKind::MappedType
            ) =>
        {
            SyntaxKind::PropertySignature
        }
        SyntaxKind::QualifiedName => {
            let is_expression = match &parent.data {
                NodeData::ExpressionWithTypeArguments(d) => d.expression == id,
                NodeData::QualifiedName(d) => {
                    d.left == id
                        && go_kind(file, parent_id, parent) == SyntaxKind::PropertyAccessExpression
                }
                _ => false,
            };
            if is_expression {
                SyntaxKind::PropertyAccessExpression
            } else {
                n.kind
            }
        }
        SyntaxKind::OmittedExpression if parent.kind == SyntaxKind::ArrayBindingPattern => {
            SyntaxKind::BindingElement
        }
        k => k,
    }
}

// ──────────────────────────────────────────────────────────────────────
// NodeSlice: Go `[]*Node`
// ──────────────────────────────────────────────────────────────────────

/// Go `[]*Node`. It points either at a ts_ast id list of one file or at a
/// cached slice of `Node`s. The default value is Go `nil`.
#[derive(Clone, Copy, Debug, Default)]
pub struct NodeSlice {
    file: u32,
    ids: &'static [ts_ast::NodeId],
    nodes: &'static [Node],
}

impl NodeSlice {
    /// Go `nil`.
    pub const NIL: Self = Self {
        file: 0,
        ids: &[],
        nodes: &[],
    };

    /// A slice over ts_ast ids in `file`.
    #[must_use]
    pub fn from_ids(file: usize, ids: &'static [ts_ast::NodeId]) -> Self {
        Self {
            file: file as u32,
            ids,
            nodes: &[],
        }
    }

    /// A slice over nodes that live for the program.
    #[must_use]
    pub fn from_nodes(nodes: &'static [Node]) -> Self {
        Self {
            file: 0,
            ids: &[],
            nodes,
        }
    }

    #[must_use]
    pub fn len(self) -> usize {
        self.ids.len() + self.nodes.len()
    }

    #[must_use]
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Go `nodes[i]`. Panics when `i` is out of range, like Go.
    #[must_use]
    pub fn get(self, i: usize) -> Node {
        if self.ids.is_empty() {
            self.nodes[i]
        } else {
            Node::new(self.file as usize, self.ids[i])
        }
    }

    #[must_use]
    pub fn first(self) -> Option<Node> {
        if self.is_empty() {
            None
        } else {
            Some(self.get(0))
        }
    }

    #[must_use]
    pub fn last(self) -> Option<Node> {
        if self.is_empty() {
            None
        } else {
            Some(self.get(self.len() - 1))
        }
    }

    #[must_use]
    pub fn iter(self) -> NodeSliceIter {
        NodeSliceIter {
            slice: self,
            front: 0,
            back: self.len(),
        }
    }

    #[must_use]
    pub fn to_vec(self) -> Vec<Node> {
        self.iter().collect()
    }
}

/// Iterator over a `NodeSlice`. Yields `Node` by value.
#[derive(Clone, Debug)]
pub struct NodeSliceIter {
    slice: NodeSlice,
    front: usize,
    back: usize,
}

impl Iterator for NodeSliceIter {
    type Item = Node;

    fn next(&mut self) -> Option<Node> {
        if self.front >= self.back {
            return None;
        }
        let n = self.slice.get(self.front);
        self.front += 1;
        Some(n)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.back - self.front;
        (n, Some(n))
    }
}

impl DoubleEndedIterator for NodeSliceIter {
    fn next_back(&mut self) -> Option<Node> {
        if self.front >= self.back {
            return None;
        }
        self.back -= 1;
        Some(self.slice.get(self.back))
    }
}

impl ExactSizeIterator for NodeSliceIter {}

impl IntoIterator for NodeSlice {
    type Item = Node;
    type IntoIter = NodeSliceIter;

    fn into_iter(self) -> NodeSliceIter {
        self.iter()
    }
}

impl IntoIterator for &NodeSlice {
    type Item = Node;
    type IntoIter = NodeSliceIter;

    fn into_iter(self) -> NodeSliceIter {
        self.iter()
    }
}

// ──────────────────────────────────────────────────────────────────────
// NodeList
// ──────────────────────────────────────────────────────────────────────

/// Go `*ast.NodeList`. `list == None` is Go `nil`. Equality is pointer
/// equality, like Go.
#[derive(Clone, Copy, Debug, Default)]
pub struct NodeList {
    pub file: u32,
    pub list: Option<&'static ts_ast::NodeList>,
}

impl PartialEq for NodeList {
    fn eq(&self, other: &Self) -> bool {
        match (self.is_nil(), other.is_nil(), self.list, other.list) {
            (true, true, _, _) => true,
            (false, false, Some(a), Some(b)) => std::ptr::eq(a, b),
            _ => false,
        }
    }
}

impl Eq for NodeList {}

impl NodeList {
    /// Go `nil`.
    pub const NIL: Self = Self {
        file: 0,
        list: None,
    };

    /// Go `list == nil`. A required ts_ast list field of a store node holds
    /// Go `nil` as a marker list (`store::NIL_LIST_POS`).
    #[must_use]
    pub fn is_nil(self) -> bool {
        match self.list {
            None => true,
            Some(l) => is_nil_list_marker(l),
        }
    }

    #[must_use]
    pub fn is_some(self) -> bool {
        !self.is_nil()
    }

    /// Go `list.Nodes`. Empty when nil.
    #[must_use]
    pub fn nodes(self) -> NodeSlice {
        match self.list {
            Some(l) => NodeSlice::from_ids(self.file as usize, &l.nodes),
            None => NodeSlice::NIL,
        }
    }

    /// Go `list.Loc`. Panics when nil, like Go.
    #[must_use]
    // PORT: the Rust list ranges include the delimiters or start at the
    // first token. Go ranges start after the opener (or at the full start)
    // and end after the last element or its trailing comma.
    pub fn loc(self) -> TextRange {
        let l = self.list.expect("nil NodeList dereference");
        assert!(!is_nil_list_marker(l), "nil NodeList dereference");
        // Synthetic and store lists hold the Go `Loc`.
        if self.file as usize == SYNTHETIC_NODE_FILE || has_file_store(self.file as usize) {
            return text_range_of(&l.range);
        }
        let Some(file) = prog().files.get(self.file as usize) else {
            return text_range_of(&l.range);
        };
        let arena = &file.legacy_source().parse.arena;
        let text = file.legacy_source().source_text.as_bytes();
        let span = |id: &ts_ast::NodeId| {
            arena
                .get(*id)
                .map(|n| crate::ast::go_view::go_node_range(&file.info.trivia, text, arena, n))
        };
        let elements = match (
            l.nodes.first().and_then(span),
            l.nodes.last().and_then(span),
        ) {
            (Some(first), Some(last)) => Some((first, last)),
            _ => None,
        };
        let (pos, end) = crate::ast::go_view::go_list_range(
            &file.info.trivia,
            text,
            (l.range.start.get(), l.range.end.get()),
            elements,
        );
        TextRange::new(pos as i32, end as i32)
    }

    // Go: ast.go:134 Pos
    #[must_use]
    pub fn pos(self) -> i32 {
        self.loc().pos()
    }

    // Go: ast.go:135 End
    #[must_use]
    pub fn end(self) -> i32 {
        self.loc().end()
    }

    // Go: ast.go:137 HasTrailingComma
    #[must_use]
    pub fn has_trailing_comma(self) -> bool {
        let nodes = self.nodes();
        match nodes.last() {
            None => false,
            Some(last) => last.end() < self.end(),
        }
    }
}

// ──────────────────────────────────────────────────────────────────────
// ModifierList
// ──────────────────────────────────────────────────────────────────────

/// Go `*ast.ModifierList`. `list == None` is Go `nil`.
#[derive(Clone, Copy, Debug, Default)]
pub struct ModifierList {
    pub file: u32,
    pub list: Option<&'static ts_ast::ModifierList>,
}

impl PartialEq for ModifierList {
    fn eq(&self, other: &Self) -> bool {
        match (self.list, other.list) {
            (None, None) => true,
            (Some(a), Some(b)) => std::ptr::eq(a, b),
            _ => false,
        }
    }
}

impl Eq for ModifierList {}

impl ModifierList {
    /// Go `nil`.
    pub const NIL: Self = Self {
        file: 0,
        list: None,
    };

    #[must_use]
    pub const fn is_nil(self) -> bool {
        self.list.is_none()
    }

    #[must_use]
    pub const fn is_some(self) -> bool {
        self.list.is_some()
    }

    /// Go `modifiers.NodeList`.
    #[must_use]
    pub fn node_list(self) -> NodeList {
        NodeList {
            file: self.file,
            list: self.list.map(|m| &m.list),
        }
    }

    /// Go `modifiers.Nodes`. Empty when nil.
    #[must_use]
    pub fn nodes(self) -> NodeSlice {
        self.node_list().nodes()
    }

    #[must_use]
    pub fn pos(self) -> i32 {
        self.node_list().pos()
    }

    #[must_use]
    pub fn end(self) -> i32 {
        self.node_list().end()
    }

    #[must_use]
    pub fn loc(self) -> TextRange {
        self.node_list().loc()
    }

    /// Go `modifiers.ModifierFlags`. NONE when nil.
    // PORT: ts_ast stores its own flag type, so the Go flags are computed
    // from the modifier nodes with `modifiers_to_flags`, as the Go factory
    // does when it builds the list.
    #[must_use]
    pub fn modifier_flags(self) -> ModifierFlags {
        if self.is_nil() {
            return ModifierFlags::NONE;
        }
        modifiers_to_flags(&self.nodes().to_vec())
    }
}

// ──────────────────────────────────────────────────────────────────────
// Visitor helpers
// ──────────────────────────────────────────────────────────────────────

// Go: ast.go:29 visit
fn visit(v: &mut dyn FnMut(Node) -> bool, node: Node) -> bool {
    if node.is_some() {
        return v(node);
    }
    false
}

// Go: ast.go:36 visitNodes
fn visit_nodes(v: &mut dyn FnMut(Node) -> bool, nodes: NodeSlice) -> bool {
    for node in nodes {
        if v(node) {
            return true;
        }
    }
    false
}

// Go: ast.go:45 visitNodeList
fn visit_node_list(v: &mut dyn FnMut(Node) -> bool, node_list: NodeList) -> bool {
    if node_list.is_some() {
        return visit_nodes(v, node_list.nodes());
    }
    false
}

// Go: ast.go:52 visitModifiers
fn visit_modifiers(v: &mut dyn FnMut(Node) -> bool, modifiers: ModifierList) -> bool {
    if modifiers.is_some() {
        return visit_nodes(v, modifiers.nodes());
    }
    false
}

// ──────────────────────────────────────────────────────────────────────
// Node core accessors
// ──────────────────────────────────────────────────────────────────────

thread_local! {
    /// Go `Node.Decorators()` results. Go allocates a new slice on each call;
    /// we keep one per node so `NodeSlice` can borrow it.
    static DECORATORS: RefCell<FxHashMap<Node, &'static [Node]>> = RefCell::new(FxHashMap::default());
    /// Go `CompositeBase.facts`: cached `SubtreeFacts` per node.
    static SUBTREE_FACTS: RefCell<FxHashMap<Node, SubtreeFacts>> = RefCell::new(FxHashMap::default());
    /// Go `Node.Text()` results that Go builds with string concatenation.
    static JOINED_TEXT: RefCell<FxHashMap<Node, &'static str>> = RefCell::new(FxHashMap::default());
    /// Empty Go member lists of parsed mapped types (see `mapped_type_members`).
    static MAPPED_TYPE_MEMBERS: RefCell<FxHashMap<Node, &'static ts_ast::NodeList>> =
        RefCell::new(FxHashMap::default());
}

impl Node {
    /// Go `node.Kind`.
    #[must_use]
    pub fn kind(self) -> SyntaxKind {
        let r = raw(self);
        // A store node holds the Go kind.
        if has_file_store(self.file_index()) {
            return r.kind;
        }
        match r.kind {
            SyntaxKind::PropertyDeclaration
            | SyntaxKind::QualifiedName
            | SyntaxKind::OmittedExpression => go_kind(self.file_index(), nid(self), r),
            k => k,
        }
    }

    /// Go `node.Flags`: parser flags plus the flags the binder adds.
    #[must_use]
    pub fn flags(self) -> NodeFlags {
        if is_synthetic_node(self) {
            return synthetic_flags(self);
        }
        if has_file_store(self.file_index()) {
            // The parser reads flags before the program exists.
            let flags = store_header(self).flags;
            return match crate::core::try_prog() {
                Some(p) if self.file_index() < p.files.len() => flags | self.bind().added_flags,
                _ => flags,
            };
        }
        self.go_file().parser_flags[nid(self).index()] | self.bind().added_flags
    }

    /// Go `node.Parent`.
    #[must_use]
    pub fn parent(self) -> Node {
        if is_synthetic_node(self) {
            return synthetic_parent(self);
        }
        if has_file_store(self.file_index()) {
            return store_header(self).parent;
        }
        opt(self.file_index(), raw(self).parent)
    }

    /// Go `node.Loc`.
    #[must_use]
    // PORT: the Rust parser starts a node at its first token. Go starts it
    // at the full start, before the leading trivia (see `ast::go_view`).
    pub fn loc(self) -> TextRange {
        if is_synthetic_node(self) {
            return synthetic_loc(self);
        }
        if has_file_store(self.file_index()) {
            return store_header(self).loc;
        }
        let r = raw(self);
        let Some(file) = prog().files.get(self.file_index()) else {
            return text_range_of(&r.range);
        };
        let (pos, end) = crate::ast::go_view::go_node_range(
            &file.info.trivia,
            file.legacy_source().source_text.as_bytes(),
            &file.legacy_source().parse.arena,
            r,
        );
        TextRange::new(pos as i32, end as i32)
    }

    // Go: ast.go:192 Pos
    #[must_use]
    pub fn pos(self) -> i32 {
        self.loc().pos()
    }

    // Go: ast.go:193 End
    #[must_use]
    pub fn end(self) -> i32 {
        self.loc().end()
    }

    /// The program file that holds this node.
    #[must_use]
    pub fn go_file(self) -> &'static GoFile {
        &prog().files[self.file_index()]
    }

    /// Binder data for this node. Nil values before the file is bound.
    #[must_use]
    pub fn bind(self) -> &'static NodeBindData {
        if is_synthetic_node(self) {
            return synthetic_bind(self);
        }
        match self.go_file().node_bind.get() {
            Some(v) => &v[nid(self).index()],
            None => &NO_BIND,
        }
    }

    // Go: ast.go:198 Name
    #[must_use]
    pub fn name(self) -> Node {
        // PORT: a QualifiedName that Go parses as a PropertyAccessExpression.
        if let NodeData::QualifiedName(d) = data(self)
            && self.kind() == SyntaxKind::PropertyAccessExpression
        {
            return req(self.file_index(), d.right);
        }
        by_data!(
            self,
            |f, d| opt(f, d.name),
            [
                BindingElement,
                ClassDeclaration,
                ClassExpression,
                FunctionDeclaration,
                FunctionExpression,
                ImportClause,
                JsDocCallbackTag,
                JsDocLink,
                JsDocLinkCode,
                JsDocLinkPlain,
                JsDocTypedefTag,
            ],
            by_data!(
                self,
                |f, d| req(f, d.name),
                [
                    EnumDeclaration,
                    EnumMember,
                    ExportSpecifier,
                    GetAccessorDeclaration,
                    SetAccessorDeclaration,
                    ImportAttribute,
                    ImportEqualsDeclaration,
                    ImportSpecifier,
                    InterfaceDeclaration,
                    JsDocNameReference,
                    JsDocParameterOrPropertyTag,
                    JsxAttribute,
                    JsxNamespacedName,
                    MetaProperty,
                    MethodDeclaration,
                    MethodSignatureDeclaration,
                    ModuleDeclaration,
                    NamedTupleMember,
                    NamespaceExport,
                    NamespaceExportDeclaration,
                    NamespaceImport,
                    ParameterDeclaration,
                    PropertyAccessExpression,
                    PropertyAssignment,
                    PropertyDeclaration,
                    PropertySignatureDeclaration,
                    ShorthandPropertyAssignment,
                    TypeAliasDeclaration,
                    TypeParameterDeclaration,
                    VariableDeclaration,
                ],
                Node::NIL
            )
        )
    }

    // Go: ast.go:199 Modifiers
    #[must_use]
    pub fn modifiers(self) -> ModifierList {
        by_data!(
            self,
            |f, d| mods(f, &d.modifiers),
            [
                ArrowFunction,
                BinaryExpression,
                ClassDeclaration,
                ClassExpression,
                ClassStaticBlockDeclaration,
                ConstructorDeclaration,
                ConstructorTypeNode,
                EnumDeclaration,
                EnumMember,
                ExportAssignment,
                ExportDeclaration,
                FunctionDeclaration,
                FunctionExpression,
                FunctionTypeNode,
                GetAccessorDeclaration,
                SetAccessorDeclaration,
                ImportDeclaration,
                ImportEqualsDeclaration,
                IndexSignatureDeclaration,
                InterfaceDeclaration,
                MethodDeclaration,
                MethodSignatureDeclaration,
                MissingDeclaration,
                ModuleDeclaration,
                NamespaceExportDeclaration,
                ParameterDeclaration,
                PropertyAssignment,
                PropertyDeclaration,
                PropertySignatureDeclaration,
                ShorthandPropertyAssignment,
                TypeAliasDeclaration,
                TypeParameterDeclaration,
                VariableStatement,
            ],
            ModifierList::NIL
        )
    }

    // Go: ast.go:205 ParameterList
    /// Go `FunctionLikeData().Parameters`. Nil for other nodes.
    // PORT: Go dereferences a nil FunctionLikeData here; we return nil.
    #[must_use]
    pub fn parameter_list(self) -> NodeList {
        by_data!(
            self,
            |f, d| list(f, &d.parameters),
            [
                ArrowFunction,
                CallSignatureDeclaration,
                ConstructSignatureDeclaration,
                ConstructorDeclaration,
                FunctionDeclaration,
                FunctionExpression,
                GetAccessorDeclaration,
                SetAccessorDeclaration,
                IndexSignatureDeclaration,
                JsDocSignature,
                MethodDeclaration,
                MethodSignatureDeclaration,
                FunctionTypeNode,
                ConstructorTypeNode,
            ],
            NodeList::NIL
        )
    }

    // Go: ast.go:206 Parameters
    #[must_use]
    pub fn parameters(self) -> NodeSlice {
        self.parameter_list().nodes()
    }

    // Go: ast.go:209 SubtreeFacts
    /// Go `node.SubtreeFacts()`, cached per node like Go `CompositeBase`.
    #[must_use]
    pub fn subtree_facts(self) -> SubtreeFacts {
        if let Some(facts) = SUBTREE_FACTS.with(|c| c.borrow().get(&self).copied()) {
            return facts;
        }
        let facts = compute_subtree_facts(self).without(SubtreeFacts::COMPUTED);
        SUBTREE_FACTS.with(|c| c.borrow_mut().insert(self, facts));
        facts
    }

    // Go: ast.go:217 Decorators
    #[must_use]
    pub fn decorators(self) -> NodeSlice {
        let modifiers = self.modifiers();
        if modifiers.is_nil() {
            return NodeSlice::NIL;
        }
        if let Some(cached) = DECORATORS.with(|c| c.borrow().get(&self).copied()) {
            return NodeSlice::from_nodes(cached);
        }
        let filtered: Vec<Node> = modifiers
            .nodes()
            .iter()
            .filter(|&m| is_decorator(m))
            .collect();
        let leaked: &'static [Node] = Box::leak(filtered.into_boxed_slice());
        DECORATORS.with(|c| c.borrow_mut().insert(self, leaked));
        NodeSlice::from_nodes(leaked)
    }

    // Go: ast.go:229 Symbol
    // PORT: Go reads `DeclarationData().Symbol`. The binder only sets the
    // symbol on declaration nodes, so reading the bind data directly is the
    // same.
    #[must_use]
    pub fn symbol(self) -> SymbolId {
        self.bind().symbol
    }

    // Go: ast.go:237 LocalSymbol
    #[must_use]
    pub fn local_symbol(self) -> SymbolId {
        self.bind().local_symbol
    }

    // Go: ast.go:245 Locals
    #[must_use]
    pub fn locals(self) -> SymbolTable {
        self.bind().locals
    }

    /// Go `LocalsContainerData().NextContainer`.
    #[must_use]
    pub fn next_container(self) -> Node {
        self.bind().next_container
    }

    /// Go `FlowNodeData().FlowNode`.
    #[must_use]
    pub fn flow_node(self) -> FlowNodeId {
        self.bind().flow_node
    }

    /// Go `EndFlowNode` of a function-like or module node.
    #[must_use]
    pub fn end_flow_node(self) -> FlowNodeId {
        self.bind().end_flow_node
    }

    /// Go `ReturnFlowNode` of a function-like node or class static block.
    #[must_use]
    pub fn return_flow_node(self) -> FlowNodeId {
        self.bind().return_flow_node
    }
}

impl FlowNodeId {
    /// Go `*FlowNode` dereference.
    #[must_use]
    pub fn get_flow(self) -> &'static FlowNode {
        assert!(self.is_some(), "nil flow node dereference");
        if self.file_index() == crate::checker::SYNTHETIC_FLOW_FILE {
            return crate::checker::synthetic_flow(self);
        }
        &prog().files[self.file_index()]
            .flow_nodes
            .get()
            .expect("flow nodes are not built for this file")[self.local_index()]
    }
}

/// Go `file.AsSourceFile()` fields that the parser and program set.
#[must_use]
pub fn source_file_info(file: Node) -> &'static crate::program::SourceFileInfo {
    &file.go_file().info
}

/// Go `file.AsSourceFile()` fields that the binder sets.
#[must_use]
pub fn file_bind_data(file: Node) -> &'static FileBindData {
    file.go_file()
        .file_bind
        .get()
        .expect("source file is not bound")
}

// ──────────────────────────────────────────────────────────────────────
// Node field accessors (Go methods on *Node)
// ──────────────────────────────────────────────────────────────────────

/// Go `AsCaseOrDefaultClause().Expression`. Nil for a default clause.
// PORT: ts_ast stores a required expression id on both clause kinds. Go
// leaves it nil for `default:`, so the kind decides.
fn case_expression(n: Node, file: usize, id: ts_ast::NodeId) -> Node {
    if n.kind() == SyntaxKind::CaseClause {
        req(file, id)
    } else {
        Node::NIL
    }
}

/// Caches a string that Go builds on each call, so `text()` can return
/// `&'static str`.
fn joined_text(n: Node, build: impl FnOnce() -> String) -> &'static str {
    if let Some(s) = JOINED_TEXT.with(|c| c.borrow().get(&n).copied()) {
        return s;
    }
    let s: &'static str = Box::leak(build().into_boxed_str());
    JOINED_TEXT.with(|c| c.borrow_mut().insert(n, s));
    s
}

impl Node {
    // Go: ast.go:253 Body
    // PORT: also covers ClassStaticBlockDeclaration, whose Go `Body` field
    // has no generated accessor.
    #[must_use]
    pub fn body(self) -> Node {
        by_data!(
            self,
            |f, d| opt(f, d.body),
            [
                FunctionDeclaration,
                MethodDeclaration,
                GetAccessorDeclaration,
                SetAccessorDeclaration,
                ConstructorDeclaration,
                ModuleDeclaration,
            ],
            by_data!(
                self,
                |f, d| req(f, d.body),
                [
                    FunctionExpression,
                    ArrowFunction,
                    ClassStaticBlockDeclaration,
                ],
                Node::NIL
            )
        )
    }

    // Go: ast.go:261 Text
    // PORT: also covers JsxText, whose Go `Text` field has no generated
    // accessor. Other kinds give "" instead of a panic.
    #[must_use]
    pub fn text(self) -> &'static str {
        match data(self) {
            NodeData::Identifier(d) => &d.text,
            NodeData::PrivateIdentifier(d) => &d.text,
            NodeData::StringLiteral(d) => &d.text,
            NodeData::NumericLiteral(d) => &d.text,
            NodeData::BigIntLiteral(d) => &d.text,
            NodeData::MetaProperty(_) => self.name().text(),
            NodeData::NoSubstitutionTemplateLiteral(d) => &d.text,
            NodeData::TemplateHead(d) => &d.text,
            NodeData::TemplateMiddle(d) => &d.text,
            NodeData::TemplateTail(d) => &d.text,
            NodeData::JsxNamespacedName(d) => {
                let file = self.file_index();
                joined_text(self, || {
                    format!(
                        "{}:{}",
                        req(file, d.namespace).text(),
                        req(file, d.name).text()
                    )
                })
            }
            NodeData::RegularExpressionLiteral(d) => &d.text,
            NodeData::JsDocText(d) => joined_text(self, || d.text.concat()),
            NodeData::JsDocLink(d) => joined_text(self, || d.text.concat()),
            NodeData::JsDocLinkCode(d) => joined_text(self, || d.text.concat()),
            NodeData::JsDocLinkPlain(d) => joined_text(self, || d.text.concat()),
            NodeData::JsxText(d) => &d.text,
            _ => "",
        }
    }

    // Go: ast.go:299 Expression
    // PORT: also covers TypeParameterDeclaration and
    // SyntheticReferenceExpression, whose Go `Expression` fields have no
    // generated accessor.
    #[must_use]
    pub fn expression(self) -> Node {
        if let NodeData::CaseOrDefaultClause(d) = data(self) {
            return case_expression(self, self.file_index(), d.expression);
        }
        // PORT: a QualifiedName that Go parses as a PropertyAccessExpression.
        if let NodeData::QualifiedName(d) = data(self)
            && self.kind() == SyntaxKind::PropertyAccessExpression
        {
            return req(self.file_index(), d.left);
        }
        by_data!(
            self,
            |f, d| req(f, d.expression),
            [
                PropertyAccessExpression,
                ElementAccessExpression,
                ParenthesizedExpression,
                CallExpression,
                NewExpression,
                ExpressionWithTypeArguments,
                ComputedPropertyName,
                NonNullExpression,
                TypeAssertion,
                AsExpression,
                SatisfiesExpression,
                TypeOfExpression,
                SpreadAssignment,
                SpreadElement,
                TemplateSpan,
                DeleteExpression,
                VoidExpression,
                AwaitExpression,
                PartiallyEmittedExpression,
                IfStatement,
                DoStatement,
                WhileStatement,
                WithStatement,
                ForInOrOfStatement,
                SwitchStatement,
                ExpressionStatement,
                ThrowStatement,
                ExternalModuleReference,
                ExportAssignment,
                Decorator,
                JsxSpreadAttribute,
                SyntheticReferenceExpression,
            ],
            by_data!(
                self,
                |f, d| opt(f, d.expression),
                [
                    YieldExpression,
                    ReturnStatement,
                    JsxExpression,
                    TypeParameterDeclaration,
                ],
                Node::NIL
            )
        )
    }

    // Go: ast.go:375 RawText
    // PORT: also covers NoSubstitutionTemplateLiteral, whose Go `RawText`
    // field has no generated accessor.
    #[must_use]
    pub fn raw_text(self) -> &'static str {
        match data(self) {
            NodeData::TemplateHead(d) => &d.raw_text,
            NodeData::TemplateMiddle(d) => &d.raw_text,
            NodeData::TemplateTail(d) => &d.raw_text,
            NodeData::NoSubstitutionTemplateLiteral(d) => &d.raw_text,
            _ => "",
        }
    }

    // Go: ast.go:465 ArgumentList
    #[must_use]
    pub fn argument_list(self) -> NodeList {
        let f = self.file_index();
        match data(self) {
            NodeData::CallExpression(d) => list(f, &d.arguments),
            NodeData::NewExpression(d) => opt_list(f, &d.arguments),
            _ => NodeList::NIL,
        }
    }

    // Go: ast.go:475 Arguments
    #[must_use]
    pub fn arguments(self) -> NodeSlice {
        self.argument_list().nodes()
    }

    // Go: ast.go:483 TypeArgumentList
    #[must_use]
    pub fn type_argument_list(self) -> NodeList {
        by_data!(
            self,
            |f, d| opt_list(f, &d.type_arguments),
            [
                CallExpression,
                NewExpression,
                TaggedTemplateExpression,
                TypeReferenceNode,
                ExpressionWithTypeArguments,
                ImportTypeNode,
                TypeQueryNode,
                JsxOpeningElement,
                JsxSelfClosingElement,
            ],
            NodeList::NIL
        )
    }

    // Go: ast.go:507 TypeArguments
    #[must_use]
    pub fn type_arguments(self) -> NodeSlice {
        self.type_argument_list().nodes()
    }

    // Go: ast.go:515 TypeParameterList
    #[must_use]
    pub fn type_parameter_list(self) -> NodeList {
        if let NodeData::JsDocTemplateTag(d) = data(self) {
            return list(self.file_index(), &d.type_parameters);
        }
        by_data!(
            self,
            |f, d| opt_list(f, &d.type_parameters),
            [
                ClassDeclaration,
                ClassExpression,
                InterfaceDeclaration,
                TypeAliasDeclaration,
                ArrowFunction,
                CallSignatureDeclaration,
                ConstructSignatureDeclaration,
                ConstructorDeclaration,
                FunctionDeclaration,
                FunctionExpression,
                GetAccessorDeclaration,
                SetAccessorDeclaration,
                IndexSignatureDeclaration,
                JsDocSignature,
                MethodDeclaration,
                MethodSignatureDeclaration,
                FunctionTypeNode,
                ConstructorTypeNode,
            ],
            NodeList::NIL
        )
    }

    // Go: ast.go:536 TypeParameters
    #[must_use]
    pub fn type_parameters(self) -> NodeSlice {
        self.type_parameter_list().nodes()
    }

    // Go: ast.go:544 MemberList
    #[must_use]
    pub fn member_list(self) -> NodeList {
        if let NodeData::MappedTypeNode(_) = data(self) {
            return mapped_type_members(self);
        }
        by_data!(
            self,
            |f, d| list(f, &d.members),
            [
                ClassDeclaration,
                ClassExpression,
                InterfaceDeclaration,
                EnumDeclaration,
                TypeLiteralNode,
            ],
            NodeList::NIL
        )
    }

    // Go: ast.go:562 Members
    #[must_use]
    pub fn members(self) -> NodeSlice {
        self.member_list().nodes()
    }

    // Go: ast.go:570 StatementList
    #[must_use]
    pub fn statement_list(self) -> NodeList {
        by_data!(
            self,
            |f, d| list(f, &d.statements),
            [SourceFile, Block, ModuleBlock, CaseOrDefaultClause,],
            NodeList::NIL
        )
    }

    // Go: ast.go:584 Statements
    #[must_use]
    pub fn statements(self) -> NodeSlice {
        self.statement_list().nodes()
    }

    // Go: ast.go:592 CanHaveStatements
    #[must_use]
    pub fn can_have_statements(self) -> bool {
        matches!(
            self.kind(),
            SyntaxKind::SourceFile
                | SyntaxKind::Block
                | SyntaxKind::ModuleBlock
                | SyntaxKind::CaseClause
                | SyntaxKind::DefaultClause
        )
    }

    // Go: ast.go:601 ModifierFlags
    #[must_use]
    pub fn modifier_flags(self) -> ModifierFlags {
        self.modifiers().modifier_flags()
    }

    // Go: ast.go:609 ModifierNodes
    #[must_use]
    pub fn modifier_nodes(self) -> NodeSlice {
        self.modifiers().nodes()
    }

    // Go: ast.go:617 Type
    // PORT: also covers JsDocVariadicType, whose Go `Type` field has no
    // generated accessor.
    #[must_use]
    pub fn type_(self) -> Node {
        let f = self.file_index();
        match data(self) {
            NodeData::JsDocParameterOrPropertyTag(d) => return opt(f, d.type_expression),
            NodeData::IndexSignatureDeclaration(d) => return req(f, d.type_),
            _ => {}
        }
        by_data!(
            self,
            |f, d| opt(f, d.type_),
            [
                VariableDeclaration,
                ParameterDeclaration,
                PropertyDeclaration,
                PropertyAssignment,
                ShorthandPropertyAssignment,
                TypePredicateNode,
                MappedTypeNode,
                ExportAssignment,
                BinaryExpression,
                ArrowFunction,
                CallSignatureDeclaration,
                ConstructSignatureDeclaration,
                ConstructorDeclaration,
                FunctionDeclaration,
                FunctionExpression,
                GetAccessorDeclaration,
                SetAccessorDeclaration,
                JsDocSignature,
                MethodDeclaration,
                MethodSignatureDeclaration,
                FunctionTypeNode,
                ConstructorTypeNode,
            ],
            by_data!(
                self,
                |f, d| req(f, d.type_),
                [
                    PropertySignatureDeclaration,
                    ParenthesizedTypeNode,
                    TypeOperatorNode,
                    TypeAssertion,
                    AsExpression,
                    SatisfiesExpression,
                    TypeAliasDeclaration,
                    NamedTupleMember,
                    OptionalTypeNode,
                    RestTypeNode,
                    TemplateLiteralTypeSpan,
                    JsDocTypeExpression,
                    JsDocNullableType,
                    JsDocNonNullableType,
                    JsDocOptionalType,
                    JsDocVariadicType,
                ],
                Node::NIL
            )
        )
    }

    // Go: ast.go:739 Initializer
    #[must_use]
    pub fn initializer(self) -> Node {
        by_data!(
            self,
            |f, d| opt(f, d.initializer),
            [
                VariableDeclaration,
                ParameterDeclaration,
                BindingElement,
                PropertyDeclaration,
                EnumMember,
                ForStatement,
                JsxAttribute,
            ],
            by_data!(
                self,
                |f, d| req(f, d.initializer),
                [
                    PropertySignatureDeclaration,
                    PropertyAssignment,
                    ForInOrOfStatement,
                ],
                Node::NIL
            )
        )
    }

    // Go: ast.go:793 TagName
    #[must_use]
    pub fn tag_name(self) -> Node {
        by_data!(
            self,
            |f, d| req(f, d.tag_name),
            [
                JsxOpeningElement,
                JsxClosingElement,
                JsxSelfClosingElement,
                JsDocUnknownTag,
                JsDocAugmentsTag,
                JsDocImplementsTag,
                JsDocDeprecatedTag,
                JsDocPublicTag,
                JsDocPrivateTag,
                JsDocProtectedTag,
                JsDocReadonlyTag,
                JsDocOverrideTag,
                JsDocCallbackTag,
                JsDocOverloadTag,
                JsDocParameterOrPropertyTag,
                JsDocReturnTag,
                JsDocThisTag,
                JsDocTypeTag,
                JsDocTemplateTag,
                JsDocTypedefTag,
                JsDocSeeTag,
                JsDocSatisfiesTag,
                JsDocThrowsTag,
                JsDocImportTag,
            ],
            Node::NIL
        )
    }

    // Go: ast.go:847 PropertyName
    #[must_use]
    pub fn property_name(self) -> Node {
        by_data!(
            self,
            |f, d| opt(f, d.property_name),
            [ImportSpecifier, ExportSpecifier, BindingElement,],
            Node::NIL
        )
    }

    // Go: ast.go:859 PropertyNameOrName
    #[must_use]
    pub fn property_name_or_name(self) -> Node {
        let name = self.property_name();
        if name.is_nil() {
            return self.name();
        }
        name
    }

    // Go: ast.go:867 IsTypeOnly
    #[must_use]
    pub fn is_type_only(self) -> bool {
        match data(self) {
            NodeData::ImportEqualsDeclaration(d) => d.is_type_only,
            NodeData::ImportSpecifier(d) => d.is_type_only,
            NodeData::ImportClause(d) => d.phase_modifier == Some(SyntaxKind::TypeKeyword),
            NodeData::ExportDeclaration(d) => d.is_type_only,
            NodeData::ExportSpecifier(d) => d.is_type_only,
            _ => false,
        }
    }

    // Go: ast.go:884 CommentList
    #[must_use]
    pub fn comment_list(self) -> NodeList {
        if let NodeData::JsDoc(d) = data(self) {
            return list(self.file_index(), &d.comment);
        }
        by_data!(
            self,
            |f, d| opt_list(f, &d.comment),
            [
                JsDocUnknownTag,
                JsDocAugmentsTag,
                JsDocImplementsTag,
                JsDocDeprecatedTag,
                JsDocPublicTag,
                JsDocPrivateTag,
                JsDocProtectedTag,
                JsDocReadonlyTag,
                JsDocOverrideTag,
                JsDocCallbackTag,
                JsDocOverloadTag,
                JsDocParameterOrPropertyTag,
                JsDocReturnTag,
                JsDocThisTag,
                JsDocTypeTag,
                JsDocTemplateTag,
                JsDocTypedefTag,
                JsDocSeeTag,
                JsDocSatisfiesTag,
                JsDocThrowsTag,
                JsDocImportTag,
            ],
            NodeList::NIL
        )
    }

    // Go: ast.go:934 Comments
    #[must_use]
    pub fn comments(self) -> NodeSlice {
        self.comment_list().nodes()
    }

    // Go: ast.go:942 Label
    #[must_use]
    pub fn label(self) -> Node {
        let f = self.file_index();
        match data(self) {
            NodeData::LabeledStatement(d) => req(f, d.label),
            NodeData::BreakStatement(d) => opt(f, d.label),
            NodeData::ContinueStatement(d) => opt(f, d.label),
            _ => Node::NIL,
        }
    }

    // Go: ast.go:954 Attributes
    // PORT: also covers the `Attributes` fields of ImportDeclaration,
    // ExportDeclaration, ImportTypeNode and JSDocImportTag, which have no
    // generated accessor.
    #[must_use]
    pub fn attributes(self) -> Node {
        by_data!(
            self,
            |f, d| req(f, d.attributes),
            [JsxOpeningElement, JsxSelfClosingElement,],
            by_data!(
                self,
                |f, d| opt(f, d.attributes),
                [
                    ImportDeclaration,
                    ExportDeclaration,
                    ImportTypeNode,
                    JsDocImportTag,
                ],
                Node::NIL
            )
        )
    }

    // Go: ast.go:964 Children
    #[must_use]
    pub fn children(self) -> NodeList {
        by_data!(
            self,
            |f, d| list(f, &d.children),
            [JsxElement, JsxFragment],
            NodeList::NIL
        )
    }

    // Go: ast.go:974 ModuleSpecifier
    #[must_use]
    pub fn module_specifier(self) -> Node {
        let f = self.file_index();
        match data(self) {
            NodeData::ImportDeclaration(d) => req(f, d.module_specifier),
            NodeData::ExportDeclaration(d) => opt(f, d.module_specifier),
            NodeData::JsDocImportTag(d) => req(f, d.module_specifier),
            _ => Node::NIL,
        }
    }

    // Go: ast.go:986 ImportClause
    #[must_use]
    pub fn import_clause(self) -> Node {
        by_data!(
            self,
            |f, d| opt(f, d.import_clause),
            [ImportDeclaration, JsDocImportTag],
            Node::NIL
        )
    }

    // Go: ast.go:996 Statement
    #[must_use]
    pub fn statement(self) -> Node {
        by_data!(
            self,
            |f, d| req(f, d.statement),
            [
                DoStatement,
                WhileStatement,
                ForStatement,
                ForInOrOfStatement,
                WithStatement,
                LabeledStatement,
            ],
            Node::NIL
        )
    }

    // Go: ast.go:1014 PropertyList
    #[must_use]
    pub fn property_list(self) -> NodeList {
        by_data!(
            self,
            |f, d| list(f, &d.properties),
            [ObjectLiteralExpression, JsxAttributes],
            NodeList::NIL
        )
    }

    // Go: ast_generated.go ImportAttributes.Attributes
    #[must_use]
    pub fn attribute_list(self) -> NodeList {
        by_data!(
            self,
            |f, d| list(f, &d.attributes),
            [ImportAttributes],
            NodeList::NIL
        )
    }

    // Go: ast.go:1024 Properties
    #[must_use]
    pub fn properties(self) -> NodeSlice {
        self.property_list().nodes()
    }

    // Go: ast.go:1032 ElementList
    #[must_use]
    pub fn element_list(self) -> NodeList {
        by_data!(
            self,
            |f, d| list(f, &d.elements),
            [
                NamedImports,
                NamedExports,
                BindingPattern,
                ArrayLiteralExpression,
                TupleTypeNode,
            ],
            NodeList::NIL
        )
    }

    // Go: ast.go:1048 Elements
    #[must_use]
    pub fn elements(self) -> NodeSlice {
        self.element_list().nodes()
    }

    // Go: ast.go:1056 PostfixToken
    #[must_use]
    pub fn postfix_token(self) -> Node {
        by_data!(
            self,
            |f, d| opt(f, d.postfix_token),
            [
                MethodDeclaration,
                ShorthandPropertyAssignment,
                MethodSignatureDeclaration,
                PropertySignatureDeclaration,
                PropertyAssignment,
                PropertyDeclaration,
                EnumMember,
                GetAccessorDeclaration,
                SetAccessorDeclaration,
            ],
            Node::NIL
        )
    }

    // Go: ast.go:1080 QuestionToken
    #[must_use]
    pub fn question_token(self) -> Node {
        let f = self.file_index();
        match data(self) {
            NodeData::ParameterDeclaration(d) => return opt(f, d.question_token),
            NodeData::ConditionalExpression(d) => return req(f, d.question_token),
            NodeData::MappedTypeNode(d) => return opt(f, d.question_token),
            NodeData::NamedTupleMember(d) => return opt(f, d.question_token),
            _ => {}
        }
        let postfix = self.postfix_token();
        if postfix.is_some() && postfix.kind() == SyntaxKind::QuestionToken {
            return postfix;
        }
        Node::NIL
    }

    // Go: ast.go:1098 QuestionDotToken
    #[must_use]
    pub fn question_dot_token(self) -> Node {
        by_data!(
            self,
            |f, d| opt(f, d.question_dot_token),
            [
                ElementAccessExpression,
                PropertyAccessExpression,
                CallExpression,
                TaggedTemplateExpression,
            ],
            Node::NIL
        )
    }

    // Go: ast.go:1112 TypeExpression
    // PORT: also covers the JSDoc `@this` and `@overload` tags, whose Go
    // `TypeExpression` fields have no generated accessor.
    #[must_use]
    pub fn type_expression(self) -> Node {
        by_data!(
            self,
            |f, d| opt(f, d.type_expression),
            [
                JsDocParameterOrPropertyTag,
                JsDocReturnTag,
                JsDocTypedefTag,
                JsDocThrowsTag,
            ],
            by_data!(
                self,
                |f, d| req(f, d.type_expression),
                [
                    JsDocTypeTag,
                    JsDocCallbackTag,
                    JsDocSatisfiesTag,
                    JsDocThisTag,
                    JsDocOverloadTag,
                ],
                Node::NIL
            )
        )
    }

    // Go: ast.go:1132 ClassName
    #[must_use]
    pub fn class_name(self) -> Node {
        by_data!(
            self,
            |f, d| req(f, d.class_name),
            [JsDocAugmentsTag, JsDocImplementsTag],
            Node::NIL
        )
    }

    // Go: ast.go:1144 Contains
    /// Reports whether `self` contains `descendant` by walking up the parent
    /// links. Panics if a non-SourceFile ancestor has no parent.
    #[must_use]
    pub fn contains(self, mut descendant: Node) -> bool {
        while descendant.is_some() {
            if descendant == self {
                return true;
            }
            let parent = descendant.parent();
            if parent.is_nil() && !is_source_file(descendant) {
                panic!("descendant is not parented");
            }
            descendant = parent;
        }
        false
    }
}

// ──────────────────────────────────────────────────────────────────────
// ForEachChild / IterChildren
// ──────────────────────────────────────────────────────────────────────

impl Node {
    // Go: ast.go:194 ForEachChild
    /// Calls `v` on each child in Go source order. Stops and returns true
    /// when `v` returns true.
    pub fn for_each_child(self, mut v: impl FnMut(Node) -> bool) -> bool {
        for_each_child_dyn(self, &mut v)
    }

    // Go: ast.go:195 IterChildren
    /// The children that `for_each_child` visits, in the same order.
    #[must_use]
    pub fn iter_children(self) -> std::vec::IntoIter<Node> {
        let mut out = Vec::new();
        for_each_child_dyn(self, &mut |c| {
            out.push(c);
            false
        });
        out.into_iter()
    }
}

// Go: ast_generated.go ForEachChild (one method per node struct)
// PORT: the per-struct Go methods are merged into one match. The order of
// each arm follows the generated Go code.
fn for_each_child_dyn(n: Node, v: &mut dyn FnMut(Node) -> bool) -> bool {
    for_each_child_impl(n, v, None)
}

/// A list slot seen by `for_each_child_and_lists`: the list and whether it
/// is a modifier list.
pub type ListHook<'a> = &'a mut dyn FnMut(NodeList, bool);

impl Node {
    /// `for_each_child` that also reports each non-nil NodeList and
    /// ModifierList slot to `lists` before its nodes are visited. Used by the
    /// `astdump` parity tool.
    pub fn for_each_child_and_lists(
        self,
        v: &mut dyn FnMut(Node) -> bool,
        lists: ListHook,
    ) -> bool {
        for_each_child_impl(self, v, Some(lists))
    }
}

fn for_each_child_impl(
    n: Node,
    v: &mut dyn FnMut(Node) -> bool,
    mut lists: Option<ListHook>,
) -> bool {
    let f = n.file_index();
    let mut report = |l: NodeList, is_mod: bool| {
        if let Some(h) = lists.as_mut() {
            if l.is_some() {
                h(l, is_mod);
            }
        }
    };
    macro_rules! n {
        ($x:expr) => {
            visit(v, req(f, $x))
        };
    }
    macro_rules! o {
        ($x:expr) => {
            visit(v, opt(f, $x))
        };
    }
    macro_rules! l {
        ($x:expr) => {{
            let l = list(f, &$x);
            report(l, false);
            visit_node_list(v, l)
        }};
    }
    macro_rules! ol {
        ($x:expr) => {{
            let l = opt_list(f, &$x);
            report(l, false);
            visit_node_list(v, l)
        }};
    }
    macro_rules! m {
        ($x:expr) => {{
            let m = mods(f, &$x);
            report(m.node_list(), true);
            visit_modifiers(v, m)
        }};
    }
    match data(n) {
        NodeData::QualifiedName(d) => n!(d.left) || n!(d.right),
        NodeData::ComputedPropertyName(d) => n!(d.expression),
        NodeData::Decorator(d) => n!(d.expression),
        NodeData::IfStatement(d) => {
            n!(d.expression) || n!(d.then_statement) || o!(d.else_statement)
        }
        NodeData::DoStatement(d) => n!(d.statement) || n!(d.expression),
        NodeData::WhileStatement(d) => n!(d.expression) || n!(d.statement),
        NodeData::ForStatement(d) => {
            o!(d.initializer) || o!(d.condition) || o!(d.incrementor) || n!(d.statement)
        }
        NodeData::ForInOrOfStatement(d) => {
            o!(d.await_modifier) || n!(d.initializer) || n!(d.expression) || n!(d.statement)
        }
        NodeData::BreakStatement(d) => o!(d.label),
        NodeData::ContinueStatement(d) => o!(d.label),
        NodeData::ReturnStatement(d) => o!(d.expression),
        NodeData::WithStatement(d) => n!(d.expression) || n!(d.statement),
        NodeData::SwitchStatement(d) => n!(d.expression) || n!(d.case_block),
        NodeData::CaseBlock(d) => l!(d.clauses),
        NodeData::CaseOrDefaultClause(d) => {
            visit(v, case_expression(n, f, d.expression)) || l!(d.statements)
        }
        NodeData::ThrowStatement(d) => n!(d.expression),
        NodeData::TryStatement(d) => n!(d.try_block) || o!(d.catch_clause) || o!(d.finally_block),
        NodeData::CatchClause(d) => o!(d.variable_declaration) || n!(d.block),
        NodeData::LabeledStatement(d) => n!(d.label) || n!(d.statement),
        NodeData::ExpressionStatement(d) => n!(d.expression),
        NodeData::Block(d) => l!(d.statements),
        NodeData::VariableStatement(d) => m!(d.modifiers) || n!(d.declaration_list),
        NodeData::VariableDeclaration(d) => {
            n!(d.name) || o!(d.exclamation_token) || o!(d.type_) || o!(d.initializer)
        }
        NodeData::VariableDeclarationList(d) => l!(d.declarations),
        NodeData::BindingPattern(d) => l!(d.elements),
        NodeData::ParameterDeclaration(d) => {
            m!(d.modifiers)
                || o!(d.dot_dot_dot_token)
                || n!(d.name)
                || o!(d.question_token)
                || o!(d.type_)
                || o!(d.initializer)
        }
        NodeData::BindingElement(d) => {
            o!(d.dot_dot_dot_token) || o!(d.property_name) || o!(d.name) || o!(d.initializer)
        }
        NodeData::MissingDeclaration(d) => m!(d.modifiers),
        NodeData::FunctionDeclaration(d) => {
            m!(d.modifiers)
                || o!(d.asterisk_token)
                || o!(d.name)
                || ol!(d.type_parameters)
                || l!(d.parameters)
                || o!(d.type_)
                || o!(d.full_signature)
                || o!(d.body)
        }
        NodeData::ClassDeclaration(d) => {
            m!(d.modifiers)
                || o!(d.name)
                || ol!(d.type_parameters)
                || ol!(d.heritage_clauses)
                || l!(d.members)
        }
        NodeData::ClassExpression(d) => {
            m!(d.modifiers)
                || o!(d.name)
                || ol!(d.type_parameters)
                || ol!(d.heritage_clauses)
                || l!(d.members)
        }
        NodeData::InterfaceDeclaration(d) => {
            m!(d.modifiers)
                || n!(d.name)
                || ol!(d.type_parameters)
                || ol!(d.heritage_clauses)
                || l!(d.members)
        }
        NodeData::HeritageClause(d) => l!(d.types),
        NodeData::TypeAliasDeclaration(d) => {
            m!(d.modifiers) || n!(d.name) || ol!(d.type_parameters) || n!(d.type_)
        }
        NodeData::EnumMember(d) => n!(d.name) || o!(d.initializer),
        NodeData::EnumDeclaration(d) => m!(d.modifiers) || n!(d.name) || l!(d.members),
        NodeData::ModuleBlock(d) => l!(d.statements),
        NodeData::ImportDeclaration(d) => {
            m!(d.modifiers) || o!(d.import_clause) || n!(d.module_specifier) || o!(d.attributes)
        }
        NodeData::ExternalModuleReference(d) => n!(d.expression),
        NodeData::NamespaceImport(d) => n!(d.name),
        NodeData::NamedImports(d) => l!(d.elements),
        NodeData::ExportAssignment(d) => m!(d.modifiers) || o!(d.type_) || n!(d.expression),
        NodeData::NamespaceExportDeclaration(d) => m!(d.modifiers) || n!(d.name),
        NodeData::NamespaceExport(d) => n!(d.name),
        NodeData::NamedExports(d) => l!(d.elements),
        NodeData::ExportSpecifier(d) => o!(d.property_name) || n!(d.name),
        NodeData::CallSignatureDeclaration(d) => {
            ol!(d.type_parameters) || l!(d.parameters) || o!(d.type_)
        }
        NodeData::ConstructSignatureDeclaration(d) => {
            ol!(d.type_parameters) || l!(d.parameters) || o!(d.type_)
        }
        NodeData::ConstructorDeclaration(d) => {
            m!(d.modifiers)
                || ol!(d.type_parameters)
                || l!(d.parameters)
                || o!(d.type_)
                || o!(d.full_signature)
                || o!(d.body)
        }
        NodeData::GetAccessorDeclaration(d) => {
            m!(d.modifiers)
                || n!(d.name)
                || ol!(d.type_parameters)
                || l!(d.parameters)
                || o!(d.type_)
                || o!(d.full_signature)
                || o!(d.body)
        }
        NodeData::SetAccessorDeclaration(d) => {
            m!(d.modifiers)
                || n!(d.name)
                || ol!(d.type_parameters)
                || l!(d.parameters)
                || o!(d.type_)
                || o!(d.full_signature)
                || o!(d.body)
        }
        NodeData::IndexSignatureDeclaration(d) => {
            m!(d.modifiers) || l!(d.parameters) || n!(d.type_)
        }
        NodeData::MethodSignatureDeclaration(d) => {
            m!(d.modifiers)
                || n!(d.name)
                || o!(d.postfix_token)
                || ol!(d.type_parameters)
                || l!(d.parameters)
                || o!(d.type_)
        }
        NodeData::MethodDeclaration(d) => {
            m!(d.modifiers)
                || o!(d.asterisk_token)
                || n!(d.name)
                || o!(d.postfix_token)
                || ol!(d.type_parameters)
                || l!(d.parameters)
                || o!(d.type_)
                || o!(d.full_signature)
                || o!(d.body)
        }
        NodeData::PropertySignatureDeclaration(d) => {
            m!(d.modifiers) || n!(d.name) || o!(d.postfix_token) || n!(d.type_) || n!(d.initializer)
        }
        NodeData::PropertyDeclaration(d) => {
            m!(d.modifiers) || n!(d.name) || o!(d.postfix_token) || o!(d.type_) || o!(d.initializer)
        }
        NodeData::ClassStaticBlockDeclaration(d) => m!(d.modifiers) || n!(d.body),
        NodeData::BinaryExpression(d) => {
            m!(d.modifiers) || n!(d.left) || o!(d.type_) || n!(d.operator_token) || n!(d.right)
        }
        NodeData::PrefixUnaryExpression(d) => n!(d.operand),
        NodeData::PostfixUnaryExpression(d) => n!(d.operand),
        NodeData::YieldExpression(d) => o!(d.asterisk_token) || o!(d.expression),
        NodeData::ArrowFunction(d) => {
            m!(d.modifiers)
                || ol!(d.type_parameters)
                || l!(d.parameters)
                || o!(d.type_)
                || o!(d.full_signature)
                || n!(d.equals_greater_than_token)
                || n!(d.body)
        }
        NodeData::FunctionExpression(d) => {
            m!(d.modifiers)
                || o!(d.asterisk_token)
                || o!(d.name)
                || ol!(d.type_parameters)
                || l!(d.parameters)
                || o!(d.type_)
                || o!(d.full_signature)
                || n!(d.body)
        }
        NodeData::AsExpression(d) => n!(d.expression) || n!(d.type_),
        NodeData::SatisfiesExpression(d) => n!(d.expression) || n!(d.type_),
        NodeData::ConditionalExpression(d) => {
            n!(d.condition)
                || n!(d.question_token)
                || n!(d.when_true)
                || n!(d.colon_token)
                || n!(d.when_false)
        }
        NodeData::PropertyAccessExpression(d) => {
            n!(d.expression) || o!(d.question_dot_token) || n!(d.name)
        }
        NodeData::ElementAccessExpression(d) => {
            n!(d.expression) || o!(d.question_dot_token) || n!(d.argument_expression)
        }
        NodeData::CallExpression(d) => {
            n!(d.expression) || o!(d.question_dot_token) || ol!(d.type_arguments) || l!(d.arguments)
        }
        NodeData::NewExpression(d) => n!(d.expression) || ol!(d.type_arguments) || ol!(d.arguments),
        NodeData::MetaProperty(d) => n!(d.name),
        NodeData::NonNullExpression(d) => n!(d.expression),
        NodeData::SpreadElement(d) => n!(d.expression),
        NodeData::TemplateExpression(d) => n!(d.head) || l!(d.template_spans),
        NodeData::TemplateSpan(d) => n!(d.expression) || n!(d.literal),
        NodeData::TaggedTemplateExpression(d) => {
            n!(d.tag) || o!(d.question_dot_token) || ol!(d.type_arguments) || n!(d.template)
        }
        NodeData::ParenthesizedExpression(d) => n!(d.expression),
        NodeData::ArrayLiteralExpression(d) => l!(d.elements),
        NodeData::ObjectLiteralExpression(d) => l!(d.properties),
        NodeData::SpreadAssignment(d) => n!(d.expression),
        NodeData::PropertyAssignment(d) => {
            m!(d.modifiers) || n!(d.name) || o!(d.postfix_token) || o!(d.type_) || n!(d.initializer)
        }
        NodeData::ShorthandPropertyAssignment(d) => {
            m!(d.modifiers)
                || n!(d.name)
                || o!(d.postfix_token)
                || o!(d.type_)
                || o!(d.equals_token)
                || o!(d.object_assignment_initializer)
        }
        NodeData::DeleteExpression(d) => n!(d.expression),
        NodeData::TypeOfExpression(d) => n!(d.expression),
        NodeData::VoidExpression(d) => n!(d.expression),
        NodeData::AwaitExpression(d) => n!(d.expression),
        NodeData::TypeAssertion(d) => n!(d.type_) || n!(d.expression),
        NodeData::UnionTypeNode(d) => l!(d.types),
        NodeData::IntersectionTypeNode(d) => l!(d.types),
        NodeData::ConditionalTypeNode(d) => {
            n!(d.check_type) || n!(d.extends_type) || n!(d.true_type) || n!(d.false_type)
        }
        NodeData::TypeOperatorNode(d) => n!(d.type_),
        NodeData::InferTypeNode(d) => n!(d.type_parameter),
        NodeData::ArrayTypeNode(d) => n!(d.element_type),
        NodeData::IndexedAccessTypeNode(d) => n!(d.object_type) || n!(d.index_type),
        NodeData::TypeReferenceNode(d) => n!(d.type_name) || ol!(d.type_arguments),
        NodeData::ExpressionWithTypeArguments(d) => n!(d.expression) || ol!(d.type_arguments),
        NodeData::LiteralTypeNode(d) => n!(d.literal),
        NodeData::TypePredicateNode(d) => {
            o!(d.asserts_modifier) || n!(d.parameter_name) || o!(d.type_)
        }
        NodeData::ImportAttribute(d) => n!(d.name) || n!(d.value),
        NodeData::ImportAttributes(d) => l!(d.attributes),
        NodeData::TypeQueryNode(d) => n!(d.expr_name) || ol!(d.type_arguments),
        NodeData::MappedTypeNode(d) => {
            o!(d.readonly_token)
                || n!(d.type_parameter)
                || o!(d.name_type)
                || o!(d.question_token)
                || o!(d.type_)
                || {
                    let l = mapped_type_members(n);
                    report(l, false);
                    visit_node_list(v, l)
                }
        }
        NodeData::TypeLiteralNode(d) => l!(d.members),
        NodeData::TupleTypeNode(d) => l!(d.elements),
        NodeData::NamedTupleMember(d) => {
            o!(d.dot_dot_dot_token) || n!(d.name) || o!(d.question_token) || n!(d.type_)
        }
        NodeData::OptionalTypeNode(d) => n!(d.type_),
        NodeData::RestTypeNode(d) => n!(d.type_),
        NodeData::ParenthesizedTypeNode(d) => n!(d.type_),
        NodeData::FunctionTypeNode(d) => ol!(d.type_parameters) || l!(d.parameters) || o!(d.type_),
        NodeData::ConstructorTypeNode(d) => {
            m!(d.modifiers) || ol!(d.type_parameters) || l!(d.parameters) || o!(d.type_)
        }
        NodeData::TemplateLiteralTypeNode(d) => n!(d.head) || l!(d.template_spans),
        NodeData::TemplateLiteralTypeSpan(d) => n!(d.type_) || n!(d.literal),
        NodeData::SyntheticExpression(d) => o!(d.tuple_name_source),
        NodeData::PartiallyEmittedExpression(d) => n!(d.expression),
        NodeData::JsxElement(d) => n!(d.opening_element) || l!(d.children) || n!(d.closing_element),
        NodeData::JsxAttributes(d) => l!(d.properties),
        NodeData::JsxNamespacedName(d) => n!(d.namespace) || n!(d.name),
        NodeData::JsxOpeningElement(d) => {
            n!(d.tag_name) || ol!(d.type_arguments) || n!(d.attributes)
        }
        NodeData::JsxSelfClosingElement(d) => {
            n!(d.tag_name) || ol!(d.type_arguments) || n!(d.attributes)
        }
        NodeData::JsxFragment(d) => {
            n!(d.opening_fragment) || l!(d.children) || n!(d.closing_fragment)
        }
        NodeData::JsxAttribute(d) => n!(d.name) || o!(d.initializer),
        NodeData::JsxSpreadAttribute(d) => n!(d.expression),
        NodeData::JsxClosingElement(d) => n!(d.tag_name),
        NodeData::JsxExpression(d) => o!(d.dot_dot_dot_token) || o!(d.expression),
        NodeData::SyntaxList(d) => visit_nodes(v, NodeSlice::from_ids(f, &d.children)),
        NodeData::JsDoc(d) => l!(d.comment) || ol!(d.tags),
        NodeData::JsDocTypeExpression(d) => n!(d.type_),
        NodeData::JsDocNonNullableType(d) => n!(d.type_),
        NodeData::JsDocNullableType(d) => n!(d.type_),
        NodeData::JsDocVariadicType(d) => n!(d.type_),
        NodeData::JsDocOptionalType(d) => n!(d.type_),
        NodeData::JsDocTypeTag(d) => n!(d.tag_name) || n!(d.type_expression) || ol!(d.comment),
        NodeData::JsDocReturnTag(d) => n!(d.tag_name) || o!(d.type_expression) || ol!(d.comment),
        NodeData::JsDocSatisfiesTag(d) => n!(d.tag_name) || n!(d.type_expression) || ol!(d.comment),
        NodeData::JsDocThrowsTag(d) => n!(d.tag_name) || o!(d.type_expression) || ol!(d.comment),
        NodeData::JsDocThisTag(d) => n!(d.tag_name) || n!(d.type_expression) || ol!(d.comment),
        NodeData::JsDocOverloadTag(d) => n!(d.tag_name) || n!(d.type_expression) || ol!(d.comment),
        NodeData::JsDocUnknownTag(d) => n!(d.tag_name) || ol!(d.comment),
        NodeData::JsDocPublicTag(d) => n!(d.tag_name) || ol!(d.comment),
        NodeData::JsDocPrivateTag(d) => n!(d.tag_name) || ol!(d.comment),
        NodeData::JsDocProtectedTag(d) => n!(d.tag_name) || ol!(d.comment),
        NodeData::JsDocReadonlyTag(d) => n!(d.tag_name) || ol!(d.comment),
        NodeData::JsDocOverrideTag(d) => n!(d.tag_name) || ol!(d.comment),
        NodeData::JsDocDeprecatedTag(d) => n!(d.tag_name) || ol!(d.comment),
        NodeData::JsDocTemplateTag(d) => {
            n!(d.tag_name) || n!(d.constraint) || l!(d.type_parameters) || ol!(d.comment)
        }
        NodeData::JsDocSeeTag(d) => n!(d.tag_name) || n!(d.name_expression) || ol!(d.comment),
        NodeData::JsDocImplementsTag(d) => n!(d.tag_name) || n!(d.class_name) || ol!(d.comment),
        NodeData::JsDocAugmentsTag(d) => n!(d.tag_name) || n!(d.class_name) || ol!(d.comment),
        NodeData::JsDocImportTag(d) => {
            n!(d.tag_name)
                || o!(d.import_clause)
                || n!(d.module_specifier)
                || o!(d.attributes)
                || ol!(d.comment)
        }
        NodeData::JsDocCallbackTag(d) => {
            n!(d.tag_name) || n!(d.type_expression) || o!(d.name) || ol!(d.comment)
        }
        NodeData::JsDocTypedefTag(d) => {
            n!(d.tag_name) || o!(d.type_expression) || o!(d.name) || ol!(d.comment)
        }
        NodeData::JsDocSignature(d) => ol!(d.type_parameters) || l!(d.parameters) || o!(d.type_),
        NodeData::JsDocNameReference(d) => n!(d.name),
        // Go: ast.go:3042 forEachChild_JSDocParameterOrPropertyTag
        NodeData::JsDocParameterOrPropertyTag(d) => {
            n!(d.tag_name)
                || (d.is_name_first && (n!(d.name) || o!(d.type_expression)))
                || (!d.is_name_first && (o!(d.type_expression) || n!(d.name)))
                || ol!(d.comment)
        }
        NodeData::ModuleDeclaration(d) => m!(d.modifiers) || n!(d.name) || o!(d.body),
        NodeData::ImportEqualsDeclaration(d) => {
            m!(d.modifiers) || n!(d.name) || n!(d.module_reference)
        }
        NodeData::ExportDeclaration(d) => {
            m!(d.modifiers) || o!(d.export_clause) || o!(d.module_specifier) || o!(d.attributes)
        }
        NodeData::ImportTypeNode(d) => {
            n!(d.argument) || o!(d.attributes) || o!(d.qualifier) || ol!(d.type_arguments)
        }
        NodeData::ImportClause(d) => o!(d.name) || o!(d.named_bindings),
        NodeData::ImportSpecifier(d) => o!(d.property_name) || n!(d.name),
        NodeData::JsDocLink(d) => o!(d.name),
        NodeData::JsDocLinkCode(d) => o!(d.name),
        NodeData::JsDocLinkPlain(d) => o!(d.name),
        NodeData::TypeParameterDeclaration(d) => {
            m!(d.modifiers)
                || n!(d.name)
                || o!(d.constraint)
                || o!(d.expression)
                || o!(d.default_type)
        }
        NodeData::SyntheticReferenceExpression(d) => n!(d.expression) || n!(d.this_arg),
        NodeData::JsDocTypeLiteral(d) => match &d.js_doc_property_tags {
            Some(tags) => visit_nodes(v, NodeSlice::from_ids(f, tags)),
            None => false,
        },
        NodeData::SourceFile(d) => l!(d.statements) || n!(d.end_of_file_token),
        _ => false,
    }
}

// ──────────────────────────────────────────────────────────────────────
// Subtree facts (ast.go computeSubtreeFacts / propagateSubtreeFacts)
// ──────────────────────────────────────────────────────────────────────

// Go: subtreefacts.go SubtreeExclusions*
const EXCL_NODE: SubtreeFacts = SubtreeFacts::COMPUTED;
const EXCL_ARROW_FUNCTION: SubtreeFacts = EXCL_NODE
    .union(SubtreeFacts::SUBTREE_CONTAINS_AWAIT)
    .union(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD);
const EXCL_FUNCTION: SubtreeFacts = EXCL_NODE
    .union(SubtreeFacts::SUBTREE_CONTAINS_LEXICAL_THIS)
    .union(SubtreeFacts::SUBTREE_CONTAINS_LEXICAL_SUPER)
    .union(SubtreeFacts::SUBTREE_CONTAINS_AWAIT)
    .union(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD);
const EXCL_CONSTRUCTOR: SubtreeFacts = EXCL_FUNCTION;
const EXCL_METHOD: SubtreeFacts = EXCL_FUNCTION;
const EXCL_ACCESSOR: SubtreeFacts = EXCL_FUNCTION;
const EXCL_PROPERTY: SubtreeFacts = EXCL_NODE
    .union(SubtreeFacts::SUBTREE_CONTAINS_LEXICAL_THIS)
    .union(SubtreeFacts::SUBTREE_CONTAINS_LEXICAL_SUPER);
const EXCL_MODULE: SubtreeFacts = EXCL_PROPERTY;
const EXCL_OBJECT_LITERAL: SubtreeFacts =
    EXCL_NODE.union(SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD);
const EXCL_VARIABLE_DECLARATION_LIST: SubtreeFacts = EXCL_OBJECT_LITERAL;
const EXCL_CATCH_CLAUSE: SubtreeFacts = EXCL_OBJECT_LITERAL;
const EXCL_BINDING_PATTERN: SubtreeFacts =
    EXCL_NODE.union(SubtreeFacts::SUBTREE_CONTAINS_REST_OR_SPREAD);

const TS: SubtreeFacts = SubtreeFacts::SUBTREE_CONTAINS_TYPE_SCRIPT;
const NONE_FACTS: SubtreeFacts = SubtreeFacts::NONE;

/// Go `core.IfElse(cond, facts, SubtreeFactsNone)`.
fn facts_if(cond: bool, facts: SubtreeFacts) -> SubtreeFacts {
    if cond { facts } else { NONE_FACTS }
}

// Go: subtreefacts.go:89 propagateEraseableSyntaxListSubtreeFacts
fn propagate_eraseable_list(children: NodeList) -> SubtreeFacts {
    facts_if(children.is_some(), TS)
}

// Go: subtreefacts.go:93 propagateEraseableSyntaxSubtreeFacts
fn propagate_eraseable(child: Node) -> SubtreeFacts {
    facts_if(child.is_some(), TS)
}

// Go: subtreefacts.go:97 propagateObjectBindingElementSubtreeFacts
fn propagate_object_binding_element(child: Node) -> SubtreeFacts {
    let mut facts = propagate_subtree_facts(child);
    if facts.intersects(SubtreeFacts::SUBTREE_CONTAINS_REST_OR_SPREAD) {
        facts = facts.without(SubtreeFacts::SUBTREE_CONTAINS_REST_OR_SPREAD);
        facts |= SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD
            | SubtreeFacts::SUBTREE_CONTAINS_ES_OBJECT_REST_OR_SPREAD;
    }
    facts
}

// Go: subtreefacts.go:106 propagateBindingElementSubtreeFacts
fn propagate_binding_element(child: Node) -> SubtreeFacts {
    propagate_subtree_facts(child).without(SubtreeFacts::SUBTREE_CONTAINS_REST_OR_SPREAD)
}

// Go: subtreefacts.go:110 propagateSubtreeFacts
/// The facts a child adds to its parent. None for a nil child.
fn propagate_subtree_facts(child: Node) -> SubtreeFacts {
    if child.is_nil() {
        return NONE_FACTS;
    }
    propagate_node_facts(child)
}

// Go: subtreefacts.go:117 propagateNodeListSubtreeFacts
fn propagate_node_list(children: NodeList, propagate: fn(Node) -> SubtreeFacts) -> SubtreeFacts {
    let mut facts = NONE_FACTS;
    for child in children.nodes() {
        facts |= propagate(child);
    }
    facts
}

// Go: subtreefacts.go:128 propagateModifierListSubtreeFacts
fn propagate_modifier_list(children: ModifierList) -> SubtreeFacts {
    let mut facts = NONE_FACTS;
    for child in children.nodes() {
        facts |= propagate_subtree_facts(child);
    }
    facts
}

/// True for Go node types that embed `TypeSyntaxBase`.
fn is_type_syntax_data(n: Node) -> bool {
    // PORT: a PropertyDeclaration that Go parses as a PropertySignature.
    if matches!(data(n), NodeData::PropertyDeclaration(_))
        && n.kind() == SyntaxKind::PropertySignature
    {
        return true;
    }
    matches!(
        data(n),
        NodeData::InterfaceDeclaration(_)
            | NodeData::TypeAliasDeclaration(_)
            | NodeData::NamespaceExportDeclaration(_)
            | NodeData::CallSignatureDeclaration(_)
            | NodeData::ConstructSignatureDeclaration(_)
            | NodeData::IndexSignatureDeclaration(_)
            | NodeData::MethodSignatureDeclaration(_)
            | NodeData::PropertySignatureDeclaration(_)
            | NodeData::TypeParameterDeclaration(_)
            | NodeData::KeywordTypeNode(_)
            | NodeData::UnionTypeNode(_)
            | NodeData::IntersectionTypeNode(_)
            | NodeData::ConditionalTypeNode(_)
            | NodeData::TypeOperatorNode(_)
            | NodeData::InferTypeNode(_)
            | NodeData::ArrayTypeNode(_)
            | NodeData::IndexedAccessTypeNode(_)
            | NodeData::TypeReferenceNode(_)
            | NodeData::LiteralTypeNode(_)
            | NodeData::ThisTypeNode(_)
            | NodeData::TypePredicateNode(_)
            | NodeData::TypeQueryNode(_)
            | NodeData::MappedTypeNode(_)
            | NodeData::TypeLiteralNode(_)
            | NodeData::TupleTypeNode(_)
            | NodeData::NamedTupleMember(_)
            | NodeData::OptionalTypeNode(_)
            | NodeData::RestTypeNode(_)
            | NodeData::ParenthesizedTypeNode(_)
            | NodeData::FunctionTypeNode(_)
            | NodeData::ConstructorTypeNode(_)
            | NodeData::TemplateLiteralTypeNode(_)
            | NodeData::TemplateLiteralTypeSpan(_)
            | NodeData::ImportTypeNode(_)
            | NodeData::JsDocTypeExpression(_)
            | NodeData::JsDocNonNullableType(_)
            | NodeData::JsDocNullableType(_)
            | NodeData::JsDocAllType(_)
            | NodeData::JsDocVariadicType(_)
            | NodeData::JsDocOptionalType(_)
            | NodeData::JsDocSignature(_)
            | NodeData::JsDocNameReference(_)
            | NodeData::JsDocTypeLiteral(_)
    )
}

// Go: ast.go:1246 (*NodeDefault).propagateSubtreeFacts and the per-type
// propagateSubtreeFacts overrides in ast.go.
// PORT: the Go overrides are merged into one match on the node data.
fn propagate_node_facts(n: Node) -> SubtreeFacts {
    // Go: ast.go:1621 (*TypeSyntaxBase).propagateSubtreeFacts
    if is_type_syntax_data(n) {
        return TS;
    }
    let facts = n.subtree_facts();
    match data(n) {
        NodeData::CatchClause(_) => facts.without(EXCL_CATCH_CLAUSE),
        NodeData::VariableDeclarationList(_) => facts.without(EXCL_VARIABLE_DECLARATION_LIST),
        NodeData::BindingPattern(_) => facts.without(EXCL_BINDING_PATTERN),
        NodeData::FunctionDeclaration(_) | NodeData::FunctionExpression(_) => {
            facts.without(EXCL_FUNCTION)
        }
        NodeData::ModuleDeclaration(_) => facts.without(EXCL_MODULE),
        NodeData::ConstructorDeclaration(_) => facts.without(EXCL_CONSTRUCTOR),
        NodeData::GetAccessorDeclaration(_) | NodeData::SetAccessorDeclaration(_) => {
            facts.without(EXCL_ACCESSOR) | propagate_subtree_facts(n.name())
        }
        NodeData::MethodDeclaration(_) => {
            facts.without(EXCL_METHOD) | propagate_subtree_facts(n.name())
        }
        NodeData::PropertyDeclaration(_) => {
            facts.without(EXCL_PROPERTY) | propagate_subtree_facts(n.name())
        }
        NodeData::ArrowFunction(_) => facts.without(EXCL_ARROW_FUNCTION),
        NodeData::ObjectLiteralExpression(_) => facts.without(EXCL_OBJECT_LITERAL),
        // Parameter, Class, OuterExpression, PropertyAccess, ElementAccess,
        // Call, New and ArrayLiteral exclusions all equal the Node exclusion.
        _ => facts.without(EXCL_NODE),
    }
}

// Go: ast.go computeSubtreeFacts overrides (ast.go:1619 to ast.go:2689) and
// ast_generated.go computeSubtreeFacts methods.
// PORT: the Go per-type methods are merged into one match. Types without an
// override use Go `(*NodeDefault).computeSubtreeFacts`, which is None.
fn compute_subtree_facts(n: Node) -> SubtreeFacts {
    if is_type_syntax_data(n) {
        // Go: ast.go:1619 (*TypeSyntaxBase).computeSubtreeFacts
        return TS;
    }
    let f = n.file_index();
    macro_rules! p {
        ($x:expr) => {
            propagate_subtree_facts(req(f, $x))
        };
    }
    macro_rules! po {
        ($x:expr) => {
            propagate_subtree_facts(opt(f, $x))
        };
    }
    macro_rules! pl {
        ($x:expr) => {
            propagate_node_list(list(f, &$x), propagate_subtree_facts)
        };
    }
    macro_rules! pol {
        ($x:expr) => {
            propagate_node_list(opt_list(f, &$x), propagate_subtree_facts)
        };
    }
    macro_rules! pm {
        ($x:expr) => {
            propagate_modifier_list(mods(f, &$x))
        };
    }
    macro_rules! el {
        ($x:expr) => {
            propagate_eraseable_list(opt_list(f, &$x))
        };
    }
    macro_rules! e {
        ($x:expr) => {
            propagate_eraseable(opt(f, $x))
        };
    }
    let ambient = |m: &'static Option<ts_ast::ModifierList>| {
        mods(f, m)
            .modifier_flags()
            .intersects(ModifierFlags::AMBIENT)
    };
    let jsx = SubtreeFacts::SUBTREE_CONTAINS_JSX;
    match data(n) {
        // Go: ast.go:1623 (*Token).computeSubtreeFacts
        NodeData::Token(_) => match n.kind() {
            SyntaxKind::UsingKeyword => SubtreeFacts::SUBTREE_CONTAINS_USING,
            SyntaxKind::PublicKeyword
            | SyntaxKind::PrivateKeyword
            | SyntaxKind::ProtectedKeyword
            | SyntaxKind::ReadonlyKeyword
            | SyntaxKind::AbstractKeyword
            | SyntaxKind::DeclareKeyword
            | SyntaxKind::ConstKeyword
            | SyntaxKind::AnyKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::InKeyword
            | SyntaxKind::OutKeyword
            | SyntaxKind::OverrideKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::ExportKeyword => TS,
            SyntaxKind::AccessorKeyword => SubtreeFacts::SUBTREE_CONTAINS_CLASS_FIELDS,
            SyntaxKind::AsyncKeyword => SubtreeFacts::SUBTREE_CONTAINS_ANY_AWAIT,
            SyntaxKind::SuperKeyword => SubtreeFacts::SUBTREE_CONTAINS_LEXICAL_SUPER,
            SyntaxKind::ThisKeyword => SubtreeFacts::SUBTREE_CONTAINS_LEXICAL_THIS,
            SyntaxKind::AsteriskAsteriskToken | SyntaxKind::AsteriskAsteriskEqualsToken => {
                SubtreeFacts::SUBTREE_CONTAINS_EXPONENTIATION_OPERATOR
            }
            SyntaxKind::QuestionQuestionToken => SubtreeFacts::SUBTREE_CONTAINS_NULLISH_COALESCING,
            SyntaxKind::QuestionDotToken => SubtreeFacts::SUBTREE_CONTAINS_OPTIONAL_CHAINING,
            SyntaxKind::QuestionQuestionEqualsToken
            | SyntaxKind::BarBarEqualsToken
            | SyntaxKind::AmpersandAmpersandEqualsToken => {
                SubtreeFacts::SUBTREE_CONTAINS_LOGICAL_ASSIGNMENTS
            }
            _ => NONE_FACTS,
        },
        // Go: ast.go:1670 (*PrivateIdentifier).computeSubtreeFacts
        NodeData::PrivateIdentifier(_) => SubtreeFacts::SUBTREE_CONTAINS_CLASS_FIELDS,
        // Go: ast.go:1678 (*Decorator).computeSubtreeFacts
        NodeData::Decorator(d) => p!(d.expression) | TS | SubtreeFacts::SUBTREE_CONTAINS_DECORATORS,
        // Go: ast.go:1684 (*ForInOrOfStatement).computeSubtreeFacts
        NodeData::ForInOrOfStatement(d) => {
            p!(d.initializer)
                | p!(d.expression)
                | p!(d.statement)
                | facts_if(
                    d.await_modifier.is_some(),
                    SubtreeFacts::SUBTREE_CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR,
                )
        }
        // Go: ast.go:1691 (*ReturnStatement).computeSubtreeFacts
        NodeData::ReturnStatement(d) => {
            po!(d.expression) | SubtreeFacts::SUBTREE_CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
        }
        // Go: ast.go:1696 (*CatchClause).computeSubtreeFacts
        NodeData::CatchClause(d) => {
            po!(d.variable_declaration)
                | p!(d.block)
                | facts_if(
                    d.variable_declaration.is_none(),
                    SubtreeFacts::SUBTREE_CONTAINS_MISSING_CATCH_CLAUSE_VARIABLE,
                )
        }
        // Go: ast.go:1709 (*VariableStatement).computeSubtreeFacts
        NodeData::VariableStatement(d) => {
            if ambient(&d.modifiers) {
                TS
            } else {
                pm!(d.modifiers) | p!(d.declaration_list)
            }
        }
        // Go: ast.go:1718 (*VariableDeclaration).computeSubtreeFacts
        NodeData::VariableDeclaration(d) => {
            p!(d.name) | e!(d.exclamation_token) | e!(d.type_) | po!(d.initializer)
        }
        // Go: ast.go:1725 (*VariableDeclarationList).computeSubtreeFacts
        NodeData::VariableDeclarationList(d) => {
            pl!(d.declarations)
                | facts_if(
                    n.flags().intersects(NodeFlags::USING),
                    SubtreeFacts::SUBTREE_CONTAINS_USING,
                )
        }
        // Go: ast.go:1734 (*BindingPattern).computeSubtreeFacts
        NodeData::BindingPattern(d) => match n.kind() {
            SyntaxKind::ObjectBindingPattern => {
                propagate_node_list(list(f, &d.elements), propagate_object_binding_element)
            }
            SyntaxKind::ArrayBindingPattern => {
                propagate_node_list(list(f, &d.elements), propagate_binding_element)
            }
            _ => NONE_FACTS,
        },
        // Go: ast.go:1749 (*ParameterDeclaration).computeSubtreeFacts
        NodeData::ParameterDeclaration(d) => {
            let name = req(f, d.name);
            if name.is_some() && is_this_identifier(name) {
                TS
            } else {
                pm!(d.modifiers)
                    | propagate_subtree_facts(name)
                    | e!(d.question_token)
                    | e!(d.type_)
                    | po!(d.initializer)
            }
        }
        // Go: ast.go:1765 (*BindingElement).computeSubtreeFacts
        NodeData::BindingElement(d) => {
            po!(d.property_name)
                | po!(d.name)
                | po!(d.initializer)
                | facts_if(
                    d.dot_dot_dot_token.is_some(),
                    SubtreeFacts::SUBTREE_CONTAINS_REST_OR_SPREAD,
                )
        }
        // Go: ast.go:1772 (*FunctionDeclaration).computeSubtreeFacts
        NodeData::FunctionDeclaration(d) => {
            let flags = n.modifier_flags();
            if d.body.is_none() || flags.intersects(ModifierFlags::AMBIENT) {
                TS
            } else {
                let is_async = flags.intersects(ModifierFlags::ASYNC);
                let is_generator = d.asterisk_token.is_some();
                pm!(d.modifiers)
                    | po!(d.asterisk_token)
                    | po!(d.name)
                    | el!(d.type_parameters)
                    | pl!(d.parameters)
                    | e!(d.type_)
                    | e!(d.full_signature)
                    | po!(d.body)
                    | facts_if(
                        is_async && is_generator,
                        SubtreeFacts::SUBTREE_CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR,
                    )
                    | facts_if(
                        is_async && !is_generator,
                        SubtreeFacts::SUBTREE_CONTAINS_ANY_AWAIT,
                    )
            }
        }
        // Go: ast.go:1801 (*ClassLikeBase).computeSubtreeFacts
        NodeData::ClassDeclaration(d) => {
            if ambient(&d.modifiers) {
                TS
            } else {
                pm!(d.modifiers)
                    | po!(d.name)
                    | el!(d.type_parameters)
                    | pol!(d.heritage_clauses)
                    | pl!(d.members)
            }
        }
        NodeData::ClassExpression(d) => {
            if ambient(&d.modifiers) {
                TS
            } else {
                pm!(d.modifiers)
                    | po!(d.name)
                    | el!(d.type_parameters)
                    | pol!(d.heritage_clauses)
                    | pl!(d.members)
            }
        }
        // Go: ast.go:1821 (*HeritageClause).computeSubtreeFacts
        NodeData::HeritageClause(d) => match d.token {
            SyntaxKind::ExtendsKeyword => pl!(d.types),
            SyntaxKind::ImplementsKeyword => TS,
            _ => NONE_FACTS,
        },
        // Go: ast.go:1836 (*EnumMember).computeSubtreeFacts
        NodeData::EnumMember(d) => p!(d.name) | po!(d.initializer) | TS,
        // Go: ast.go:1842 (*EnumDeclaration).computeSubtreeFacts
        NodeData::EnumDeclaration(d) => {
            if ambient(&d.modifiers) {
                TS
            } else {
                pm!(d.modifiers) | p!(d.name) | pl!(d.members) | TS
            }
        }
        // Go: ast.go:1853 (*ModuleDeclaration).computeSubtreeFacts
        NodeData::ModuleDeclaration(d) => {
            if n.modifier_flags().intersects(ModifierFlags::AMBIENT) {
                TS
            } else {
                pm!(d.modifiers) | p!(d.name) | po!(d.body) | TS
            }
        }
        // Go: ast.go:1868 (*ImportEqualsDeclaration).computeSubtreeFacts
        NodeData::ImportEqualsDeclaration(d) => {
            if d.is_type_only || !is_external_module_reference(req(f, d.module_reference)) {
                TS
            } else {
                pm!(d.modifiers) | p!(d.name) | p!(d.module_reference)
            }
        }
        // Go: ast.go:1882 (*ImportSpecifier).computeSubtreeFacts
        NodeData::ImportSpecifier(d) => {
            if d.is_type_only {
                TS
            } else {
                po!(d.property_name) | p!(d.name)
            }
        }
        // Go: ast.go:1891 (*ImportClause).computeSubtreeFacts
        NodeData::ImportClause(d) => {
            if d.phase_modifier == Some(SyntaxKind::TypeKeyword) {
                TS
            } else {
                po!(d.name) | po!(d.named_bindings)
            }
        }
        // Go: ast.go:1900 (*ExportAssignment).computeSubtreeFacts
        NodeData::ExportAssignment(d) => {
            pm!(d.modifiers) | po!(d.type_) | p!(d.expression) | facts_if(d.is_export_equals, TS)
        }
        // Go: ast.go:1908 (*ExportDeclaration).computeSubtreeFacts
        NodeData::ExportDeclaration(d) => {
            pm!(d.modifiers)
                | po!(d.export_clause)
                | po!(d.module_specifier)
                | po!(d.attributes)
                | facts_if(d.is_type_only, TS)
        }
        // Go: ast.go:1916 (*ExportSpecifier).computeSubtreeFacts
        NodeData::ExportSpecifier(d) => {
            if d.is_type_only {
                TS
            } else {
                po!(d.property_name) | p!(d.name)
            }
        }
        // Go: ast.go:1932 (*ConstructorDeclaration).computeSubtreeFacts
        NodeData::ConstructorDeclaration(d) => {
            if d.body.is_none() {
                TS
            } else {
                pm!(d.modifiers)
                    | el!(d.type_parameters)
                    | pl!(d.parameters)
                    | e!(d.type_)
                    | e!(d.full_signature)
                    | po!(d.body)
            }
        }
        // Go: ast.go:1951 (*AccessorDeclarationBase).computeSubtreeFacts
        NodeData::GetAccessorDeclaration(d) => {
            if d.body.is_none() {
                TS
            } else {
                pm!(d.modifiers)
                    | p!(d.name)
                    | el!(d.type_parameters)
                    | pl!(d.parameters)
                    | e!(d.type_)
                    | e!(d.full_signature)
                    | po!(d.body)
            }
        }
        NodeData::SetAccessorDeclaration(d) => {
            if d.body.is_none() {
                TS
            } else {
                pm!(d.modifiers)
                    | p!(d.name)
                    | el!(d.type_parameters)
                    | pl!(d.parameters)
                    | e!(d.type_)
                    | e!(d.full_signature)
                    | po!(d.body)
            }
        }
        // Go: ast.go:1970 (*MethodDeclaration).computeSubtreeFacts
        NodeData::MethodDeclaration(d) => {
            if d.body.is_none() {
                TS
            } else {
                let is_async = modifiers_have_async(mods(f, &d.modifiers));
                let is_generator = d.asterisk_token.is_some();
                pm!(d.modifiers)
                    | po!(d.asterisk_token)
                    | p!(d.name)
                    | e!(d.postfix_token)
                    | el!(d.type_parameters)
                    | pl!(d.parameters)
                    | po!(d.body)
                    | e!(d.type_)
                    | e!(d.full_signature)
                    | facts_if(
                        is_async && is_generator,
                        SubtreeFacts::SUBTREE_CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR,
                    )
                    | facts_if(
                        is_async && !is_generator,
                        SubtreeFacts::SUBTREE_CONTAINS_ANY_AWAIT,
                    )
            }
        }
        // Go: ast.go:1995 (*PropertyDeclaration).computeSubtreeFacts
        NodeData::PropertyDeclaration(d) => {
            pm!(d.modifiers)
                | p!(d.name)
                | e!(d.postfix_token)
                | e!(d.type_)
                | po!(d.initializer)
                | SubtreeFacts::SUBTREE_CONTAINS_CLASS_FIELDS
        }
        // Go: ast.go:2009 (*ClassStaticBlockDeclaration).computeSubtreeFacts
        NodeData::ClassStaticBlockDeclaration(d) => {
            pm!(d.modifiers) | p!(d.body) | SubtreeFacts::SUBTREE_CONTAINS_CLASS_FIELDS
        }
        // Go: ast.go:2015 (*KeywordExpression).computeSubtreeFacts
        NodeData::KeywordExpression(_) => match n.kind() {
            SyntaxKind::ThisKeyword => SubtreeFacts::SUBTREE_CONTAINS_LEXICAL_THIS,
            SyntaxKind::SuperKeyword => SubtreeFacts::SUBTREE_CONTAINS_LEXICAL_SUPER,
            _ => NONE_FACTS,
        },
        // Go: ast.go:2029 (*BigIntLiteral).computeSubtreeFacts
        NodeData::BigIntLiteral(_) => NONE_FACTS,
        // Go: ast.go:2033 (*Identifier).computeSubtreeFacts
        NodeData::Identifier(_) => SubtreeFacts::SUBTREE_CONTAINS_IDENTIFIER,
        // Go: ast.go:2037 (*NoSubstitutionTemplateLiteral).computeSubtreeFacts
        NodeData::NoSubstitutionTemplateLiteral(_) => facts_if(
            n.template_flags()
                .intersects(TokenFlags::CONTAINS_INVALID_ESCAPE),
            SubtreeFacts::SUBTREE_CONTAINS_INVALID_TEMPLATE_ESCAPE,
        ),
        // Go: ast.go:2044 (*BinaryExpression).computeSubtreeFacts
        NodeData::BinaryExpression(d) => {
            let left = req(f, d.left);
            let operator_kind = req(f, d.operator_token).kind();
            let mut facts = pm!(d.modifiers)
                | propagate_subtree_facts(left)
                | po!(d.type_)
                | p!(d.operator_token)
                | p!(d.right)
                | facts_if(
                    operator_kind == SyntaxKind::InKeyword && is_private_identifier(left),
                    SubtreeFacts::SUBTREE_CONTAINS_CLASS_FIELDS
                        | SubtreeFacts::SUBTREE_CONTAINS_PRIVATE_IDENTIFIER_IN_EXPRESSION,
                );
            if operator_kind == SyntaxKind::EqualsToken
                && (is_object_literal_expression(left) || is_array_literal_expression(left))
                && contains_object_rest_or_spread(left)
            {
                facts |= SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD;
            }
            facts
        }
        // Go: ast.go:2061 (*YieldExpression).computeSubtreeFacts
        NodeData::YieldExpression(d) => {
            po!(d.expression) | SubtreeFacts::SUBTREE_CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
        }
        // Go: ast.go:2065 (*ArrowFunction).computeSubtreeFacts
        NodeData::ArrowFunction(d) => {
            pm!(d.modifiers)
                | el!(d.type_parameters)
                | pl!(d.parameters)
                | e!(d.type_)
                | e!(d.full_signature)
                | p!(d.body)
                | facts_if(
                    n.modifier_flags().intersects(ModifierFlags::ASYNC),
                    SubtreeFacts::SUBTREE_CONTAINS_ANY_AWAIT,
                )
        }
        // Go: ast.go:2079 (*FunctionExpression).computeSubtreeFacts
        NodeData::FunctionExpression(d) => {
            let is_async = modifiers_have_async(mods(f, &d.modifiers));
            let is_generator = d.asterisk_token.is_some();
            pm!(d.modifiers)
                | po!(d.asterisk_token)
                | po!(d.name)
                | el!(d.type_parameters)
                | pl!(d.parameters)
                | e!(d.type_)
                | e!(d.full_signature)
                | p!(d.body)
                | facts_if(
                    is_async && is_generator,
                    SubtreeFacts::SUBTREE_CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR,
                )
                | facts_if(
                    is_async && !is_generator,
                    SubtreeFacts::SUBTREE_CONTAINS_ANY_AWAIT,
                )
        }
        // Go: ast.go:2098 (*AsExpression).computeSubtreeFacts
        NodeData::AsExpression(d) => p!(d.expression) | TS,
        // Go: ast.go:2106 (*SatisfiesExpression).computeSubtreeFacts
        NodeData::SatisfiesExpression(d) => p!(d.expression) | TS,
        // Go: ast.go:2114 (*PropertyAccessExpression).computeSubtreeFacts
        NodeData::PropertyAccessExpression(d) => {
            let name = req(f, d.name);
            p!(d.expression)
                | po!(d.question_dot_token)
                | propagate_subtree_facts(name)
                | facts_if(
                    !is_identifier(name),
                    SubtreeFacts::SUBTREE_CONTAINS_PRIVATE_IDENTIFIER_IN_EXPRESSION,
                )
        }
        // Go: ast.go:2132 (*CallExpression).computeSubtreeFacts
        NodeData::CallExpression(d) => {
            p!(d.expression)
                | po!(d.question_dot_token)
                | el!(d.type_arguments)
                | pl!(d.arguments)
                | facts_if(
                    req(f, d.expression).kind() == SyntaxKind::ImportKeyword,
                    SubtreeFacts::SUBTREE_CONTAINS_DYNAMIC_IMPORT,
                )
        }
        // Go: ast.go:2144 (*NewExpression).computeSubtreeFacts
        NodeData::NewExpression(d) => p!(d.expression) | el!(d.type_arguments) | pol!(d.arguments),
        // Go: ast.go:2154 (*MetaProperty).computeSubtreeFacts
        NodeData::MetaProperty(d) => p!(d.name).without(SubtreeFacts::SUBTREE_CONTAINS_IDENTIFIER),
        // Go: ast.go:2158 (*NonNullExpression).computeSubtreeFacts
        NodeData::NonNullExpression(d) => p!(d.expression) | TS,
        // Go: ast.go:2162 (*SpreadElement).computeSubtreeFacts
        NodeData::SpreadElement(d) => {
            p!(d.expression) | SubtreeFacts::SUBTREE_CONTAINS_REST_OR_SPREAD
        }
        // Go: ast.go:2166 (*TaggedTemplateExpression).computeSubtreeFacts
        NodeData::TaggedTemplateExpression(d) => {
            p!(d.tag) | po!(d.question_dot_token) | el!(d.type_arguments) | p!(d.template)
        }
        // Go: ast.go:2183 (*SpreadAssignment).computeSubtreeFacts
        NodeData::SpreadAssignment(d) => {
            p!(d.expression)
                | SubtreeFacts::SUBTREE_CONTAINS_ES_OBJECT_REST_OR_SPREAD
                | SubtreeFacts::SUBTREE_CONTAINS_OBJECT_REST_OR_SPREAD
        }
        // Go: ast.go:2187 (*PropertyAssignment).computeSubtreeFacts
        NodeData::PropertyAssignment(d) => p!(d.name) | po!(d.type_) | p!(d.initializer),
        // Go: ast.go:2193 (*ShorthandPropertyAssignment).computeSubtreeFacts
        NodeData::ShorthandPropertyAssignment(d) => {
            p!(d.name) | po!(d.type_) | po!(d.object_assignment_initializer) | TS
        }
        // Go: ast.go:2200 (*AwaitExpression).computeSubtreeFacts
        NodeData::AwaitExpression(d) => {
            p!(d.expression)
                | SubtreeFacts::SUBTREE_CONTAINS_AWAIT
                | SubtreeFacts::SUBTREE_CONTAINS_ANY_AWAIT
                | SubtreeFacts::SUBTREE_CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
        }
        // Go: ast.go:2205 (*TypeAssertion).computeSubtreeFacts
        NodeData::TypeAssertion(d) => p!(d.expression) | TS,
        // Go: ast.go:2213 (*ExpressionWithTypeArguments).computeSubtreeFacts
        NodeData::ExpressionWithTypeArguments(d) => p!(d.expression) | el!(d.type_arguments),
        // Go: ast.go:2279 (*TemplateHead).computeSubtreeFacts
        NodeData::TemplateHead(_) => facts_if(
            n.template_flags()
                .intersects(TokenFlags::CONTAINS_INVALID_ESCAPE),
            SubtreeFacts::SUBTREE_CONTAINS_INVALID_TEMPLATE_ESCAPE,
        ),
        // Go: ast.go:2286 (*TemplateMiddle).computeSubtreeFacts
        NodeData::TemplateMiddle(_) => facts_if(
            n.template_flags()
                .intersects(TokenFlags::CONTAINS_INVALID_ESCAPE),
            SubtreeFacts::SUBTREE_CONTAINS_INVALID_TEMPLATE_ESCAPE,
        ),
        // Go: ast.go:2293 (*TemplateTail).computeSubtreeFacts
        NodeData::TemplateTail(_) => facts_if(
            n.template_flags()
                .intersects(TokenFlags::CONTAINS_INVALID_ESCAPE),
            SubtreeFacts::SUBTREE_CONTAINS_INVALID_TEMPLATE_ESCAPE,
        ),
        // Go: ast.go:2300 (*JsxElement).computeSubtreeFacts
        NodeData::JsxElement(d) => {
            p!(d.opening_element) | pl!(d.children) | p!(d.closing_element) | jsx
        }
        // Go: ast.go:2307 (*JsxAttributes).computeSubtreeFacts
        NodeData::JsxAttributes(d) => pl!(d.properties) | jsx,
        // Go: ast.go:2312 (*JsxNamespacedName).computeSubtreeFacts
        NodeData::JsxNamespacedName(d) => p!(d.namespace) | p!(d.name) | jsx,
        // Go: ast.go:2318 (*JsxOpeningElement).computeSubtreeFacts
        NodeData::JsxOpeningElement(d) => {
            p!(d.tag_name) | el!(d.type_arguments) | p!(d.attributes) | jsx
        }
        // Go: ast.go:2325 (*JsxSelfClosingElement).computeSubtreeFacts
        NodeData::JsxSelfClosingElement(d) => {
            p!(d.tag_name) | el!(d.type_arguments) | p!(d.attributes) | jsx
        }
        // Go: ast.go:2332 (*JsxFragment).computeSubtreeFacts
        NodeData::JsxFragment(d) => pl!(d.children) | jsx,
        // Go: ast.go:2337 and ast.go:2341 Jsx fragment tokens
        NodeData::JsxOpeningFragment(_) | NodeData::JsxClosingFragment(_) => jsx,
        // Go: ast.go:2345 (*JsxAttribute).computeSubtreeFacts
        NodeData::JsxAttribute(d) => p!(d.name) | po!(d.initializer) | jsx,
        // Go: ast.go:2351 (*JsxSpreadAttribute).computeSubtreeFacts
        NodeData::JsxSpreadAttribute(d) => p!(d.expression) | jsx,
        // Go: ast.go:2355 (*JsxClosingElement).computeSubtreeFacts
        NodeData::JsxClosingElement(d) => p!(d.tag_name) | jsx,
        // Go: ast.go:2359 (*JsxExpression).computeSubtreeFacts
        NodeData::JsxExpression(d) => po!(d.expression) | jsx,
        // Go: ast.go:2363 (*JsxText).computeSubtreeFacts
        NodeData::JsxText(_) => jsx,
        // Go: ast.go:2689 (*SourceFile).computeSubtreeFacts
        NodeData::SourceFile(d) => pl!(d.statements),
        // Go: ast_generated.go computeSubtreeFacts methods
        NodeData::QualifiedName(d) => p!(d.left) | p!(d.right),
        NodeData::ComputedPropertyName(d) => p!(d.expression),
        NodeData::IfStatement(d) => p!(d.expression) | p!(d.then_statement) | po!(d.else_statement),
        NodeData::DoStatement(d) => p!(d.statement) | p!(d.expression),
        NodeData::WhileStatement(d) => p!(d.expression) | p!(d.statement),
        NodeData::ForStatement(d) => {
            po!(d.initializer) | po!(d.condition) | po!(d.incrementor) | p!(d.statement)
        }
        NodeData::WithStatement(d) => p!(d.expression) | p!(d.statement),
        NodeData::SwitchStatement(d) => p!(d.expression) | p!(d.case_block),
        NodeData::CaseBlock(d) => pl!(d.clauses),
        NodeData::CaseOrDefaultClause(d) => {
            propagate_subtree_facts(case_expression(n, f, d.expression)) | pl!(d.statements)
        }
        NodeData::ThrowStatement(d) => p!(d.expression),
        NodeData::TryStatement(d) => p!(d.try_block) | po!(d.catch_clause) | po!(d.finally_block),
        NodeData::LabeledStatement(d) => p!(d.label) | p!(d.statement),
        NodeData::ExpressionStatement(d) => p!(d.expression),
        NodeData::Block(d) => pl!(d.statements),
        NodeData::ModuleBlock(d) => pl!(d.statements),
        NodeData::ImportDeclaration(d) => {
            pm!(d.modifiers) | po!(d.import_clause) | p!(d.module_specifier) | po!(d.attributes)
        }
        NodeData::ExternalModuleReference(d) => p!(d.expression),
        NodeData::NamespaceImport(d) => p!(d.name),
        NodeData::NamedImports(d) => pl!(d.elements),
        NodeData::NamespaceExport(d) => p!(d.name),
        NodeData::NamedExports(d) => pl!(d.elements),
        NodeData::PrefixUnaryExpression(d) => p!(d.operand),
        NodeData::PostfixUnaryExpression(d) => p!(d.operand),
        NodeData::ConditionalExpression(d) => {
            p!(d.condition)
                | p!(d.question_token)
                | p!(d.when_true)
                | p!(d.colon_token)
                | p!(d.when_false)
        }
        NodeData::ElementAccessExpression(d) => {
            p!(d.expression) | po!(d.question_dot_token) | p!(d.argument_expression)
        }
        NodeData::TemplateExpression(d) => p!(d.head) | pl!(d.template_spans),
        NodeData::TemplateSpan(d) => p!(d.expression) | p!(d.literal),
        NodeData::ParenthesizedExpression(d) => p!(d.expression),
        NodeData::ArrayLiteralExpression(d) => pl!(d.elements),
        NodeData::ObjectLiteralExpression(d) => pl!(d.properties),
        NodeData::DeleteExpression(d) => p!(d.expression),
        NodeData::TypeOfExpression(d) => p!(d.expression),
        NodeData::VoidExpression(d) => p!(d.expression),
        NodeData::ImportAttribute(d) => p!(d.name) | p!(d.value),
        NodeData::ImportAttributes(d) => pl!(d.attributes),
        NodeData::PartiallyEmittedExpression(d) => p!(d.expression),
        NodeData::SyntheticReferenceExpression(d) => p!(d.expression) | p!(d.this_arg),
        // Go: ast.go:1242 (*NodeDefault).computeSubtreeFacts
        _ => NONE_FACTS,
    }
}

/// Go `node.modifiers != nil && node.modifiers.ModifierFlags&ModifierFlagsAsync != 0`.
fn modifiers_have_async(modifiers: ModifierList) -> bool {
    modifiers.modifier_flags().intersects(ModifierFlags::ASYNC)
}

// ──────────────────────────────────────────────────────────────────────
// Access kinds
// ──────────────────────────────────────────────────────────────────────

// Go: ast.go:1268 IsWriteOnlyAccess
#[must_use]
pub fn is_write_only_access(node: Node) -> bool {
    access_kind(node) == AccessKind::WRITE
}

// Go: ast.go:1272 IsWriteAccess
#[must_use]
pub fn is_write_access(node: Node) -> bool {
    access_kind(node) != AccessKind::READ
}

// Go: ast.go:1276 IsWriteAccessForReference
#[must_use]
pub fn is_write_access_for_reference(node: Node) -> bool {
    let decl = get_declaration_from_name(node);
    (decl.is_some() && declaration_is_write_access(decl))
        || node.kind() == SyntaxKind::DefaultKeyword
        || is_write_access(node)
}

// Go: ast.go:1281 GetDeclarationFromName
/// The declaration that `name` names, or nil.
#[must_use]
pub fn get_declaration_from_name(name: Node) -> Node {
    if name.is_nil() || name.parent().is_nil() {
        return Node::NIL;
    }
    let parent = name.parent();
    match name.kind() {
        SyntaxKind::StringLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::NumericLiteral
        | SyntaxKind::Identifier => {
            // Go: the literal kinds check for a computed property name, then
            // fall through to the Identifier case.
            if name.kind() != SyntaxKind::Identifier && is_computed_property_name(parent) {
                return parent.parent();
            }
            if is_declaration(parent) {
                if parent.name() == name {
                    return parent;
                }
                return Node::NIL;
            }
            if is_qualified_name(parent) {
                let tag = parent.parent();
                if is_js_doc_parameter_tag(tag) && tag.name() == parent {
                    return tag;
                }
                return Node::NIL;
            }
            let bin_exp = parent.parent();
            if is_binary_expression(bin_exp)
                && get_assignment_declaration_kind(bin_exp) != JSDeclarationKind::NONE
            {
                // (binExp.left as BindableStaticNameExpression).symbol || binExp.symbol
                let left = bin_exp.left();
                let left_has_symbol = left.is_some() && left.symbol().is_some();
                if (left_has_symbol || bin_exp.symbol().is_some())
                    && get_name_of_declaration(bin_exp) == name
                {
                    return bin_exp;
                }
            }
        }
        SyntaxKind::PrivateIdentifier => {
            if is_declaration(parent) && parent.name() == name {
                return parent;
            }
        }
        _ => {}
    }
    Node::NIL
}

// Go: ast.go:1327 declarationIsWriteAccess
fn declaration_is_write_access(decl: Node) -> bool {
    if decl.is_nil() {
        return false;
    }
    // Consider anything in an ambient declaration to be a write access since it may be coming from JS.
    if decl.flags().intersects(NodeFlags::AMBIENT) {
        return true;
    }
    match decl.kind() {
        SyntaxKind::BinaryExpression
        | SyntaxKind::BindingElement
        | SyntaxKind::ClassDeclaration
        | SyntaxKind::ClassExpression
        | SyntaxKind::DefaultKeyword
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::EnumMember
        | SyntaxKind::ExportSpecifier
        | SyntaxKind::ImportClause
        | SyntaxKind::ImportEqualsDeclaration
        | SyntaxKind::ImportSpecifier
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::JsDocCallbackTag
        | SyntaxKind::JsDocTypedefTag
        | SyntaxKind::JsxAttribute
        | SyntaxKind::ModuleDeclaration
        | SyntaxKind::NamespaceExportDeclaration
        | SyntaxKind::NamespaceImport
        | SyntaxKind::NamespaceExport
        | SyntaxKind::Parameter
        | SyntaxKind::ShorthandPropertyAssignment
        | SyntaxKind::TypeAliasDeclaration
        | SyntaxKind::JsTypeAliasDeclaration
        | SyntaxKind::TypeParameter => true,
        // In `({ x: y } = 0);`, `x` is not a write access.
        SyntaxKind::PropertyAssignment => {
            !is_array_literal_or_object_literal_destructuring_pattern(decl.parent())
        }
        // Functions are writes if they provide a value (have a body).
        SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::Constructor
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::GetAccessor
        | SyntaxKind::SetAccessor => decl.body().is_some(),
        // Variables and properties are writes if they have an initializer or are in a catch clause.
        SyntaxKind::VariableDeclaration | SyntaxKind::PropertyDeclaration => {
            decl.initializer().is_some() || is_catch_clause(decl.parent())
        }
        SyntaxKind::MethodSignature
        | SyntaxKind::PropertySignature
        | SyntaxKind::JsDocPropertyTag
        | SyntaxKind::JsDocParameterTag => false,
        // Preserve TS behavior: crash on unexpected kinds.
        _ => panic!("Unhandled case in declarationIsWriteAccess"),
    }
}

// Go: ast.go:1406 IsArrayLiteralOrObjectLiteralDestructuringPattern
#[must_use]
pub fn is_array_literal_or_object_literal_destructuring_pattern(node: Node) -> bool {
    if !(is_array_literal_expression(node) || is_object_literal_expression(node)) {
        return false;
    }
    let parent = node.parent();
    // [a, b, c] = someExpression;
    if is_binary_expression(parent)
        && parent.left() == node
        && parent.operator_token().kind() == SyntaxKind::EqualsToken
    {
        return true;
    }
    // for ([a, b, c] of expression)
    if is_for_of_statement(parent) && parent.initializer() == node {
        return true;
    }
    // {x, a: {a, b, c} } = someExpression
    if is_property_assignment(parent) {
        return is_array_literal_or_object_literal_destructuring_pattern(parent.parent());
    }
    // [x, [a, b, c] ] = someExpression
    is_array_literal_or_object_literal_destructuring_pattern(parent)
}

// Go: ast.go:1430 accessKind
fn access_kind(node: Node) -> AccessKind {
    let parent = node.parent();
    if parent.is_nil() {
        return AccessKind::READ;
    }
    match parent.kind() {
        SyntaxKind::ParenthesizedExpression | SyntaxKind::ArrayLiteralExpression => {
            access_kind(parent)
        }
        SyntaxKind::PrefixUnaryExpression | SyntaxKind::PostfixUnaryExpression => {
            let operator = parent.operator();
            if operator == SyntaxKind::PlusPlusToken || operator == SyntaxKind::MinusMinusToken {
                AccessKind::READ_WRITE
            } else {
                AccessKind::READ
            }
        }
        SyntaxKind::BinaryExpression => {
            if parent.left() == node {
                let operator = parent.operator_token();
                if is_assignment_operator(operator.kind()) {
                    if operator.kind() == SyntaxKind::EqualsToken {
                        return AccessKind::WRITE;
                    }
                    return AccessKind::READ_WRITE;
                }
            }
            AccessKind::READ
        }
        SyntaxKind::PropertyAccessExpression => {
            if parent.name() != node {
                return AccessKind::READ;
            }
            access_kind(parent)
        }
        SyntaxKind::PropertyAssignment => {
            let parent_access = access_kind(parent.parent());
            // In `({ x: varname }) = { x: 1 }`, the left `x` is a read, the right `x` is a write.
            if node == parent.name() {
                return reverse_access_kind(parent_access);
            }
            parent_access
        }
        SyntaxKind::ShorthandPropertyAssignment => {
            // Assume it's the local variable being accessed, since we don't check public properties for --noUnusedLocals.
            if node == parent.object_assignment_initializer() {
                return AccessKind::READ;
            }
            access_kind(parent.parent())
        }
        SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement => {
            if node == parent.initializer() {
                AccessKind::WRITE
            } else {
                AccessKind::READ
            }
        }
        _ => AccessKind::READ,
    }
}

// Go: ast.go:1491 reverseAccessKind
fn reverse_access_kind(a: AccessKind) -> AccessKind {
    if a == AccessKind::READ {
        AccessKind::WRITE
    } else if a == AccessKind::WRITE {
        AccessKind::READ
    } else if a == AccessKind::READ_WRITE {
        AccessKind::READ_WRITE
    } else {
        panic!("Unhandled case in reverseAccessKind")
    }
}

// Go: ast.go:1515 IsDeclarationNode
/// Go `node.DeclarationData() != nil`: the node types that embed
/// `DeclarationBase`.
#[must_use]
pub fn is_declaration_node(node: Node) -> bool {
    matches!(
        data(node),
        NodeData::ArrowFunction(_)
            | NodeData::BinaryExpression(_)
            | NodeData::BindingElement(_)
            | NodeData::CallExpression(_)
            | NodeData::CallSignatureDeclaration(_)
            | NodeData::ClassDeclaration(_)
            | NodeData::ClassExpression(_)
            | NodeData::ClassStaticBlockDeclaration(_)
            | NodeData::ConstructSignatureDeclaration(_)
            | NodeData::ConstructorDeclaration(_)
            | NodeData::ConstructorTypeNode(_)
            | NodeData::EnumDeclaration(_)
            | NodeData::EnumMember(_)
            | NodeData::ExportAssignment(_)
            | NodeData::ExportDeclaration(_)
            | NodeData::ExportSpecifier(_)
            | NodeData::FunctionDeclaration(_)
            | NodeData::FunctionExpression(_)
            | NodeData::FunctionTypeNode(_)
            | NodeData::GetAccessorDeclaration(_)
            | NodeData::ImportClause(_)
            | NodeData::ImportDeclaration(_)
            | NodeData::ImportEqualsDeclaration(_)
            | NodeData::ImportSpecifier(_)
            | NodeData::IndexSignatureDeclaration(_)
            | NodeData::InterfaceDeclaration(_)
            | NodeData::JsDocSignature(_)
            | NodeData::JsDocTypeLiteral(_)
            | NodeData::JsxAttribute(_)
            | NodeData::JsxAttributes(_)
            | NodeData::MappedTypeNode(_)
            | NodeData::MethodDeclaration(_)
            | NodeData::MethodSignatureDeclaration(_)
            | NodeData::MissingDeclaration(_)
            | NodeData::ModuleDeclaration(_)
            | NodeData::NamedTupleMember(_)
            | NodeData::NamespaceExport(_)
            | NodeData::NamespaceExportDeclaration(_)
            | NodeData::NamespaceImport(_)
            | NodeData::NoSubstitutionTemplateLiteral(_)
            | NodeData::ObjectLiteralExpression(_)
            | NodeData::ParameterDeclaration(_)
            | NodeData::PropertyAssignment(_)
            | NodeData::PropertyDeclaration(_)
            | NodeData::PropertySignatureDeclaration(_)
            | NodeData::SemicolonClassElement(_)
            | NodeData::SetAccessorDeclaration(_)
            | NodeData::ShorthandPropertyAssignment(_)
            | NodeData::SourceFile(_)
            | NodeData::SpreadAssignment(_)
            | NodeData::TypeAliasDeclaration(_)
            | NodeData::TypeLiteralNode(_)
            | NodeData::TypeParameterDeclaration(_)
            | NodeData::VariableDeclaration(_)
    )
}

// Go: ast.go:1532 IsLocalsContainer
/// Go `node.LocalsContainerData() != nil`: the node types that embed
/// `LocalsContainerBase`.
#[must_use]
pub fn is_locals_container(node: Node) -> bool {
    matches!(
        data(node),
        NodeData::ArrowFunction(_)
            | NodeData::Block(_)
            | NodeData::CallSignatureDeclaration(_)
            | NodeData::CaseBlock(_)
            | NodeData::CatchClause(_)
            | NodeData::ClassDeclaration(_)
            | NodeData::ClassExpression(_)
            | NodeData::ClassStaticBlockDeclaration(_)
            | NodeData::ConditionalTypeNode(_)
            | NodeData::ConstructSignatureDeclaration(_)
            | NodeData::ConstructorDeclaration(_)
            | NodeData::ConstructorTypeNode(_)
            | NodeData::ForInOrOfStatement(_)
            | NodeData::ForStatement(_)
            | NodeData::FunctionDeclaration(_)
            | NodeData::FunctionExpression(_)
            | NodeData::FunctionTypeNode(_)
            | NodeData::GetAccessorDeclaration(_)
            | NodeData::IndexSignatureDeclaration(_)
            | NodeData::JsDocSignature(_)
            | NodeData::MappedTypeNode(_)
            | NodeData::MethodDeclaration(_)
            | NodeData::MethodSignatureDeclaration(_)
            | NodeData::ModuleDeclaration(_)
            | NodeData::SetAccessorDeclaration(_)
            | NodeData::SourceFile(_)
            | NodeData::TypeAliasDeclaration(_)
    )
}

impl Node {
    // Go: ast.go:1563 JSDoc
    /// The JSDoc nodes of this node. Pass `Node::NIL` for `file` to walk up
    /// to the source file.
    // PORT: Go resolves a lazy cache miss with the parser hook
    // `parseJSDocForNode`. The Go frontend path (`GOPORT_FRONTEND=go`) runs
    // it through `program::resolve_lazy_js_doc`. The legacy path has no
    // hook, so a miss on a lazy file stops at `unported!`.
    #[must_use]
    pub fn js_doc(self, file: Node) -> NodeSlice {
        if !self.flags().intersects(NodeFlags::HAS_JS_DOC) {
            return NodeSlice::NIL;
        }
        let file = if file.is_nil() {
            get_source_file_of_node(self)
        } else {
            file
        };
        if file.is_nil() {
            return NodeSlice::NIL;
        }
        // PORT: during the parse (Go `collectExternalModuleReferences`) the
        // store file is not in a program yet; its cache is in the store.
        if is_file_store_before_program(file.file_index()) {
            return file_store_js_doc(file.file_index(), self)
                .map_or(NodeSlice::NIL, NodeSlice::from_nodes);
        }
        let info = source_file_info(file);
        match info.jsdoc_cache.get(&self) {
            Some(jsdocs) => NodeSlice::from_nodes(jsdocs),
            None if info.has_lazy_js_doc => match crate::program::resolve_lazy_js_doc(file, self) {
                Some(jsdocs) => NodeSlice::from_nodes(jsdocs),
                None => unported!("parseJSDocForNode"),
            },
            None => NodeSlice::NIL,
        }
    }

    // Go: ast.go:1581 EagerJSDoc
    /// JSDoc nodes that are already parsed and cached. It never parses.
    #[must_use]
    pub fn eager_js_doc(self, file: Node) -> NodeSlice {
        if !self.flags().intersects(NodeFlags::HAS_JS_DOC) {
            return NodeSlice::NIL;
        }
        let file = if file.is_nil() {
            get_source_file_of_node(self)
        } else {
            file
        };
        if file.is_nil() {
            return NodeSlice::NIL;
        }
        if is_file_store_before_program(file.file_index()) {
            return file_store_js_doc(file.file_index(), self)
                .map_or(NodeSlice::NIL, NodeSlice::from_nodes);
        }
        source_file_info(file)
            .jsdoc_cache
            .get(&self)
            .map_or(NodeSlice::NIL, |jsdocs| NodeSlice::from_nodes(jsdocs))
    }
}

// Go: ast.go:1832 IsTypeOrJSTypeAliasDeclaration
#[must_use]
pub fn is_type_or_js_type_alias_declaration(node: Node) -> bool {
    node.kind() == SyntaxKind::TypeAliasDeclaration
        || node.kind() == SyntaxKind::JsTypeAliasDeclaration
}

// Go: ast.go:1878 IsImportDeclarationOrJSImportDeclaration
#[must_use]
pub fn is_import_declaration_or_js_import_declaration(node: Node) -> bool {
    node.kind() == SyntaxKind::ImportDeclaration || node.kind() == SyntaxKind::JsImportDeclaration
}

// Go: ast.go:1904 IsAnyExportAssignment
#[must_use]
pub fn is_any_export_assignment(node: Node) -> bool {
    node.kind() == SyntaxKind::ExportAssignment
}

impl Node {
    // Go: ast.go:2218 (*ImportAttributesNode).GetResolutionModeOverride
    /// The `resolution-mode` from an import attributes node, and whether
    /// one was given. The node can be nil.
    #[must_use]
    pub fn get_resolution_mode_override(self) -> (ResolutionMode, bool) {
        if self.is_nil() {
            return (RESOLUTION_MODE_NONE, false);
        }
        let NodeData::ImportAttributes(d) = data(self) else {
            panic!("AsImportAttributes called on {:?}", self.kind());
        };
        let attributes = list(self.file_index(), &d.attributes).nodes();
        if attributes.len() != 1 {
            return (RESOLUTION_MODE_NONE, false);
        }
        let elem = attributes.get(0);
        if !is_string_literal_like(elem.name()) {
            return (RESOLUTION_MODE_NONE, false);
        }
        if elem.name().text() != "resolution-mode" {
            return (RESOLUTION_MODE_NONE, false);
        }
        let value = elem.value();
        if !is_string_literal_like(value) {
            return (RESOLUTION_MODE_NONE, false);
        }
        if value.text() != "import" && value.text() != "require" {
            return (RESOLUTION_MODE_NONE, false);
        }
        if value.text() == "import" {
            (RESOLUTION_MODE_ESM, true)
        } else {
            (RESOLUTION_MODE_COMMON_JS, true)
        }
    }
}

// ──────────────────────────────────────────────────────────────────────
// SourceFile methods. `file` is a SourceFile node.
// ──────────────────────────────────────────────────────────────────────

thread_local! {
    /// Go `SourceFile.ecmaLineMap`, computed once per file.
    static ECMA_LINE_MAPS: RefCell<FxHashMap<Node, &'static [i32]>> = RefCell::new(FxHashMap::default());
    /// Go `SourceFile.nameTable`, computed once per file.
    static NAME_TABLES: RefCell<FxHashMap<Node, &'static FxHashMap<String, i32>>> = RefCell::new(FxHashMap::default());
    /// Go `SourceFile.positionMap`, computed once per file.
    static POSITION_MAPS: RefCell<FxHashMap<Node, &'static PositionMap>> = RefCell::new(FxHashMap::default());
    /// Go `SourceFile.declarationMap`, computed once per file.
    static DECLARATION_MAPS: RefCell<FxHashMap<Node, &'static FxHashMap<String, Vec<Node>>>> =
        RefCell::new(FxHashMap::default());
}

// Go: ast.go:2566 (*SourceFile).Text
#[must_use]
pub fn source_file_text(file: Node) -> &'static str {
    if is_synthetic_node(file) {
        return synthetic_source_file_text(file);
    }
    if has_file_store(file.file_index()) {
        return file_store_text(file.file_index());
    }
    &file.go_file().legacy_source().source_text
}

// Go: ast.go:2570 (*SourceFile).FileName
#[must_use]
pub fn source_file_file_name(file: Node) -> &'static str {
    if is_synthetic_node(file) {
        return synthetic_source_file_file_name(file);
    }
    if has_file_store(file.file_index()) {
        return file_store_file_name(file.file_index());
    }
    &file.go_file().legacy_source().file_name
}

// Go: ast.go:2578 (*SourceFile).Imports
#[must_use]
pub fn source_file_imports(file: Node) -> NodeSlice {
    NodeSlice::from_nodes(&source_file_info(file).imports)
}

// Go: ast.go:2582 (*SourceFile).Diagnostics
#[must_use]
pub fn source_file_diagnostics(file: Node) -> &'static [Diagnostic] {
    &source_file_info(file).diagnostics
}

// Go: ast.go:2590 (*SourceFile).JSDiagnostics
#[must_use]
pub fn source_file_js_diagnostics(file: Node) -> &'static [Diagnostic] {
    &source_file_info(file).js_diagnostics
}

// Go: ast.go:2598 (*SourceFile).JSDocDiagnostics
#[must_use]
pub fn source_file_jsdoc_diagnostics(file: Node) -> &'static [Diagnostic] {
    &source_file_info(file).jsdoc_diagnostics
}

// Go: ast.go:2641 (*SourceFile).BindDiagnostics
// PORT: panics before the file is bound. Go returns nil there.
#[must_use]
pub fn source_file_bind_diagnostics(file: Node) -> &'static [Diagnostic] {
    &file_bind_data(file).bind_diagnostics
}

// Go: ast.go:2657 (*SourceFile).IsJS
#[must_use]
pub fn source_file_is_js(file: Node) -> bool {
    is_source_file_js(file)
}

// Go: ast.go:2702 (*SourceFile).ECMALineMap
#[must_use]
pub fn source_file_ecma_line_map(file: Node) -> &'static [i32] {
    if let Some(line_map) = ECMA_LINE_MAPS.with(|c| c.borrow().get(&file).copied()) {
        return line_map;
    }
    let line_map: &'static [i32] = Vec::leak(compute_ecma_line_starts(source_file_text(file)));
    ECMA_LINE_MAPS.with(|c| c.borrow_mut().insert(file, line_map));
    line_map
}

// Go: ast.go:2720 (*SourceFile).GetNameTable
/// All names in the file mapped to their position. A name that appears
/// more than once maps to -1.
#[must_use]
pub fn source_file_get_name_table(file: Node) -> &'static FxHashMap<String, i32> {
    if let Some(table) = NAME_TABLES.with(|c| c.borrow().get(&file).copied()) {
        return table;
    }
    fn walk(file: Node, node: Node, name_table: &mut FxHashMap<String, i32>) -> bool {
        if is_identifier(node) && !is_tag_name(node) && !node.text().is_empty()
            || is_string_or_numeric_literal_like(node) && literal_is_name(node)
            || is_private_identifier(node)
        {
            let text = node.text();
            if let Some(pos) = name_table.get_mut(text) {
                *pos = -1;
            } else {
                name_table.insert(text.to_string(), node.pos());
            }
        }
        node.for_each_child(|child| walk(file, child, name_table));
        for jsdoc in node.js_doc(file) {
            jsdoc.for_each_child(|child| walk(file, child, name_table));
        }
        false
    }
    let mut name_table = FxHashMap::default();
    file.for_each_child(|child| walk(file, child, &mut name_table));
    let table: &'static FxHashMap<String, i32> = Box::leak(Box::new(name_table));
    NAME_TABLES.with(|c| c.borrow_mut().insert(file, table));
    table
}

// Go: ast.go:2751 (*SourceFile).IsBound
#[must_use]
pub fn source_file_is_bound(file: Node) -> bool {
    file.go_file().file_bind.get().is_some()
}

// Go: ast.go:2756 (*SourceFile).GetPositionMap
// PORT: Go reads the scanner's `ContainsNonASCII` flag. The text is the
// same input, so `str::is_ascii` gives the same answer.
#[must_use]
pub fn source_file_get_position_map(file: Node) -> &'static PositionMap {
    if let Some(map) = POSITION_MAPS.with(|c| c.borrow().get(&file).copied()) {
        return map;
    }
    let text = source_file_text(file);
    let map = if text.is_ascii() {
        PositionMap {
            ascii_only: true,
            ..PositionMap::default()
        }
    } else {
        compute_position_map(text)
    };
    let map: &'static PositionMap = Box::leak(Box::new(map));
    POSITION_MAPS.with(|c| c.borrow_mut().insert(file, map));
    map
}

// Go: ast.go:2840 (*SourceFile).GetDeclarationMap
#[must_use]
pub fn source_file_get_declaration_map(file: Node) -> &'static FxHashMap<String, Vec<Node>> {
    if let Some(map) = DECLARATION_MAPS.with(|c| c.borrow().get(&file).copied()) {
        return map;
    }
    let map: &'static FxHashMap<String, Vec<Node>> =
        Box::leak(Box::new(compute_declaration_map(file)));
    DECLARATION_MAPS.with(|c| c.borrow_mut().insert(file, map));
    map
}

// Go: ast.go:2849 (*SourceFile).computeDeclarationMap
fn compute_declaration_map(file: Node) -> FxHashMap<String, Vec<Node>> {
    fn add_declaration(result: &mut FxHashMap<String, Vec<Node>>, declaration: Node) {
        let name = get_declaration_name(declaration);
        if !name.is_empty() {
            result.entry(name).or_default().push(declaration);
        }
    }
    fn visit(result: &mut FxHashMap<String, Vec<Node>>, node: Node) -> bool {
        match node.kind() {
            SyntaxKind::FunctionDeclaration
            | SyntaxKind::FunctionExpression
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::MethodSignature => {
                let declaration_name = get_declaration_name(node);
                if !declaration_name.is_empty() {
                    let declarations = result.entry(declaration_name).or_default();
                    let last_declaration = declarations.last().copied().unwrap_or(Node::NIL);
                    // Check whether this declaration belongs to an "overload group".
                    if last_declaration.is_some()
                        && node.parent() == last_declaration.parent()
                        && node.symbol() == last_declaration.symbol()
                    {
                        // Overwrite the last declaration if it was an overload and this one is an implementation.
                        if node.body().is_some() && last_declaration.body().is_nil() {
                            let last = declarations.len() - 1;
                            declarations[last] = node;
                        }
                    } else {
                        declarations.push(node);
                    }
                }
                node.for_each_child(|child| visit(result, child));
            }
            SyntaxKind::ClassDeclaration
            | SyntaxKind::ClassExpression
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::TypeAliasDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::ModuleDeclaration
            | SyntaxKind::ImportEqualsDeclaration
            | SyntaxKind::ImportClause
            | SyntaxKind::NamespaceImport
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::TypeLiteral => {
                add_declaration(result, node);
                node.for_each_child(|child| visit(result, child));
            }
            SyntaxKind::ImportSpecifier | SyntaxKind::ExportSpecifier => {
                if node.property_name().is_some() {
                    add_declaration(result, node);
                }
            }
            SyntaxKind::Parameter
            | SyntaxKind::VariableDeclaration
            | SyntaxKind::BindingElement => {
                // Only consider parameter properties.
                if node.kind() == SyntaxKind::Parameter
                    && !has_syntactic_modifier(node, ModifierFlags::PARAMETER_PROPERTY_MODIFIER)
                {
                    return false;
                }
                let name = node.name();
                if name.is_some() {
                    if is_binding_pattern(name) {
                        name.for_each_child(|child| visit(result, child));
                    } else {
                        if node.initializer().is_some() {
                            visit(result, node.initializer());
                        }
                        add_declaration(result, node);
                    }
                }
            }
            SyntaxKind::EnumMember
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::PropertySignature => {
                add_declaration(result, node);
            }
            SyntaxKind::ExportDeclaration => {
                // Handle named exports case e.g.:
                //    export {a, b as B} from "mod";
                let export_clause = node.export_clause();
                if export_clause.is_some() {
                    if is_named_exports(export_clause) {
                        for element in export_clause.elements() {
                            visit(result, element);
                        }
                    } else {
                        visit(result, export_clause.name());
                    }
                }
            }
            SyntaxKind::ImportDeclaration => {
                let import_clause = node.import_clause();
                if import_clause.is_some() {
                    // Handle default import case e.g.:
                    //    import d from "mod";
                    if import_clause.name().is_some() {
                        add_declaration(result, import_clause.name());
                    }
                    // Handle named bindings in imports e.g.:
                    //    import * as NS from "mod";
                    //    import {a, b as B} from "mod";
                    let named_bindings = import_clause.named_bindings();
                    if named_bindings.is_some() {
                        if named_bindings.kind() == SyntaxKind::NamespaceImport {
                            add_declaration(result, named_bindings);
                        } else {
                            for element in named_bindings.elements() {
                                visit(result, element);
                            }
                        }
                    }
                }
            }
            SyntaxKind::BinaryExpression => {
                let kind = get_assignment_declaration_kind(node);
                if kind == JSDeclarationKind::EXPORTS_PROPERTY
                    || kind == JSDeclarationKind::THIS_PROPERTY
                    || kind == JSDeclarationKind::PROPERTY
                {
                    add_declaration(result, node);
                }
                node.for_each_child(|child| visit(result, child));
            }
            _ => {
                node.for_each_child(|child| visit(result, child));
            }
        }
        false
    }
    let mut result = FxHashMap::default();
    file.for_each_child(|child| visit(&mut result, child));
    result
}

// Go: ast.go:2959 GetDeclarationName
/// The plain text name of a declaration, or "" when it has none.
#[must_use]
pub fn get_declaration_name(declaration: Node) -> String {
    let name = get_non_assigned_name_of_declaration(declaration);
    if name.is_some() {
        if is_computed_property_name(name) {
            if is_string_or_numeric_literal_like(name.expression()) {
                return name.expression().text().to_string();
            }
            if is_property_access_expression(name.expression()) {
                return name.expression().name().text().to_string();
            }
        } else if is_property_name(name) {
            return name.text().to_string();
        }
    }
    String::new()
}
