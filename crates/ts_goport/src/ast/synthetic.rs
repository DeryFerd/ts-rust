//! Synthetic AST nodes: the nodes Go creates with `ast.NodeFactory`.
//!
//! Go factory nodes are ordinary `*ast.Node` values. Here a synthetic node is
//! a `Node` handle whose file index is `SYNTHETIC_NODE_FILE`. Its low 32 bits
//! index a thread-local slot list (like `SYNTHETIC_FLOW_FILE` for flow nodes).
//!
//! Each node slot holds a leaked `ts_ast::Node` (kind and `NodeData`), so every
//! accessor in `node.rs` and `fields.rs` that matches on `NodeData` works on
//! synthetic nodes without changes. Child ids inside that data are ids in the
//! synthetic id space:
//! - a synthetic child uses its own slot index;
//! - a parsed child (Go shares the pointer) uses an alias slot. `Node::new`
//!   resolves an alias slot to the parsed node, so identity is kept:
//!   `synthetic.name() == parsed_name` is true, like Go pointer equality;
//! - Go `nil` in a field that ts_ast stores as a required `NodeId` uses slot 0,
//!   which resolves to `Node::NIL`.
//!
//! Go mutates factory nodes after creation (`node.Parent = p`, `node.Loc = l`,
//! `node.Flags |= f`, `node.FlowNodeData().FlowNode = f`,
//! `node.AsX().Symbol = s`). Those fields live in the slot, not in the leaked
//! `ts_ast::Node`, and `node.rs` reads them through the hooks below.
//!
//! PORT: parsed nodes are immutable. The setters panic on a parsed node. Go
//! code that writes a field of a parsed node needs its own port decision.

use crate::prelude::*;
use ts_ast::NodeData;

/// File index of synthetic nodes. `SYNTHETIC_FLOW_FILE` is `0xffff_ffff`.
pub const SYNTHETIC_NODE_FILE: usize = 0xffff_fffe;

/// Slot 0: Go `nil` stored in a ts_ast field that has no `Option`.
const NIL_SLOT: u32 = 0;

/// One synthetic slot.
enum Slot {
    /// Go `nil`. Only slot 0.
    Nil,
    /// A parsed node used as a child of a synthetic node.
    Alias(Node),
    /// A node the factory created.
    Node(SyntheticNode),
}

/// The mutable Go `NodeBase` fields of a factory node.
struct SyntheticNode {
    node: &'static ts_ast::Node,
    parent: Node,
    flags: NodeFlags,
    loc: TextRange,
    /// Go `DeclarationData().Symbol`, `FlowNodeData().FlowNode`, ... Replaced
    /// (and the old value leaked) on each write, so `bind()` can return
    /// `&'static`. Writes are rare.
    bind: &'static NodeBindData,
    /// Go `SyntheticExpression.Type.(*Type)`. Nil for other kinds.
    synthetic_type: TypeId,
}

struct SyntheticArena {
    slots: Vec<Slot>,
    /// Alias slot of each parsed node, so one parsed node gets one slot.
    aliases: FxHashMap<Node, u32>,
}

impl SyntheticArena {
    fn new() -> Self {
        Self { slots: vec![Slot::Nil], aliases: FxHashMap::default() }
    }
}

static EMPTY_BIND: NodeBindData = NodeBindData {
    symbol: SymbolId::NIL,
    local_symbol: SymbolId::NIL,
    locals: SymbolTable::NIL,
    next_container: Node::NIL,
    flow_node: FlowNodeId::NIL,
    end_flow_node: FlowNodeId::NIL,
    return_flow_node: FlowNodeId::NIL,
    added_flags: NodeFlags::NONE,
};

thread_local! {
    static ARENA: RefCell<SyntheticArena> = RefCell::new(SyntheticArena::new());
}

/// The handle of slot `index`. Does not resolve aliases.
const fn handle(index: u32) -> Node {
    Node(((SYNTHETIC_NODE_FILE as u64) << 32) | (index as u64 + 1))
}

/// Slot index of a synthetic handle.
fn slot_index(n: Node) -> usize {
    ((n.0 & 0xffff_ffff) - 1) as usize
}

/// True when `n` is a node that the factory created.
#[must_use]
pub fn is_synthetic_node(n: Node) -> bool {
    n.is_some() && n.file_index() == SYNTHETIC_NODE_FILE
}

/// Hook for `Node::new(SYNTHETIC_NODE_FILE, id)`: the Go node that a child id
/// inside synthetic `NodeData` stands for.
#[must_use]
pub fn resolve_synthetic_id(id: ts_ast::NodeId) -> Node {
    ARENA.with(|a| match &a.borrow().slots[id.index()] {
        Slot::Nil => Node::NIL,
        Slot::Alias(target) => *target,
        Slot::Node(_) => handle(id.index() as u32),
    })
}

/// Reads the node slot of a synthetic handle.
fn with_node<R>(n: Node, f: impl FnOnce(&SyntheticNode) -> R) -> R {
    ARENA.with(|a| match &a.borrow().slots[slot_index(n)] {
        Slot::Node(s) => f(s),
        _ => panic!("synthetic handle does not name a node slot"),
    })
}

/// Writes the node slot of a synthetic handle. Panics on a parsed node.
fn with_node_mut<R>(n: Node, f: impl FnOnce(&mut SyntheticNode) -> R) -> R {
    assert!(is_synthetic_node(n), "cannot mutate a parsed node (kind {:?})", n.kind());
    ARENA.with(|a| match &mut a.borrow_mut().slots[slot_index(n)] {
        Slot::Node(s) => f(s),
        _ => panic!("synthetic handle does not name a node slot"),
    })
}

// ──────────────────────────────────────────────────────────────────────
// Read hooks for node.rs / fields.rs
// ──────────────────────────────────────────────────────────────────────

/// Hook for `raw(n)`: the ts_ast node (kind and data) of a synthetic node.
#[must_use]
pub fn synthetic_ast_node(n: Node) -> &'static ts_ast::Node {
    with_node(n, |s| s.node)
}

/// The ts_ast node of any node, parsed or synthetic. For code outside
/// `node.rs` that reads ts_ast data directly.
#[must_use]
pub fn ast_node_of(n: Node) -> &'static ts_ast::Node {
    assert!(n.is_some(), "nil node dereference");
    if n.file_index() == SYNTHETIC_NODE_FILE {
        return synthetic_ast_node(n);
    }
    prog().files[n.file_index()]
        .source
        .parse
        .arena
        .get(n.node_id())
        .expect("node is not in its file arena")
}

/// The ts_ast data of any node, parsed or synthetic.
#[must_use]
pub fn ast_data_of(n: Node) -> &'static NodeData {
    &ast_node_of(n).data
}

/// Hook for `Node::flags` on a synthetic node.
#[must_use]
pub fn synthetic_flags(n: Node) -> NodeFlags {
    with_node(n, |s| s.flags)
}

/// Hook for `Node::parent` on a synthetic node.
#[must_use]
pub fn synthetic_parent(n: Node) -> Node {
    with_node(n, |s| s.parent)
}

/// Hook for `Node::loc` on a synthetic node.
#[must_use]
pub fn synthetic_loc(n: Node) -> TextRange {
    with_node(n, |s| s.loc)
}

/// Hook for `Node::bind` on a synthetic node.
#[must_use]
pub fn synthetic_bind(n: Node) -> &'static NodeBindData {
    with_node(n, |s| s.bind)
}

/// Go `node.AsSyntheticExpression().Type.(*Type)`.
#[must_use]
pub fn synthetic_expression_type(n: Node) -> TypeId {
    debug_assert!(n.kind() == SyntaxKind::SyntheticExpression);
    with_node(n, |s| s.synthetic_type)
}

// ──────────────────────────────────────────────────────────────────────
// Go field writes on factory nodes
// ──────────────────────────────────────────────────────────────────────

/// Go `node.Parent = parent`.
pub fn set_node_parent(n: Node, parent: Node) {
    with_node_mut(n, |s| s.parent = parent);
}

/// Go `node.Loc = loc`.
pub fn set_node_loc(n: Node, loc: TextRange) {
    with_node_mut(n, |s| s.loc = loc);
}

/// Go `node.Flags = flags`.
pub fn set_node_flags(n: Node, flags: NodeFlags) {
    with_node_mut(n, |s| s.flags = flags);
}

/// Changes the binder data of a factory node: Go
/// `node.FlowNodeData().FlowNode = f`, `node.AsX().Symbol = s`, ...
pub fn update_node_bind(n: Node, f: impl FnOnce(&mut NodeBindData)) {
    with_node_mut(n, |s| {
        let mut bind = *s.bind;
        f(&mut bind);
        s.bind = Box::leak(Box::new(bind));
    });
}

/// Go `node.FlowNodeData().FlowNode = flow`.
pub fn set_node_flow_node(n: Node, flow: FlowNodeId) {
    update_node_bind(n, |b| b.flow_node = flow);
}

/// Go `node.AsX().Symbol = symbol` (declaration data).
pub fn set_node_symbol(n: Node, symbol: SymbolId) {
    update_node_bind(n, |b| b.symbol = symbol);
}

/// Go `node.AsX().LocalSymbol = symbol`.
pub fn set_node_local_symbol(n: Node, symbol: SymbolId) {
    update_node_bind(n, |b| b.local_symbol = symbol);
}

/// Go `node.AsX().Locals = locals`.
pub fn set_node_locals(n: Node, locals: SymbolTable) {
    update_node_bind(n, |b| b.locals = locals);
}

// ──────────────────────────────────────────────────────────────────────
// Allocation (used by factory.rs)
// ──────────────────────────────────────────────────────────────────────

/// Go `newNode(kind, data, hooks)`: a new factory node with
/// `Loc = UndefinedTextRange()`, nil parent, no flags and no binder data.
pub fn alloc_synthetic_node(kind: SyntaxKind, data: NodeData) -> Node {
    debug_assert!(data.matches_syntax_kind(kind), "{kind:?} does not fit its NodeData");
    let node: &'static ts_ast::Node = Box::leak(Box::new(ts_ast::Node {
        kind,
        flags: ts_ast::NodeFlags(0),
        range: undefined_ts_range(),
        parent: None,
        data,
    }));
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        let index = a.slots.len() as u32;
        a.slots.push(Slot::Node(SyntheticNode {
            node,
            parent: Node::NIL,
            flags: NodeFlags::NONE,
            loc: TextRange::undefined(),
            bind: &EMPTY_BIND,
            synthetic_type: TypeId::NIL,
        }));
        handle(index)
    })
}

/// Sets the Go `SyntheticExpression.Type` of a new node.
pub(crate) fn set_synthetic_expression_type(n: Node, t: TypeId) {
    with_node_mut(n, |s| s.synthetic_type = t);
}

/// The synthetic-space id that stands for `n` inside synthetic `NodeData`.
/// Nil maps to the nil slot. A parsed node gets (or reuses) an alias slot.
#[must_use]
pub fn synthetic_child_id(n: Node) -> ts_ast::NodeId {
    if n.is_nil() {
        return ts_ast::NodeId::new(NIL_SLOT);
    }
    if n.file_index() == SYNTHETIC_NODE_FILE {
        return ts_ast::NodeId::new(slot_index(n) as u32);
    }
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        if let Some(&index) = a.aliases.get(&n) {
            return ts_ast::NodeId::new(index);
        }
        let index = a.slots.len() as u32;
        a.slots.push(Slot::Alias(n));
        a.aliases.insert(n, index);
        ts_ast::NodeId::new(index)
    })
}

/// Like `synthetic_child_id`, for ts_ast fields that are `Option<NodeId>`.
#[must_use]
pub fn synthetic_opt_child_id(n: Node) -> Option<ts_ast::NodeId> {
    if n.is_nil() { None } else { Some(synthetic_child_id(n)) }
}

/// Go `core.UndefinedTextRange()` in ts_ast form. `TextPos` is `u32`; the
/// `as i32` in `node.rs` `text_range_of` turns `u32::MAX` back into `-1`.
fn undefined_ts_range() -> ts_core::TextRange {
    ts_range(TextRange::undefined())
}

/// A Go `core.TextRange` in ts_ast form (`-1` is stored as `u32::MAX`).
fn ts_range(loc: TextRange) -> ts_core::TextRange {
    ts_core::TextRange { start: ts_core::TextPos::new(loc.pos() as u32), end: ts_core::TextPos::new(loc.end() as u32) }
}

/// The ts_ast list for a synthetic node's list field.
fn ts_list(nodes: &[Node], loc: TextRange, has_trailing_comma: bool) -> ts_ast::NodeList {
    ts_ast::NodeList {
        range: ts_range(loc),
        nodes: nodes.iter().map(|&n| synthetic_child_id(n)).collect(),
        has_trailing_comma,
    }
}

/// Go `f.NewNodeList(nodes)` with a given `Loc`.
// PORT: Go list `Loc` is mutable; here a synthetic list fixes its `Loc` at
// creation. Callers that set `list.Loc` later pass it here instead.
#[must_use]
pub fn new_synthetic_node_list(nodes: &[Node], loc: TextRange) -> NodeList {
    let list: &'static ts_ast::NodeList = Box::leak(Box::new(ts_list(nodes, loc, false)));
    NodeList { file: SYNTHETIC_NODE_FILE as u32, list: Some(list) }
}

/// Go `f.NewModifierList(nodes)` with a given `Loc`. `modifier_flags()` in
/// node.rs recomputes `ModifiersToFlags(nodes)`, as the Go factory does.
#[must_use]
pub fn new_synthetic_modifier_list(nodes: &[Node], loc: TextRange) -> ModifierList {
    let list: &'static ts_ast::ModifierList = Box::leak(Box::new(ts_ast::ModifierList {
        list: ts_list(nodes, loc, false),
        flags: ts_ast::ModifierFlags(modifiers_to_flags(nodes).0 as u32),
    }));
    ModifierList { file: SYNTHETIC_NODE_FILE as u32, list: Some(list) }
}

/// A list value to store inside new synthetic `NodeData`. Go stores the
/// `*NodeList` pointer; a list that already is synthetic is copied as is, and
/// a parsed list is rebuilt over alias ids with its own `Loc`.
// PORT: ts_ast stores lists by value, so a synthetic node that takes a
// parsed (or another synthetic) list gets a copy. `NodeList` equality on the
// copy is false where Go compares equal pointers.
#[must_use]
pub fn synthetic_list_value(list: NodeList) -> Option<ts_ast::NodeList> {
    let l = list.list?;
    if list.file as usize == SYNTHETIC_NODE_FILE {
        return Some(l.clone());
    }
    let nodes = list.nodes().to_vec();
    Some(ts_list(&nodes, list.loc(), l.has_trailing_comma))
}

/// Like `synthetic_list_value` for a list field that ts_ast requires. Go
/// `nil` becomes an empty list with an undefined `Loc`.
// PORT: Go keeps `nil`; `NodeList::is_nil` on that field is false here.
#[must_use]
pub fn synthetic_req_list_value(list: NodeList) -> ts_ast::NodeList {
    synthetic_list_value(list).unwrap_or_else(|| ts_list(&[], TextRange::undefined(), false))
}

/// A modifier list value to store inside new synthetic `NodeData`.
#[must_use]
pub fn synthetic_modifiers_value(modifiers: ModifierList) -> Option<ts_ast::ModifierList> {
    let m = modifiers.list?;
    if modifiers.file as usize == SYNTHETIC_NODE_FILE {
        return Some(m.clone());
    }
    let nodes = modifiers.nodes().to_vec();
    Some(ts_ast::ModifierList {
        list: ts_list(&nodes, modifiers.loc(), m.list.has_trailing_comma),
        flags: ts_ast::ModifierFlags(modifiers_to_flags(&nodes).0 as u32),
    })
}
