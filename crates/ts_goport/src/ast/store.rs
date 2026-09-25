//! Per-file Go node stores: the nodes the ported Go parser creates.
//!
//! Go parser nodes are ordinary `*ast.Node` values made by `ast.NodeFactory`.
//! Here each parsed file gets one store. The store id is the file index in
//! `GoProgram::files`, so a store node is a normal `Node` handle: high 32
//! bits are the store id, low 32 bits are the slot index + 1.
//!
//! Each slot holds a leaked `ts_ast::Node` (Go kind and `NodeData`) plus the
//! mutable Go `NodeBase` header (parent, flags, loc). Child ids inside that
//! data are slot indexes of the same store:
//! - a child in the same file uses its own slot index;
//! - a child from another file or a synthetic child (Go shares the pointer)
//!   uses an alias slot, which `Node::new` resolves to that node;
//! - Go `nil` in a field that ts_ast stores as a required `NodeId` uses
//!   slot 0, which resolves to `Node::NIL`.
//!
//! `node.rs` reads kind, loc, flags and parent from here for files that have
//! a store. Files of the legacy loader (ts_parser) never have a store, so
//! their reads do not change.
//!
//! The header and the data can change until the parser finishes the file
//! (`finishNode`, parent setting, JSDoc flags, reparser.go writes). Then the
//! loader freezes the store. Binder data is not stored here: it stays in
//! `GoFile::node_bind`, indexed by slot index.
//!
//! PORT: a program is either all legacy files or all store files. File ids
//! are store ids, so a store can only be made while no legacy program is
//! installed on this thread.

use crate::prelude::*;
use std::cell::Cell;
use ts_ast::NodeData;

/// Slot 0: Go `nil` stored in a ts_ast field that has no `Option`.
const NIL_SLOT: u32 = 0;

/// Position that marks a Go `nil` list in a ts_ast list field that has no
/// `Option`. Go positions are byte offsets, so they never reach it, and
/// `u32::MAX` is already the undefined position `-1`.
// PORT: ts_ast cannot change under the R97 rules. For store nodes the factory
// stores Go `nil` in a required list field as an empty list at this position,
// and `NodeList::is_nil` reads it back as nil (plan risk 1).
pub const NIL_LIST_POS: u32 = u32::MAX - 1;

/// The mutable Go `NodeBase` fields of a store node.
#[derive(Clone, Copy, Debug)]
pub struct NodeHeader {
    pub parent: Node,
    pub flags: NodeFlags,
    pub loc: TextRange,
}

/// One store slot.
enum StoreSlot {
    /// Go `nil`. Only slot 0.
    Nil,
    /// A node of another file (or a synthetic node) used as a child.
    Alias(Node),
    /// A node the factory created in this file.
    Node {
        node: &'static ts_ast::Node,
        header: NodeHeader,
    },
}

/// The Go nodes of one parsed file.
struct FileStore {
    file_name: &'static str,
    text: &'static str,
    slots: Vec<StoreSlot>,
    /// Alias slot of each foreign node, so one node gets one slot.
    aliases: FxHashMap<Node, u32>,
    /// Set when the parser has finished the file.
    frozen: bool,
}

thread_local! {
    static STORES: RefCell<Vec<FileStore>> = const { RefCell::new(Vec::new()) };
    /// `STORES.len()`, readable without a `RefCell` borrow. `node.rs` checks
    /// it on every read, so the legacy path stays cheap.
    static STORE_COUNT: Cell<usize> = const { Cell::new(0) };
}

/// The handle of slot `index` in store `file`. Does not resolve aliases.
const fn handle(file: usize, index: u32) -> Node {
    Node(((file as u64) << 32) | (index as u64 + 1))
}

/// Slot index of a store handle.
fn slot_index(n: Node) -> usize {
    ((n.0 & 0xffff_ffff) - 1) as usize
}

fn with_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> R {
    STORES.with(|s| f(&s.borrow()[file]))
}

fn with_store_mut<R>(file: usize, f: impl FnOnce(&mut FileStore) -> R) -> R {
    STORES.with(|s| f(&mut s.borrow_mut()[file]))
}

/// Reads the node slot of a store handle.
fn with_slot<R>(n: Node, f: impl FnOnce(&'static ts_ast::Node, &NodeHeader) -> R) -> R {
    with_store(n.file_index(), |s| match &s.slots[slot_index(n)] {
        StoreSlot::Node { node, header } => f(node, header),
        _ => panic!("store handle does not name a node slot"),
    })
}

/// Writes the node slot of a store handle. Panics on a frozen store.
fn with_slot_mut<R>(
    n: Node,
    f: impl FnOnce(&mut &'static ts_ast::Node, &mut NodeHeader) -> R,
) -> R {
    with_store_mut(n.file_index(), |s| {
        assert!(!s.frozen, "cannot mutate a node of a finished file");
        match &mut s.slots[slot_index(n)] {
            StoreSlot::Node { node, header } => f(node, header),
            _ => panic!("store handle does not name a node slot"),
        }
    })
}

// ──────────────────────────────────────────────────────────────────────
// Stores
// ──────────────────────────────────────────────────────────────────────

/// Makes the store of the next parsed file and returns its id. Ids follow
/// parse order and are the file indexes in `GoProgram::files`.
pub fn new_file_store(file_name: &'static str, text: &'static str) -> usize {
    let count = STORE_COUNT.get();
    assert!(
        crate::core::try_prog().is_none_or(|p| p.files.len() <= count),
        "a legacy program is installed; file ids would collide with store ids"
    );
    STORES.with(|s| {
        let mut s = s.borrow_mut();
        s.push(FileStore {
            file_name,
            text,
            slots: vec![StoreSlot::Nil],
            aliases: FxHashMap::default(),
            frozen: false,
        });
        STORE_COUNT.set(s.len());
        s.len() - 1
    })
}

/// Number of stores on this thread.
#[must_use]
pub fn file_store_count() -> usize {
    STORE_COUNT.get()
}

/// True when file `file` was parsed by the ported parser.
#[inline]
#[must_use]
pub fn has_file_store(file: usize) -> bool {
    file < STORE_COUNT.get()
}

/// True when `n` is a node of a store file.
#[inline]
#[must_use]
pub fn is_store_node(n: Node) -> bool {
    n.is_some() && has_file_store(n.file_index())
}

/// Go `file.FileName()` of a store file.
#[must_use]
pub fn file_store_file_name(file: usize) -> &'static str {
    with_store(file, |s| s.file_name)
}

/// Go `file.Text()` of a store file.
#[must_use]
pub fn file_store_text(file: usize) -> &'static str {
    with_store(file, |s| s.text)
}

/// Ends the parse of a file. Header and data writes panic after this.
pub fn freeze_file_store(file: usize) {
    with_store_mut(file, |s| s.frozen = true);
}

#[must_use]
pub fn is_file_store_frozen(file: usize) -> bool {
    with_store(file, |s| s.frozen)
}

/// Number of slots (nil, alias and node slots). Per-node vectors that are
/// indexed by `NodeId::index()` (`GoFile::node_bind`) need this length.
#[must_use]
pub fn file_store_slot_count(file: usize) -> usize {
    with_store(file, |s| s.slots.len())
}

/// The parser `node.Flags` of every slot, indexed by slot index. Nil and
/// alias slots give no flags. The loader fills `GoFile::parser_flags` from
/// this, so the binder reads the same flags as for a legacy file.
#[must_use]
pub fn file_store_parser_flags(file: usize) -> Vec<NodeFlags> {
    with_store(file, |s| {
        s.slots
            .iter()
            .map(|slot| match slot {
                StoreSlot::Node { header, .. } => header.flags,
                _ => NodeFlags::NONE,
            })
            .collect()
    })
}

// ──────────────────────────────────────────────────────────────────────
// Read hooks for node.rs and core.rs
// ──────────────────────────────────────────────────────────────────────

/// Hook for `Node::new(file, id)` on a store file: the Go node that a child
/// id inside store `NodeData` stands for.
#[must_use]
pub fn resolve_store_id(file: usize, id: ts_ast::NodeId) -> Node {
    with_store(file, |s| match &s.slots[id.index()] {
        StoreSlot::Nil => Node::NIL,
        StoreSlot::Alias(target) => *target,
        StoreSlot::Node { .. } => handle(file, id.index() as u32),
    })
}

/// Hook for `raw(n)`: the ts_ast node (Go kind and data) of a store node.
#[must_use]
pub fn store_ast_node(n: Node) -> &'static ts_ast::Node {
    with_slot(n, |node, _| node)
}

/// Hook for `Node::flags`, `parent` and `loc` on a store node.
#[must_use]
pub fn store_header(n: Node) -> NodeHeader {
    with_slot(n, |_, header| *header)
}

// ──────────────────────────────────────────────────────────────────────
// Go field writes during the parse
// ──────────────────────────────────────────────────────────────────────

/// Go `node.Parent = parent` on a node of an unfrozen file.
pub fn set_store_node_parent(n: Node, parent: Node) {
    with_slot_mut(n, |_, h| h.parent = parent);
}

/// Go `node.Loc = loc` on a node of an unfrozen file.
pub fn set_store_node_loc(n: Node, loc: TextRange) {
    with_slot_mut(n, |_, h| h.loc = loc);
}

/// Go `node.Flags = flags` on a node of an unfrozen file.
pub fn set_store_node_flags(n: Node, flags: NodeFlags) {
    with_slot_mut(n, |_, h| h.flags = flags);
}

/// Go write to a data field of a node of an unfrozen file (reparser.go,
/// `internIdentifier`). The new data replaces the old; the old node leaks.
pub fn replace_store_node_data(n: Node, data: NodeData) {
    with_slot_mut(n, |node, _| {
        debug_assert!(
            data.matches_syntax_kind(node.kind),
            "{:?} does not fit its NodeData",
            node.kind
        );
        *node = leak_ast_node(node.kind, data);
    });
}

// ──────────────────────────────────────────────────────────────────────
// Allocation (used by factory.rs through `NodeFactory::for_file`)
// ──────────────────────────────────────────────────────────────────────

/// A leaked ts_ast node. Only kind and data are read for store and
/// synthetic nodes; the header lives in the slot.
fn leak_ast_node(kind: SyntaxKind, data: NodeData) -> &'static ts_ast::Node {
    Box::leak(Box::new(ts_ast::Node {
        kind,
        flags: ts_ast::NodeFlags(0),
        range: ts_range(TextRange::undefined()),
        parent: None,
        data,
    }))
}

/// Go `newNode(kind, data, hooks)` in store `file`: `Loc =
/// UndefinedTextRange()`, nil parent, no flags.
pub fn alloc_store_node(file: usize, kind: SyntaxKind, data: NodeData) -> Node {
    debug_assert!(
        data.matches_syntax_kind(kind),
        "{kind:?} does not fit its NodeData"
    );
    let node = leak_ast_node(kind, data);
    with_store_mut(file, |s| {
        assert!(!s.frozen, "cannot create a node in a finished file");
        let index = s.slots.len() as u32;
        s.slots.push(StoreSlot::Node {
            node,
            header: NodeHeader {
                parent: Node::NIL,
                flags: NodeFlags::NONE,
                loc: TextRange::undefined(),
            },
        });
        handle(file, index)
    })
}

/// The store-local id that stands for `n` inside `NodeData` of store `file`.
/// Nil maps to the nil slot. A node of another file gets (or reuses) an
/// alias slot.
#[must_use]
pub fn store_child_id(file: usize, n: Node) -> ts_ast::NodeId {
    if n.is_nil() {
        return ts_ast::NodeId::new(NIL_SLOT);
    }
    if n.file_index() == file {
        return ts_ast::NodeId::new(slot_index(n) as u32);
    }
    with_store_mut(file, |s| {
        if let Some(&index) = s.aliases.get(&n) {
            return ts_ast::NodeId::new(index);
        }
        let index = s.slots.len() as u32;
        s.slots.push(StoreSlot::Alias(n));
        s.aliases.insert(n, index);
        ts_ast::NodeId::new(index)
    })
}

/// Like `store_child_id`, for ts_ast fields that are `Option<NodeId>`.
#[must_use]
pub fn store_opt_child_id(file: usize, n: Node) -> Option<ts_ast::NodeId> {
    if n.is_nil() {
        None
    } else {
        Some(store_child_id(file, n))
    }
}

/// A Go `core.TextRange` in ts_ast form (`-1` is stored as `u32::MAX`).
fn ts_range(loc: TextRange) -> ts_core::TextRange {
    ts_core::TextRange {
        start: ts_core::TextPos::new(loc.pos() as u32),
        end: ts_core::TextPos::new(loc.end() as u32),
    }
}

/// The ts_ast list for a list of store `file`.
fn ts_list(file: usize, nodes: &[Node], loc: TextRange) -> ts_ast::NodeList {
    ts_ast::NodeList {
        range: ts_range(loc),
        nodes: nodes.iter().map(|&n| store_child_id(file, n)).collect(),
        has_trailing_comma: false,
    }
}

/// Go `f.NewNodeList(nodes)` followed by `list.Loc = loc`, in store `file`.
#[must_use]
pub fn new_store_node_list(file: usize, nodes: &[Node], loc: TextRange) -> NodeList {
    let list: &'static ts_ast::NodeList = Box::leak(Box::new(ts_list(file, nodes, loc)));
    NodeList {
        file: file as u32,
        list: Some(list),
    }
}

/// Go `f.NewModifierList(nodes)` followed by `list.Loc = loc`, in store
/// `file`. `ModifierFlags = ModifiersToFlags(nodes)` as in Go.
#[must_use]
pub fn new_store_modifier_list(file: usize, nodes: &[Node], loc: TextRange) -> ModifierList {
    let list: &'static ts_ast::ModifierList = Box::leak(Box::new(ts_ast::ModifierList {
        list: ts_list(file, nodes, loc),
        flags: ts_ast::ModifierFlags(modifiers_to_flags(nodes).0 as u32),
    }));
    ModifierList {
        file: file as u32,
        list: Some(list),
    }
}

/// A list value to store inside new `NodeData` of store `file`. Go stores
/// the `*NodeList` pointer. A list of the same store is copied as is; any
/// other list is rebuilt over ids of this store with its own `Loc`.
// PORT: ts_ast stores lists by value, so `NodeList` equality on the copy is
// false where Go compares equal pointers (plan risk 2).
#[must_use]
pub fn store_list_value(file: usize, list: NodeList) -> Option<ts_ast::NodeList> {
    if list.is_nil() {
        return None;
    }
    let l = list.list?;
    if list.file as usize == file {
        return Some(l.clone());
    }
    let nodes = list.nodes().to_vec();
    Some(ts_list(file, &nodes, list.loc()))
}

/// Like `store_list_value` for a list field that ts_ast requires. Go `nil`
/// becomes an empty list at `NIL_LIST_POS`, which `NodeList::is_nil` reads
/// as nil.
#[must_use]
pub fn store_req_list_value(file: usize, list: NodeList) -> ts_ast::NodeList {
    store_list_value(file, list).unwrap_or_else(|| ts_ast::NodeList {
        range: ts_core::TextRange {
            start: ts_core::TextPos::new(NIL_LIST_POS),
            end: ts_core::TextPos::new(NIL_LIST_POS),
        },
        nodes: Vec::new(),
        has_trailing_comma: false,
    })
}

/// A modifier list value to store inside new `NodeData` of store `file`.
#[must_use]
pub fn store_modifiers_value(file: usize, modifiers: ModifierList) -> Option<ts_ast::ModifierList> {
    let m = modifiers.list?;
    if modifiers.file as usize == file {
        return Some(m.clone());
    }
    let nodes = modifiers.nodes().to_vec();
    Some(ts_ast::ModifierList {
        list: ts_list(file, &nodes, modifiers.loc()),
        flags: ts_ast::ModifierFlags(modifiers_to_flags(&nodes).0 as u32),
    })
}

/// True when `l` is the Go `nil` marker of a required list field.
#[inline]
#[must_use]
pub fn is_nil_list_marker(l: &ts_ast::NodeList) -> bool {
    l.range.start.get() == NIL_LIST_POS && l.range.end.get() == NIL_LIST_POS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_factory_writes_into_the_file_store() {
        let file = new_file_store("/a.ts", "a.b");
        let f = NodeFactory::for_file(file);
        let a = f.new_identifier("a");
        let b = f.new_identifier("b");
        set_node_loc(a, TextRange::new(0, 1));
        let q = f.new_qualified_name(a, b);
        set_node_parent(a, q);
        set_node_flags(q, NodeFlags::AMBIENT);

        assert_eq!(q.file_index(), file);
        assert_eq!(q.kind(), SyntaxKind::QualifiedName);
        assert_eq!(q.left(), a);
        assert_eq!(a.parent(), q);
        assert_eq!(a.loc(), TextRange::new(0, 1));
        assert_eq!(q.loc(), TextRange::undefined());
        assert_eq!(q.flags(), NodeFlags::AMBIENT);
        assert_eq!(source_file_text(q), "a.b");

        // A synthetic child is an alias slot that resolves to the same node.
        let s = NodeFactory::new().new_identifier("s");
        let q2 = f.new_qualified_name(q, s);
        assert_eq!(q2.right(), s);

        // Go nil in a required list field reads back as nil.
        let decls = f.new_variable_declaration_list(NodeList::NIL, NodeFlags::NONE);
        assert!(decls.declarations().is_nil());
        let list = f.new_node_list_with_loc(&[a], TextRange::new(0, 3));
        assert_eq!(list.loc(), TextRange::new(0, 3));
        assert_eq!(list.nodes().get(0), a);

        freeze_file_store(file);
        assert!(std::panic::catch_unwind(|| set_node_parent(b, q)).is_err());
    }
}
