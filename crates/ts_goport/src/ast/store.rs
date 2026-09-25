//! Per-file Go node stores: the nodes the ported Go parser creates.
//!
//! Go parser nodes are ordinary `*ast.Node` values made by `ast.NodeFactory`.
//! Here each parsed file gets one store. The store id is the file index in
//! `GoProgram::files`, so a store node is a normal `Node` handle: high 32
//! bits are the store id, low 32 bits are the slot index + 1.
//!
//! Each slot has a header (Go kind plus the mutable Go `NodeBase` fields:
//! parent, flags, loc) and, for a node slot, a leaked `ts_ast::Node` that
//! holds the node data. Child ids inside that data are slot indexes of the
//! same store:
//! - a child in the same file uses its own slot index;
//! - a child from another file or a synthetic child (Go shares the pointer)
//!   uses an alias slot, which `Node::new` resolves to that node;
//! - Go `nil` in a field that ts_ast stores as a required `NodeId` uses
//!   slot 0, which resolves to `Node::NIL`.
//!
//! `node.rs` reads kind, loc, flags and parent from the header for files that
//! have a store. Files of the legacy loader (ts_parser) never have a store,
//! so their reads do not change.
//!
//! Two phases:
//! - Build: the parser runs on one thread and writes the stores of that
//!   thread (`BUILD`). The header and the data can change until the parser
//!   finishes the file (`finishNode`, parent setting, JSDoc flags,
//!   reparser.go writes). Then the parser freezes the file.
//! - Detached: a parse worker (`files_parser.rs` prefetch) parses one file
//!   into a store with a provisional id (`DETACHED_STORE_BASE` + job) that
//!   only its thread sees (`DETACHED`). The loading thread adopts the
//!   finished store when the loader asks for that file
//!   (`adopt_detached_store`). The store then gets the next real id, so ids
//!   still follow the serial parse order.
//! - Frozen: `core::set_prog` calls `freeze_file_stores`, which moves every
//!   store into one leaked, read-only, process-wide slice (`FROZEN`). Node
//!   reads then need no thread-local and no `RefCell` borrow, and the slice
//!   can be read from any thread. Writes and new stores panic after this.
//!
//! Binder data is not stored here: it stays in `GoFile::node_bind`, indexed
//! by slot index.
//!
//! PORT: a program is either all legacy files or all store files. File ids
//! are store ids, so a store can only be made while no legacy program is
//! installed on this thread. One process installs one program.

use crate::prelude::*;
use std::sync::OnceLock;
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

/// The Go kind and the mutable Go `NodeBase` fields of a store node.
///
/// A nil or alias slot has kind `Unknown`, no flags, an undefined loc, and
/// its target (nil for slot 0) in `parent`.
#[derive(Clone, Copy, Debug)]
pub struct NodeHeader {
    /// Go `node.Parent`. Inside a store a parent in the same store is kept
    /// as a `LOCAL_STORE` handle; the read hooks return the real handle.
    pub parent: Node,
    pub loc: TextRange,
    pub flags: NodeFlags,
    pub kind: SyntaxKind,
    /// Set by `freeze_file_stores`: Go `GetSourceFileOfNode(node)` is the
    /// root of this store (`FileStore::root`). False means "walk the parents".
    source_file_is_root: bool,
}

impl NodeHeader {
    /// The header as the node reads see it: a parent in the same store (see
    /// `LOCAL_STORE`) becomes a handle of store `file`.
    #[inline]
    fn read(mut self, file: usize) -> Self {
        if self.parent.file_index() == LOCAL_STORE {
            self.parent = handle(file, slot_index(self.parent) as u32);
        }
        self
    }

    /// The stored form of `parent` for a node of store `file`.
    #[inline]
    fn stored_parent(file: usize, parent: Node) -> Node {
        if parent.is_some() && parent.file_index() == file {
            handle(LOCAL_STORE, slot_index(parent) as u32)
        } else {
            parent
        }
    }

    /// The header of a nil (`target` nil) or alias slot.
    const fn target(target: Node) -> Self {
        Self {
            parent: target,
            loc: TextRange::undefined(),
            flags: NodeFlags::NONE,
            kind: SyntaxKind::Unknown,
            source_file_is_root: false,
        }
    }
}

/// The Go nodes of one parsed file. Slot `i` is `headers[i]` and `nodes[i]`.
struct FileStore {
    file_name: &'static str,
    text: &'static str,
    headers: Vec<NodeHeader>,
    /// The ts_ast node (kind and data) of each node slot. `None` for the nil
    /// slot and alias slots.
    nodes: Vec<Option<&'static ts_ast::Node>>,
    /// Alias slot of each foreign node, so one node gets one slot. Emptied
    /// by `freeze_file_stores`.
    aliases: FxHashMap<Node, u32>,
    /// Set when the parser has finished the file.
    frozen: bool,
    /// Slot of the SourceFile node that `mark_source_file_roots` found when
    /// the file was frozen, or 0 (the nil slot).
    root_slot: u32,
    /// `file_store_parser_flags`, made on the parsing thread when the file
    /// is frozen. The loader takes it once.
    parser_flags: Option<Vec<NodeFlags>>,
    /// Go `file.jsdocCache`, set by `finishSourceFile`. Node reads use it
    /// until the program that holds this file is installed, so
    /// `freeze_file_stores` empties it.
    jsdoc_cache: FxHashMap<Node, &'static [Node]>,
    /// The SourceFile node of this store, set by `freeze_file_stores`.
    root: Node,
    /// Go `SourceFile.ECMALineMap()`, computed on first use after freeze
    /// and shared by every thread.
    ecma_line_starts: OnceLock<Box<[i32]>>,
}

thread_local! {
    /// The stores of this thread, while the parser runs.
    static BUILD: RefCell<Vec<FileStore>> = const { RefCell::new(Vec::new()) };
    /// The detached store of a parse worker and its provisional id.
    static DETACHED: RefCell<Option<(usize, FileStore)>> = const { RefCell::new(None) };
}

/// File index that marks a parent in the same store inside a stored
/// header. Reads give the handle of the store (`NodeHeader::read`), so a
/// store keeps its headers when its id changes (`adopt_detached_store`).
const LOCAL_STORE: usize = 0x7fff_ffff;

/// First provisional store id. Real store ids are file indexes and stay far
/// below it; synthetic node and flow ids are above every provisional id.
pub const DETACHED_STORE_BASE: usize = 0x8000_0000;
/// Number of provisional ids.
pub const DETACHED_STORE_LIMIT: usize = 0x4000_0000;

#[inline]
fn is_detached_id(file: usize) -> bool {
    (DETACHED_STORE_BASE..DETACHED_STORE_BASE + DETACHED_STORE_LIMIT).contains(&file)
}

/// All stores, read-only, after `freeze_file_stores`, with dense per-store
/// header and node tables for the hot node reads.
struct Frozen {
    stores: &'static [FileStore],
    headers: Box<[&'static [NodeHeader]]>,
    nodes: Box<[&'static [Option<&'static ts_ast::Node>]]>,
    /// `headers[file][i].kind`, packed. `Node::kind` reads only this.
    kinds: Box<[Box<[SyntaxKind]>]>,
    /// `try_resolve_store_id(file, i)` for every slot, computed once.
    /// `Node::new` reads only this.
    resolved: Box<[Box<[Node]>]>,
}

static FROZEN: OnceLock<Frozen> = OnceLock::new();

/// The frozen stores, or `None` while the parser runs.
#[inline]
fn frozen() -> Option<&'static [FileStore]> {
    FROZEN.get().map(|f| f.stores)
}

/// The handle of slot `index` in store `file`. Does not resolve aliases.
const fn handle(file: usize, index: u32) -> Node {
    Node(((file as u64) << 32) | (index as u64 + 1))
}

/// Slot index of a store handle.
#[inline]
fn slot_index(n: Node) -> usize {
    ((n.0 & 0xffff_ffff) - 1) as usize
}

fn with_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> R {
    if let Some(stores) = frozen() {
        return f(&stores[file]);
    }
    if is_detached_id(file) {
        return DETACHED.with(|d| match &*d.borrow() {
            Some((id, store)) if *id == file => f(store),
            _ => panic!("store {file:#x} is not the detached store of this thread"),
        });
    }
    BUILD.with(|s| f(&s.borrow()[file]))
}

fn with_store_mut<R>(file: usize, f: impl FnOnce(&mut FileStore) -> R) -> R {
    assert!(
        frozen().is_none(),
        "cannot change a node store after freeze"
    );
    if is_detached_id(file) {
        return DETACHED.with(|d| match &mut *d.borrow_mut() {
            Some((id, store)) if *id == file => f(store),
            _ => panic!("store {file:#x} is not the detached store of this thread"),
        });
    }
    BUILD.with(|s| f(&mut s.borrow_mut()[file]))
}

/// Writes the node slot of a store handle. Panics on a frozen store.
fn with_slot_mut<R>(
    n: Node,
    f: impl FnOnce(&mut &'static ts_ast::Node, &mut NodeHeader) -> R,
) -> R {
    with_store_mut(n.file_index(), |s| {
        assert!(!s.frozen, "cannot mutate a node of a finished file");
        let index = slot_index(n);
        match &mut s.nodes[index] {
            Some(node) => f(node, &mut s.headers[index]),
            None => panic!("store handle does not name a node slot"),
        }
    })
}

// ──────────────────────────────────────────────────────────────────────
// Stores
// ──────────────────────────────────────────────────────────────────────

/// Makes the store of the next parsed file and returns its id. Ids follow
/// parse order and are the file indexes in `GoProgram::files`.
pub fn new_file_store(file_name: &'static str, text: &'static str) -> usize {
    assert!(frozen().is_none(), "cannot make a node store after freeze");
    BUILD.with(|s| {
        let mut s = s.borrow_mut();
        assert!(
            crate::core::try_prog().is_none_or(|p| p.files.len() <= s.len()),
            "a legacy program is installed; file ids would collide with store ids"
        );
        s.push(FileStore::new(file_name, text));
        s.len() - 1
    })
}

impl FileStore {
    fn new(file_name: &'static str, text: &'static str) -> Self {
        Self {
            file_name,
            text,
            headers: vec![NodeHeader::target(Node::NIL)],
            nodes: vec![None],
            aliases: FxHashMap::default(),
            frozen: false,
            root_slot: NIL_SLOT,
            parser_flags: None,
            jsdoc_cache: FxHashMap::default(),
            root: Node::NIL,
            ecma_line_starts: OnceLock::new(),
        }
    }
}

// ──────────────────────────────────────────────────────────────────────
// Detached stores (parse workers)
// ──────────────────────────────────────────────────────────────────────

/// A finished store that a parse worker made with a provisional id. Only
/// `adopt_detached_store` can make it part of the program.
pub struct DetachedStore {
    id: usize,
    store: FileStore,
}

impl DetachedStore {
    /// The provisional id of the store.
    #[must_use]
    pub fn id(&self) -> usize {
        self.id
    }

    /// True when every node the store names is its own. A store that names
    /// a node of another store (an alias slot, for example a synthetic
    /// node of the worker) cannot be adopted.
    #[must_use]
    pub fn is_self_contained(&self) -> bool {
        self.store.frozen && self.store.aliases.is_empty()
    }
}

/// Makes the detached store of this thread with provisional id
/// `DETACHED_STORE_BASE + job` and returns that id. A parse worker parses
/// one file at a time; the store stays until `take_detached_file_store`.
pub fn new_detached_file_store(job: usize, file_name: &'static str, text: &'static str) -> usize {
    assert!(frozen().is_none(), "cannot make a node store after freeze");
    assert!(job < DETACHED_STORE_LIMIT, "too many detached stores");
    let id = DETACHED_STORE_BASE + job;
    DETACHED.with(|d| {
        let mut d = d.borrow_mut();
        assert!(d.is_none(), "this thread already has a detached store");
        *d = Some((id, FileStore::new(file_name, text)));
    });
    id
}

/// Removes the detached store of this thread, if any.
pub fn take_detached_file_store() -> Option<DetachedStore> {
    DETACHED
        .with(|d| d.borrow_mut().take())
        .map(|(id, store)| DetachedStore { id, store })
}

/// Maps the node handles of an adopted detached store to its real id.
#[derive(Clone, Copy, Debug)]
pub struct StoreRemap {
    from: usize,
    to: usize,
}

impl StoreRemap {
    /// The real store id.
    #[must_use]
    pub fn store(self) -> usize {
        self.to
    }

    /// `n` with the provisional store id replaced by the real one. Other
    /// handles (nil, other stores) do not change.
    #[inline]
    #[must_use]
    pub fn node(self, n: Node) -> Node {
        if n.is_some() && n.file_index() == self.from {
            handle(self.to, slot_index(n) as u32)
        } else {
            n
        }
    }
}

/// Gives a self-contained detached store the next real store id on this
/// thread, as `new_file_store` would have at this point, and returns the
/// handle map for the values the parse returned with it.
pub fn adopt_detached_store(detached: DetachedStore) -> StoreRemap {
    assert!(frozen().is_none(), "cannot adopt a node store after freeze");
    assert!(
        detached.is_self_contained(),
        "cannot adopt a store that names other stores"
    );
    let DetachedStore { id, mut store } = detached;
    BUILD.with(|s| {
        let mut s = s.borrow_mut();
        assert!(
            crate::core::try_prog().is_none_or(|p| p.files.len() <= s.len()),
            "a legacy program is installed; file ids would collide with store ids"
        );
        let remap = StoreRemap {
            from: id,
            to: s.len(),
        };
        store.jsdoc_cache = store
            .jsdoc_cache
            .iter()
            .map(|(&node, &jsdocs)| {
                let jsdocs: &'static [Node] = if jsdocs.iter().any(|&n| remap.node(n) != n) {
                    Box::leak(jsdocs.iter().map(|&n| remap.node(n)).collect())
                } else {
                    jsdocs
                };
                (remap.node(node), jsdocs)
            })
            .collect();
        s.push(store);
        remap
    })
}

/// Number of stores (on this thread while the parser runs).
#[must_use]
pub fn file_store_count() -> usize {
    match frozen() {
        Some(stores) => stores.len(),
        None => BUILD.with(|s| s.borrow().len()),
    }
}

/// True after `freeze_file_stores`. The program is installed then, and it
/// holds every store file.
#[inline]
#[must_use]
pub fn file_stores_frozen() -> bool {
    frozen().is_some()
}

/// True when file `file` was parsed by the ported parser.
#[inline]
#[must_use]
pub fn has_file_store(file: usize) -> bool {
    match FROZEN.get() {
        Some(f) => file < f.headers.len(),
        None if is_detached_id(file) => {
            DETACHED.with(|d| d.borrow().as_ref().is_some_and(|(id, _)| *id == file))
        }
        None => BUILD.with(|s| file < s.borrow().len()),
    }
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

/// Go `result.jsdocCache = p.createJSDocCache()` in `finishSourceFile`.
// PORT: the lists are leaked so reads can return `&'static` slices, like
// `GoFile::info.jsdoc_cache` after the program is installed.
pub fn set_file_store_js_doc_cache(file: usize, cache: &FxHashMap<Node, Vec<Node>>) {
    let cache = cache
        .iter()
        .map(|(node, jsdocs)| (*node, &*Box::leak(jsdocs.clone().into_boxed_slice())))
        .collect();
    with_store_mut(file, |s| s.jsdoc_cache = cache);
}

/// Go `file.jsdocCache[node]` of a store file whose program is not
/// installed yet.
#[must_use]
pub fn file_store_js_doc(file: usize, node: Node) -> Option<&'static [Node]> {
    with_store(file, |s| s.jsdoc_cache.get(&node).copied())
}

/// True when node reads of store file `file` must use the store, because
/// no installed program holds the file yet (the parser is still running).
#[must_use]
pub fn is_file_store_before_program(file: usize) -> bool {
    frozen().is_none()
        && has_file_store(file)
        && crate::core::try_prog().is_none_or(|p| p.files.len() <= file)
}

/// Ends the parse of a file. Header and data writes panic after this.
/// Headers cannot change after this, so it also marks the source file roots
/// (`mark_source_file_roots`) on the parsing thread.
pub fn freeze_file_store(file: usize) {
    with_store_mut(file, |s| {
        s.frozen = true;
        s.headers.shrink_to_fit();
        s.nodes.shrink_to_fit();
        mark_source_file_roots(s);
        s.parser_flags = Some(s.headers.iter().map(|h| h.flags).collect());
    });
}

#[must_use]
pub fn is_file_store_frozen(file: usize) -> bool {
    frozen().is_some() || with_store(file, |s| s.frozen)
}

/// Number of slots (nil, alias and node slots). Per-node vectors that are
/// indexed by `NodeId::index()` (`GoFile::node_bind`) need this length.
#[must_use]
pub fn file_store_slot_count(file: usize) -> usize {
    with_store(file, |s| s.headers.len())
}

/// The parser `node.Flags` of every slot, indexed by slot index. Nil and
/// alias slots give no flags. The loader fills `GoFile::parser_flags` from
/// this, so the binder reads the same flags as for a legacy file.
#[must_use]
pub fn file_store_parser_flags(file: usize) -> Vec<NodeFlags> {
    let computed = |s: &FileStore| s.headers.iter().map(|h| h.flags).collect();
    if frozen().is_some() {
        return with_store(file, computed);
    }
    with_store_mut(file, |s| {
        s.parser_flags.take().unwrap_or_else(|| computed(s))
    })
}

/// Moves every store of this thread into the process-wide read-only slice.
/// `core::set_prog` calls this once, when the program is installed. After
/// this, store writes and new stores panic.
// PORT: Go needs no freeze; its nodes are heap objects. The freeze also
// computes `NodeHeader::source_file_is_root` for `get_source_file_of_node`.
pub fn freeze_file_stores() {
    let mut stores = BUILD.with(|s| std::mem::take(&mut *s.borrow_mut()));
    for (file, store) in stores.iter_mut().enumerate() {
        if !store.frozen {
            // PORT: a store whose parse did not finish (a parse panic).
            store.frozen = true;
            store.headers.shrink_to_fit();
            store.nodes.shrink_to_fit();
            mark_source_file_roots(store);
        }
        store.aliases = FxHashMap::default();
        store.jsdoc_cache = FxHashMap::default();
        store.parser_flags = None;
        if store.root_slot != NIL_SLOT {
            store.root = handle(file, store.root_slot);
        }
    }
    let stores: &'static [FileStore] = Box::leak(stores.into_boxed_slice());
    let frozen = Frozen {
        stores,
        headers: stores.iter().map(|s| &s.headers[..]).collect(),
        nodes: stores.iter().map(|s| &s.nodes[..]).collect(),
        kinds: stores
            .iter()
            .map(|s| s.headers.iter().map(|h| h.kind).collect())
            .collect(),
        resolved: stores
            .iter()
            .enumerate()
            .map(|(file, s)| {
                (0..s.headers.len())
                    .map(|i| resolve_slot(file, i, &s.nodes, &s.headers))
                    .collect()
            })
            .collect(),
    };
    assert!(
        FROZEN.set(frozen).is_ok(),
        "node stores are already frozen; one process installs one program"
    );
}

/// Sets `store.root_slot` and `NodeHeader::source_file_is_root` of each node
/// slot whose Go parent walk (`GetSourceFileOfNode`) ends at that root.
/// Headers are frozen, so the walk result cannot change. A walk that leaves
/// the store (a synthetic or foreign parent) stays unmarked and is walked
/// at read time.
fn mark_source_file_roots(store: &mut FileStore) {
    // PORT: the parser makes the SourceFile node last, so the root is the
    // last SourceFile slot. Any other SourceFile node stays unmarked.
    let Some(root) = (0..store.headers.len())
        .rev()
        .find(|&i| store.nodes[i].is_some() && store.headers[i].kind == SyntaxKind::SourceFile)
    else {
        return;
    };
    store.root_slot = root as u32;

    const UNSEEN: u8 = 0;
    const ON_PATH: u8 = 1;
    const ROOT: u8 = 2;
    const NOT_ROOT: u8 = 3;
    let mut state = vec![UNSEEN; store.headers.len()];
    let mut path = Vec::new();
    // The parser makes a parent after its children, so most parents have a
    // higher slot. Walking the slots down finds them already marked.
    for start in (1..store.headers.len()).rev() {
        if store.nodes[start].is_none() {
            continue;
        }
        let header = &store.headers[start];
        let parent = header.parent;
        if header.kind != SyntaxKind::SourceFile
            && parent.file_index() == LOCAL_STORE
            && matches!(state[slot_index(parent)], ROOT | NOT_ROOT)
        {
            let result = state[slot_index(parent)];
            state[start] = result;
            store.headers[start].source_file_is_root = result == ROOT;
            continue;
        }
        let mut cur = start;
        let result = loop {
            match state[cur] {
                ROOT | NOT_ROOT => break state[cur],
                // A parent cycle: Go never returns. Leave it to the walk.
                ON_PATH => break NOT_ROOT,
                _ => {}
            }
            state[cur] = ON_PATH;
            path.push(cur);
            let header = &store.headers[cur];
            if header.kind == SyntaxKind::SourceFile {
                break if cur == root { ROOT } else { NOT_ROOT };
            }
            let parent = header.parent;
            if parent.file_index() != LOCAL_STORE {
                break NOT_ROOT;
            }
            cur = slot_index(parent);
        };
        for i in path.drain(..) {
            state[i] = result;
            store.headers[i].source_file_is_root = result == ROOT;
        }
    }
}

// ──────────────────────────────────────────────────────────────────────
// Read hooks for node.rs and core.rs
// ──────────────────────────────────────────────────────────────────────

/// Hook for `Node::new(file, id)` on a store file: the Go node that a child
/// id inside store `NodeData` stands for.
#[inline]
#[must_use]
pub fn resolve_store_id(file: usize, id: ts_ast::NodeId) -> Node {
    let index = id.index();
    let resolve = |s: &FileStore| match s.nodes[index] {
        Some(_) => handle(file, index as u32),
        // The nil slot or an alias slot: the target is in the header.
        None => s.headers[index].parent,
    };
    if let Some(f) = FROZEN.get() {
        return match f.nodes[file][index] {
            Some(_) => handle(file, index as u32),
            None => f.headers[file][index].parent,
        };
    }
    with_store(file, resolve)
}

/// Hook for `raw(n)`: the ts_ast node (Go kind and data) of a store node.
#[inline]
#[must_use]
pub fn store_ast_node(n: Node) -> &'static ts_ast::Node {
    let get =
        |s: &FileStore| s.nodes[slot_index(n)].expect("store handle does not name a node slot");
    if let Some(f) = FROZEN.get() {
        return f.nodes[n.file_index()][slot_index(n)]
            .expect("store handle does not name a node slot");
    }
    with_store(n.file_index(), get)
}

/// Hook for `Node::kind`, `flags`, `parent` and `loc` on a store node.
#[inline]
#[must_use]
pub fn store_header(n: Node) -> NodeHeader {
    let get = |s: &FileStore| {
        let index = slot_index(n);
        debug_assert!(
            s.nodes[index].is_some(),
            "store handle does not name a node slot"
        );
        s.headers[index].read(n.file_index())
    };
    if let Some(f) = FROZEN.get() {
        let (file, index) = (n.file_index(), slot_index(n));
        debug_assert!(
            f.nodes[file][index].is_some(),
            "store handle does not name a node slot"
        );
        return f.headers[file][index].read(file);
    }
    with_store(n.file_index(), get)
}

/// The header of `n` when it is a store node (kind, parser flags, parent,
/// loc): one table lookup after freeze, one thread-local access before.
/// `None` for nil, synthetic and legacy nodes. With it a node read needs no
/// separate `has_file_store` call.
#[inline]
#[must_use]
pub fn try_store_header(n: Node) -> Option<NodeHeader> {
    if n.is_nil() {
        return None;
    }
    let (file, index) = (n.file_index(), slot_index(n));
    if let Some(f) = FROZEN.get() {
        return f.headers.get(file).map(|headers| headers[index].read(file));
    }
    if is_detached_id(file) {
        return DETACHED.with(|d| match &*d.borrow() {
            Some((id, store)) if *id == file => Some(store.headers[index].read(file)),
            _ => None,
        });
    }
    BUILD.with(|s| {
        s.borrow()
            .get(file)
            .map(|store| store.headers[index].read(file))
    })
}

/// Go `node.Kind` of a store node after freeze. `None` before freeze and
/// for nil, synthetic and legacy nodes.
#[inline]
#[must_use]
pub fn frozen_store_kind(n: Node) -> Option<SyntaxKind> {
    if n.is_nil() {
        return None;
    }
    let kinds = FROZEN.get()?.kinds.get(n.file_index())?;
    Some(kinds[slot_index(n)])
}

/// The header of a store node after freeze, by reference, so a read of one
/// field does not copy the whole header. The parent is still in its stored
/// form (see `LOCAL_STORE`). `None` as for `frozen_store_kind`.
#[inline]
fn frozen_header(n: Node) -> Option<&'static NodeHeader> {
    if n.is_nil() {
        return None;
    }
    let headers = FROZEN.get()?.headers.get(n.file_index())?;
    Some(&headers[slot_index(n)])
}

/// Parser `node.Flags` of a store node after freeze (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_flags(n: Node) -> Option<NodeFlags> {
    frozen_header(n).map(|h| h.flags)
}

/// Go `node.Loc` of a store node after freeze (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_loc(n: Node) -> Option<TextRange> {
    frozen_header(n).map(|h| h.loc)
}

/// Go `node.Parent` of a store node after freeze (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_parent(n: Node) -> Option<Node> {
    frozen_header(n).map(|h| h.read(n.file_index()).parent)
}

/// `store_ast_node(n)` when `n` is a store node, in one lookup (see
/// `try_store_header`). `None` for nil, synthetic and legacy nodes.
#[inline]
#[must_use]
pub fn try_store_ast_node(n: Node) -> Option<&'static ts_ast::Node> {
    if n.is_nil() {
        return None;
    }
    let (file, index) = (n.file_index(), slot_index(n));
    let node =
        |slot: Option<&'static ts_ast::Node>| slot.expect("store handle does not name a node slot");
    if let Some(f) = FROZEN.get() {
        return f.nodes.get(file).map(|nodes| node(nodes[index]));
    }
    if is_detached_id(file) {
        return DETACHED.with(|d| match &*d.borrow() {
            Some((id, store)) if *id == file => Some(node(store.nodes[index])),
            _ => None,
        });
    }
    BUILD.with(|s| s.borrow().get(file).map(|store| node(store.nodes[index])))
}

/// `resolve_store_id(file, id)` when `file` has a store, in one lookup (see
/// `try_store_header`). `None` when it has none.
#[inline]
#[must_use]
pub fn try_resolve_store_id(file: usize, id: ts_ast::NodeId) -> Option<Node> {
    let index = id.index();
    let resolve = |nodes: &[Option<&'static ts_ast::Node>], headers: &[NodeHeader]| {
        Some(resolve_slot(file, index, nodes, headers))
    };
    if let Some(f) = FROZEN.get() {
        return f.resolved.get(file).map(|resolved| resolved[index]);
    }
    if is_detached_id(file) {
        return DETACHED.with(|d| match &*d.borrow() {
            Some((id, store)) if *id == file => resolve(&store.nodes, &store.headers),
            _ => None,
        });
    }
    BUILD.with(|s| {
        s.borrow()
            .get(file)
            .and_then(|store| resolve(&store.nodes, &store.headers))
    })
}

/// The node for slot `index` of store `file`: the slot itself when it holds
/// a node, else the handle stored in its header.
fn resolve_slot(
    file: usize,
    index: usize,
    nodes: &[Option<&'static ts_ast::Node>],
    headers: &[NodeHeader],
) -> Node {
    match nodes[index] {
        Some(_) => handle(file, index as u32),
        None => headers[index].parent,
    }
}

/// `try_resolve_store_id(file, _)` for every slot of store `file`, indexed
/// by `NodeId::index()`. `None` before freeze and for a file without a
/// store.
#[inline]
#[must_use]
pub fn frozen_resolved(file: usize) -> Option<&'static [Node]> {
    Some(&FROZEN.get()?.resolved.get(file)?[..])
}

/// Go `SourceFile.ECMALineMap()` of store file `file` after freeze. It is
/// computed once and shared by every thread. `None` before freeze or for a
/// file without a store.
#[must_use]
pub fn frozen_file_ecma_line_starts(file: usize) -> Option<&'static [i32]> {
    let store = frozen()?.get(file)?;
    Some(store.ecma_line_starts.get_or_init(|| {
        crate::scanner_util::compute_ecma_line_starts(store.text).into_boxed_slice()
    }))
}

/// Go `GetSourceFileOfNode(n)` in O(1), when `n` is a frozen store node
/// whose parent walk ends at its store root. `None` means "walk".
#[inline]
#[must_use]
pub fn frozen_source_file_of_node(n: Node) -> Option<Node> {
    if n.is_nil() {
        return None;
    }
    let f = FROZEN.get()?;
    let file = n.file_index();
    f.headers.get(file)?[slot_index(n)]
        .source_file_is_root
        .then(|| f.stores[file].root)
}

// ──────────────────────────────────────────────────────────────────────
// Go field writes during the parse
// ──────────────────────────────────────────────────────────────────────

/// Runs `f` on the header of `n` when `n` is a node slot of a store of this
/// thread (built or detached), with one thread-local access. False when
/// `n` is not a store node of this thread (for example a synthetic node).
/// Panics on a finished store, like `with_slot_mut`.
fn try_with_build_header(n: Node, f: impl FnOnce(&mut NodeHeader)) -> bool {
    if n.is_nil() || FROZEN.get().is_some() {
        return false;
    }
    let file = n.file_index();
    let write = |s: &mut FileStore| {
        assert!(!s.frozen, "cannot mutate a node of a finished file");
        let index = slot_index(n);
        assert!(
            s.nodes[index].is_some(),
            "store handle does not name a node slot"
        );
        f(&mut s.headers[index]);
    };
    if is_detached_id(file) {
        return DETACHED.with(|d| match &mut *d.borrow_mut() {
            Some((id, store)) if *id == file => {
                write(store);
                true
            }
            _ => false,
        });
    }
    BUILD.with(|s| match s.borrow_mut().get_mut(file) {
        Some(store) => {
            write(store);
            true
        }
        None => false,
    })
}

/// Go `finishNode` writes `node.Loc = loc` and `node.Flags |= flags` on a
/// node of an unfinished store, in one store access. False (nothing
/// written) when `n` is not a store node of this thread.
pub fn finish_store_node(n: Node, loc: TextRange, flags: NodeFlags) -> bool {
    try_with_build_header(n, |h| {
        h.loc = loc;
        h.flags |= flags;
    })
}

/// Go `node.Parent = parent` on a node of an unfinished store, in one store
/// access. False (nothing written) when `n` is not a store node of this
/// thread.
pub fn try_set_store_node_parent(n: Node, parent: Node) -> bool {
    let parent = NodeHeader::stored_parent(n.file_index(), parent);
    try_with_build_header(n, |h| h.parent = parent)
}

/// Go `node.Parent = parent` on a node of an unfrozen file.
pub fn set_store_node_parent(n: Node, parent: Node) {
    let parent = NodeHeader::stored_parent(n.file_index(), parent);
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
        let index = s.headers.len() as u32;
        s.headers.push(NodeHeader {
            parent: Node::NIL,
            loc: TextRange::undefined(),
            flags: NodeFlags::NONE,
            kind,
            source_file_is_root: false,
        });
        s.nodes.push(Some(node));
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
        let index = s.headers.len() as u32;
        s.headers.push(NodeHeader::target(n));
        s.nodes.push(None);
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

    #[test]
    fn adopted_detached_parse_equals_a_serial_parse() {
        use crate::frontend::parser::{
            ParsedSourceFile, SourceFileParseOptions, adopt_detached_parse, parse_source_file,
            parse_source_file_detached,
        };
        let text =
            "/** doc */\nexport function f(a: number) { return a + 1; }\nlet x = <T>(y: T) => y;\n";
        let opts = SourceFileParseOptions {
            file_name: "/a.ts".to_string(),
            ..Default::default()
        };
        let serial = parse_source_file(&opts, text, ScriptKind::TS);
        let worker_opts = opts.clone();
        let detached = std::thread::spawn(move || {
            parse_source_file_detached(7, &worker_opts, text, ScriptKind::TS)
        })
        .join()
        .unwrap();
        assert_eq!(detached.store.id(), DETACHED_STORE_BASE + 7);
        let adopted: ParsedSourceFile = adopt_detached_parse(detached, &opts);

        assert_eq!(adopted.store, serial.store + 1);
        let slots = file_store_slot_count(serial.store);
        assert_eq!(file_store_slot_count(adopted.store), slots);
        let to_serial = |n: Node| {
            if n.is_some() && n.file_index() == adopted.store {
                handle(serial.store, slot_index(n) as u32)
            } else {
                n
            }
        };
        for index in 1..slots as u32 {
            let (a, b) = (handle(serial.store, index), handle(adopted.store, index));
            let (ha, hb) = (store_header(a), store_header(b));
            assert_eq!(ha.kind, hb.kind);
            assert_eq!(ha.flags, hb.flags);
            assert_eq!(ha.loc, hb.loc);
            assert_eq!(ha.parent, to_serial(hb.parent));
        }
        assert_eq!(serial.root, to_serial(adopted.root));
        assert_eq!(serial.imports.len(), adopted.imports.len());
        assert_eq!(serial.jsdoc_cache.len(), adopted.jsdoc_cache.len());
        for (node, jsdocs) in &adopted.jsdoc_cache {
            let expected: Vec<Node> = jsdocs.iter().map(|&n| to_serial(n)).collect();
            assert_eq!(serial.jsdoc_cache[&to_serial(*node)], expected);
            assert_eq!(file_store_js_doc(adopted.store, *node), Some(&jsdocs[..]));
        }
    }
}
