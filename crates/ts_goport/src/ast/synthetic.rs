//! Synthetic AST nodes: the nodes Go creates with `ast.NodeFactory`.
//!
//! Go factory nodes are ordinary `*ast.Node` values. Here a synthetic node is
//! a `Node` handle whose file index is `SYNTHETIC_NODE_FILE`. Its low 32 bits
//! index a thread-local slot list (like `SYNTHETIC_FLOW_FILE` for flow nodes).
//!
//! Each node slot names a `crate::astdata::Node` (kind and `NodeData`) that the
//! thread owns, so the accessors in `node.rs` and `fields.rs` that match on
//! `NodeData` work on synthetic nodes too. Child ids inside that data are ids
//! in the synthetic id space:
//! - a synthetic child uses its own slot index;
//! - a parsed child (Go shares the pointer) uses an alias slot. `Node::new`
//!   resolves an alias slot to the parsed node, so identity is kept:
//!   `synthetic.name() == parsed_name` is true, like Go pointer equality;
//! - Go `nil` in a field that astdata stores as a required `NodeId` uses slot 0,
//!   which resolves to `Node::NIL`.
//!
//! Go mutates factory nodes after creation (`node.Parent = p`, `node.Loc = l`,
//! `node.Flags |= f`, `node.FlowNodeData().FlowNode = f`,
//! `node.AsX().Symbol = s`). Those fields live in the slot, not in the
//! `crate::astdata::Node`, and `node.rs` reads them through the hooks below.
//!
//! Ownership: the slots, the node data, the factory lists and the node
//! slices that reads make belong to the thread's arena. Nothing hands out a
//! reference into them that outlives a read. Data is read inside a closure
//! (`with_ast_node`, `with_ast_data`, or the `with_data!` macro in hot code),
//! and a list field through a selector (`list_of!`, `modifiers_of!`). A list
//! of synthetic data is a `SyntheticList` handle (an index), not a pointer,
//! and a text is interned (`synthetic_text`). Only a parsed node gives
//! `&'static` data (`static_ast_node`). A checker worker of a released
//! program frees all of it (`free_synthetic_nodes`, called by
//! `program::release_program`). A one-program process leaks it at the end
//! instead (`forget_synthetic_nodes`), like the checker itself.
//!
//! Owners: the language server makes the nodes of every program version on
//! its dispatch thread. There each program version owns the entries made
//! while it is current (`open_synthetic_owner`), and its release frees them
//! (`free_synthetic_owner`, called by `ls_program`). Other entries belong to
//! the thread (the base owner). The tables are in chunks, and each chunk
//! has one owner, so a handle stays an index and keeps Go pointer identity
//! while its owner lives. A freed chunk leaves a hole that is never used
//! again: a read of a freed entry panics, and a handle never names another
//! node. The rules:
//! - a new node, a factory list and a list copy go to the current program
//!   version when it is an owner on this thread and no base scope
//!   (`enter_base_synthetic_owner`) is open, else to the base owner;
//! - a data write (`replace_node_data`, `set_node_kind`) goes to the owner
//!   of the node, so a base node never points into a program version;
//! - alias slots and node slices always go to the base owner.
//!
//! Code whose nodes a cache keeps across program versions (the token cache,
//! lazy JSDoc, parses) opens a base scope.
//! PORT: the Go GC frees request garbage at once and checker nodes with
//! their checker. Here they stay until their program version is released.
//!
//! PORT: parsed nodes are immutable. The setters panic on a parsed node,
//! except on a node of a ported-parser file that the parser has not finished
//! (`ast/store.rs`). Go code that writes a field of a parsed node needs its
//! own port decision.

use crate::astdata::NodeData;
use crate::prelude::*;
use std::cell::{Cell, OnceCell};

/// File index of synthetic nodes. `SYNTHETIC_FLOW_FILE` is `0xffff_ffff`.
pub const SYNTHETIC_NODE_FILE: usize = 0xffff_fffe;

/// Slot 0: Go `nil` stored in a astdata field that has no `Option`.
const NIL_SLOT: u32 = 0;

/// One synthetic slot.
#[derive(Clone)]
enum Slot {
    /// Go `nil`. Only slot 0.
    Nil,
    /// A parsed node used as a child of a synthetic node.
    Alias(Node),
    /// A node the factory created.
    Node(SyntheticNode),
}

/// The mutable Go `NodeBase` fields of a factory node.
#[derive(Clone)]
struct SyntheticNode {
    /// The astdata node (kind and data): an entry of `SyntheticArena::datas`.
    /// A Go write to a data field or to the kind adds a new entry and moves
    /// the node to it, so a list handle taken before the write still reads
    /// the old list, like a Go `*NodeList` pointer.
    data: u32,
    parent: Node,
    flags: NodeFlags,
    loc: TextRange,
    /// Go `DeclarationData().Symbol`, `FlowNodeData().FlowNode`, ... `None`
    /// until the first write.
    bind: Option<Box<NodeBindData>>,
    /// Go `SyntheticExpression.Type.(*Type)`. Nil for other kinds.
    synthetic_type: TypeId,
    /// The Go `ast.SourceFile` fields of a factory SourceFile. `None` for
    /// other kinds.
    source_file: Option<Box<SyntheticSourceFileData>>,
}

/// The Go `ast.SourceFile` fields (other than `Statements` and
/// `EndOfFileToken`, which are in the node data) of a SourceFile that the
/// factory made: `NewSourceFile` sets the first group, `copyFrom` and later
/// Go writes (`result.AsSourceFile().IsDeclarationFile = true`) set the rest.
// PORT: a parsed SourceFile keeps these fields in `SourceFileInfo`. astdata
// node data cannot hold them, so a factory SourceFile keeps them in its slot.
// Go `parseOptions` is kept as its file name and path; the external module
// indicator options are only read by the parser. `ContainsNonASCII` and
// `Identifiers` are not in `SourceFileInfo`, so `copyFrom` cannot copy them
// from a parsed file and they are not kept.
#[derive(Clone, Debug, Default)]
pub struct SyntheticSourceFileData {
    // Fields set by NewSourceFile
    pub file_name: &'static str,
    pub path: String,
    pub text: &'static str,

    // Fields set by copyFrom (Go "fields set by parser") and later writes
    pub language_variant: LanguageVariant,
    pub script_kind: ScriptKind,
    pub is_declaration_file: bool,
    pub uses_uri_style_node_core_modules: Tristate,
    pub imports: Vec<Node>,
    pub module_augmentations: Vec<Node>,
    pub ambient_module_names: Vec<String>,
    pub comment_directives: Vec<CommentDirective>,
    pub pragmas: Vec<Pragma>,
    pub referenced_files: Vec<FileReference>,
    pub type_reference_directives: Vec<FileReference>,
    pub lib_reference_directives: Vec<FileReference>,
    pub common_js_module_indicator: Node,
    pub external_module_indicator: Node,
}

/// A list that the factory made (`new_synthetic_node_list`,
/// `new_synthetic_modifier_list`) or that a read copied
/// (`copy_synthetic_list`).
#[derive(Clone)]
enum OwnList {
    Nodes(crate::astdata::NodeList),
    Modifiers(crate::astdata::ModifierList),
}

impl OwnList {
    fn get(&self) -> AnyList<'_> {
        match self {
            Self::Nodes(l) => AnyList::Nodes(l),
            Self::Modifiers(m) => AnyList::Modifiers(m),
        }
    }
}

/// Bytes per chunk of `SyntheticArena::slots`, `datas` and `lists`.
// PERF: 14 KiB is jemalloc's largest small size class, and small classes
// pack densely in slabs. A larger chunk is a large allocation, which starts
// at a random cache line offset and so touches one page more (10% for a
// 40 KiB chunk).
const CHUNK_BYTES: usize = 14 * 1024;

/// Slots per chunk of `SyntheticArena::slots`.
const SLOT_CHUNK: usize = CHUNK_BYTES / size_of::<Slot>();
const _: () = assert!(SLOT_CHUNK >= 128);

/// Cells per chunk of `SyntheticArena::datas`. The `Rc` header is 16 bytes.
const DATA_CHUNK: usize = (CHUNK_BYTES - 16) / size_of::<OnceCell<crate::astdata::Node>>();

/// Lists per chunk of `SyntheticArena::lists`.
const LIST_CHUNK: usize = CHUNK_BYTES / size_of::<OwnList>();

/// A chunk of `SyntheticArena::datas`: cells that fill in order.
type DataChunk = Rc<[OnceCell<crate::astdata::Node>]>;

/// The panic of a read of an entry whose owner was freed.
const FREED: &str = "synthetic node of a released program version is read";

/// The owner of an arena chunk (see "Owners" in the module comment).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OwnerKey {
    /// The thread. Its chunks go only with the whole arena.
    Base,
    /// A language server program version (`GoProgram::id`).
    Program(u32),
}

/// The chunk numbers of one owner, oldest first. New entries of the owner
/// fill the last chunk of each table until it is full.
#[derive(Default)]
struct OwnerChunks {
    slots: Vec<u32>,
    datas: Vec<u32>,
    /// The number of filled cells in the last chunk of `datas`.
    data_fill: u32,
    lists: Vec<u32>,
}

/// The synthetic nodes of one thread. Each table is a list of chunks, and
/// each chunk has one owner. Entry `i` of a table with `N` entries per
/// chunk is entry `i % N` of chunk `i / N`. A freed chunk is `None`. Chunk
/// numbers only grow, so an index never names a second entry.
struct SyntheticArena {
    /// Node slots, in chunks of `SLOT_CHUNK`.
    slots: Vec<Option<Vec<Slot>>>,
    /// The owner of each chunk of `slots`.
    slot_owner: Vec<OwnerKey>,
    /// Alias slot of each parsed node, so one parsed node gets one slot.
    aliases: FxHashMap<Node, u32>,
    /// The astdata nodes of the node slots (see `SyntheticNode::data`), in
    /// chunks of `DATA_CHUNK`. A read holds the chunk of its node (an `Rc`),
    /// so it can hold the node while the arena is not borrowed, even when
    /// the owner of the chunk is freed meanwhile. A new node fills the next
    /// cell (`OnceCell::set` needs no `&mut`), so it can be added while such
    /// a read runs.
    // PERF: one allocation per chunk. An `Rc` per node made each 40-byte
    // node a 64-byte allocation plus an 8-byte pointer (goport_typesyms on
    // effect: +16% peak memory).
    datas: Vec<Option<DataChunk>>,
    /// Factory lists (`SyntheticList::Own`), in chunks of `LIST_CHUNK`. A
    /// chunk never grows past its capacity, so a list keeps its address
    /// (`synthetic_list_ptr`).
    lists: Vec<Option<Vec<OwnList>>>,
    /// Node slices that node reads made (`SyntheticList::Slice`), where Go
    /// allocates a new slice on each call. They belong to the thread.
    slices: Vec<Box<[Node]>>,
    /// The chunks of the thread (the base owner).
    base: OwnerChunks,
    /// The chunks of each program version that is an owner on this thread,
    /// by `GoProgram::id`.
    owners: FxHashMap<u32, OwnerChunks>,
    /// The last program that `current_owner` looked up, and its owner.
    last: Option<(&'static GoProgram, OwnerKey)>,
    /// The number of slots made on this thread, freed or not.
    slots_made: usize,
}

impl SyntheticArena {
    fn new() -> Self {
        let mut arena = Self {
            slots: Vec::new(),
            slot_owner: Vec::new(),
            aliases: FxHashMap::default(),
            datas: Vec::new(),
            lists: Vec::new(),
            slices: Vec::new(),
            base: OwnerChunks::default(),
            owners: FxHashMap::default(),
            last: None,
            slots_made: 0,
        };
        let nil = arena.push_slot(OwnerKey::Base, Slot::Nil);
        debug_assert_eq!(nil, NIL_SLOT);
        arena
    }

    /// The owner of a new node, factory list or list copy: the current
    /// program version when it is an owner on this thread and no base scope
    /// is open, else the thread.
    #[inline]
    fn current_owner(&mut self) -> OwnerKey {
        if self.owners.is_empty() || BASE_SCOPES.with(Cell::get) > 0 {
            return OwnerKey::Base;
        }
        let Some(program) = crate::core::try_prog() else {
            return OwnerKey::Base;
        };
        if let Some((last, owner)) = self.last
            && std::ptr::eq(last, program)
        {
            return owner;
        }
        let owner = if self.owners.contains_key(&program.id) {
            OwnerKey::Program(program.id)
        } else {
            OwnerKey::Base
        };
        self.last = Some((program, owner));
        owner
    }

    /// The chunks of `owner`, which must be open.
    fn chunks(&self, owner: OwnerKey) -> &OwnerChunks {
        match owner {
            OwnerKey::Base => &self.base,
            OwnerKey::Program(id) => self.owners.get(&id).expect("synthetic owner is not open"),
        }
    }

    /// `chunks` to write.
    fn chunks_mut(&mut self, owner: OwnerKey) -> &mut OwnerChunks {
        match owner {
            OwnerKey::Base => &mut self.base,
            OwnerKey::Program(id) => self
                .owners
                .get_mut(&id)
                .expect("synthetic owner is not open"),
        }
    }

    /// Slot `index`. Panics when its owner was freed.
    #[inline]
    fn slot(&self, index: usize) -> &Slot {
        &self.slots[index / SLOT_CHUNK].as_ref().expect(FREED)[index % SLOT_CHUNK]
    }

    /// `slot` to write.
    fn slot_mut(&mut self, index: usize) -> &mut Slot {
        &mut self.slots[index / SLOT_CHUNK].as_mut().expect(FREED)[index % SLOT_CHUNK]
    }

    /// Adds a slot of `owner` and returns its index.
    fn push_slot(&mut self, owner: OwnerKey, slot: Slot) -> u32 {
        let open = self
            .chunks(owner)
            .slots
            .last()
            .copied()
            .filter(|&c| self.slots[c as usize].as_ref().expect(FREED).len() < SLOT_CHUNK);
        let c = match open {
            Some(c) => c,
            None => {
                let c = new_chunk_number(self.slots.len(), SLOT_CHUNK);
                self.slots.push(Some(Vec::with_capacity(SLOT_CHUNK)));
                self.slot_owner.push(owner);
                self.chunks_mut(owner).slots.push(c);
                c
            }
        };
        let chunk = self.slots[c as usize].as_mut().expect(FREED);
        chunk.push(slot);
        let index = c as usize * SLOT_CHUNK + chunk.len() - 1;
        self.slots_made += 1;
        index as u32
    }

    /// The astdata node of data entry `index`. Panics when its owner was
    /// freed.
    #[inline]
    fn data(&self, index: u32) -> &crate::astdata::Node {
        let i = index as usize;
        self.datas[i / DATA_CHUNK].as_ref().expect(FREED)[i % DATA_CHUNK]
            .get()
            .expect("synthetic node data entry is not filled")
    }

    /// Adds a data entry of `owner` and returns its index.
    fn push_data(&mut self, owner: OwnerKey, node: crate::astdata::Node) -> u32 {
        let chunks = self.chunks(owner);
        let fill = chunks.data_fill;
        let open = chunks
            .datas
            .last()
            .copied()
            .filter(|_| (fill as usize) < DATA_CHUNK);
        let (c, cell) = match open {
            Some(c) => (c, fill),
            None => {
                let c = new_chunk_number(self.datas.len(), DATA_CHUNK);
                self.datas
                    .push(Some((0..DATA_CHUNK).map(|_| OnceCell::new()).collect()));
                self.chunks_mut(owner).datas.push(c);
                (c, 0)
            }
        };
        self.chunks_mut(owner).data_fill = cell + 1;
        assert!(
            self.datas[c as usize].as_ref().expect(FREED)[cell as usize]
                .set(node)
                .is_ok(),
            "synthetic node data entry is filled twice"
        );
        (c as usize * DATA_CHUNK + cell as usize) as u32
    }

    /// The factory list of entry `index`. Panics when its owner was freed.
    #[inline]
    fn own_list(&self, index: u32) -> &OwnList {
        let i = index as usize;
        &self.lists[i / LIST_CHUNK].as_ref().expect(FREED)[i % LIST_CHUNK]
    }

    /// Adds a factory list of `owner` and returns its index.
    fn push_list(&mut self, owner: OwnerKey, list: OwnList) -> u32 {
        let open = self
            .chunks(owner)
            .lists
            .last()
            .copied()
            .filter(|&c| self.lists[c as usize].as_ref().expect(FREED).len() < LIST_CHUNK);
        let c = match open {
            Some(c) => c,
            None => {
                let c = new_chunk_number(self.lists.len(), LIST_CHUNK);
                self.lists.push(Some(Vec::with_capacity(LIST_CHUNK)));
                self.chunks_mut(owner).lists.push(c);
                c
            }
        };
        let chunk = self.lists[c as usize].as_mut().expect(FREED);
        chunk.push(list);
        (c as usize * LIST_CHUNK + chunk.len() - 1) as u32
    }

    /// The node slot of synthetic handle `n`.
    fn node(&self, n: Node) -> &SyntheticNode {
        match self.slot(slot_index(n)) {
            Slot::Node(s) => s,
            _ => panic!("synthetic handle does not name a node slot"),
        }
    }

    /// The Go node that synthetic-space id `index` stands for.
    fn resolve(&self, index: usize) -> Node {
        match self.slot(index) {
            Slot::Nil => Node::NIL,
            Slot::Alias(target) => *target,
            Slot::Node(_) => handle(index as u32),
        }
    }

    /// The list that `list` names. Panics on a node slice.
    fn list(&self, list: SyntheticList) -> AnyList<'_> {
        match list {
            SyntheticList::Field { data, sel } => sel(&self.data(data).data)
                .flatten()
                .expect("synthetic list field is not in its node data"),
            SyntheticList::Own { index } => self.own_list(index).get(),
            SyntheticList::Slice { .. } => panic!("a node slice is not a NodeList"),
        }
    }
}

/// The number of a new chunk in a table of `len` chunks with `per_chunk`
/// entries each. Entry ids are `u32` and are not used again, so a thread
/// that makes about 4 billion entries of one kind runs out of them.
fn new_chunk_number(len: usize, per_chunk: usize) -> u32 {
    assert!(
        (len + 1) * per_chunk < u32::MAX as usize,
        "synthetic entry ids exhausted"
    );
    len as u32
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
    /// The number of open base scopes on this thread
    /// (`enter_base_synthetic_owner`).
    static BASE_SCOPES: Cell<u32> = const { Cell::new(0) };
}

/// False when `GOPORT_SYNTHETIC_OWNERS=0`: then no program version becomes
/// an owner, and every entry belongs to its thread, as before owners (for
/// A/B runs, and as a fallback).
fn owners_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| !matches!(std::env::var("GOPORT_SYNTHETIC_OWNERS").as_deref(), Ok("0")))
}

/// Makes program version `id` an owner on this thread: the synthetic
/// entries made while it is current go to its own chunks, until
/// `free_synthetic_owner(id)` frees them. `ls_program` calls it for each
/// language server program version. Other threads and programs have no
/// owners, so all their entries belong to their thread.
pub fn open_synthetic_owner(id: u32) {
    if !owners_enabled() {
        return;
    }
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        assert!(
            a.owners.insert(id, OwnerChunks::default()).is_none(),
            "synthetic owner {id} is opened twice"
        );
        a.last = None;
    });
}

/// Frees the synthetic entries of program version `id` on this thread.
/// Their handles must not be read again: a read panics. It does nothing
/// when `id` is not an owner. A read that holds a node (`with_ast_node`)
/// keeps the data chunk of that node until the read ends.
// Not in Go: the GC frees the nodes that nothing reaches.
pub fn free_synthetic_owner(id: u32) {
    let freed = ARENA.with(|a| {
        let mut a = a.borrow_mut();
        let chunks = a.owners.remove(&id)?;
        a.last = None;
        let slots: Vec<_> = chunks
            .slots
            .iter()
            .map(|&c| a.slots[c as usize].take())
            .collect();
        let datas: Vec<_> = chunks
            .datas
            .iter()
            .map(|&c| a.datas[c as usize].take())
            .collect();
        let lists: Vec<_> = chunks
            .lists
            .iter()
            .map(|&c| a.lists[c as usize].take())
            .collect();
        Some((slots, datas, lists))
    });
    drop(freed);
}

/// New synthetic entries of this thread belong to the thread (the base
/// owner) while the scope lives, whatever program is current. Open it
/// around code whose nodes a cache keeps across program versions: the token
/// cache, lazy JSDoc and parses.
#[must_use = "new entries go to the thread only while the scope lives"]
pub fn enter_base_synthetic_owner() -> BaseOwnerScope {
    BASE_SCOPES.with(|scopes| scopes.set(scopes.get() + 1));
    BaseOwnerScope {
        _not_send: std::marker::PhantomData,
    }
}

/// From `enter_base_synthetic_owner`. It is `!Send`, so it drops on the
/// thread that made it.
pub struct BaseOwnerScope {
    _not_send: std::marker::PhantomData<*const ()>,
}

impl Drop for BaseOwnerScope {
    fn drop(&mut self) {
        BASE_SCOPES.with(|scopes| scopes.set(scopes.get() - 1));
    }
}

/// A copy of the synthetic nodes of one thread (see `synthetic_seed`). It
/// owns deep copies of the node data, so it can move to another thread.
pub struct SyntheticSeed {
    slots: Vec<Option<Vec<Slot>>>,
    aliases: FxHashMap<Node, u32>,
    /// The filled cells of each chunk of `SyntheticArena::datas`.
    datas: Vec<Option<Vec<crate::astdata::Node>>>,
    lists: Vec<Option<Vec<OwnList>>>,
    slices: Vec<Box<[Node]>>,
    slots_made: usize,
}

/// A copy of the synthetic nodes made on this thread so far whose owner is
/// not freed. Each entry keeps its index (a freed chunk stays a hole). A
/// checker worker starts from the nodes of the loading thread
/// (`install_synthetic_seed`), so the nodes that the parser and the binder
/// made keep their handles on every thread.
// PORT: Go factory nodes are shared pointers. Each checker thread owns a
// copy of the nodes made before the checkers started, and the nodes it
// makes itself.
#[must_use]
pub fn synthetic_seed() -> SyntheticSeed {
    ARENA.with(|a| {
        let a = a.borrow();
        SyntheticSeed {
            slots: a.slots.clone(),
            aliases: a.aliases.clone(),
            datas: a
                .datas
                .iter()
                .map(|chunk| {
                    chunk.as_ref().map(|chunk| {
                        chunk
                            .iter()
                            .map_while(|cell| cell.get().cloned())
                            .collect::<Vec<_>>()
                    })
                })
                .collect(),
            lists: a.lists.clone(),
            slices: a.slices.clone(),
            slots_made: a.slots_made,
        }
    })
}

/// The number of synthetic slots made on this thread, freed or not. Work
/// that must not make synthetic nodes compares it before and after.
#[must_use]
pub fn synthetic_slot_count() -> usize {
    ARENA.with(|a| a.borrow().slots_made)
}

/// The number of synthetic slots on this thread whose owner is not freed.
#[must_use]
pub fn synthetic_live_slot_count() -> usize {
    ARENA.with(|a| a.borrow().slots.iter().flatten().map(Vec::len).sum())
}

/// Makes `seed` the synthetic nodes of this thread. Every chunk of the seed
/// belongs to the thread, and new entries start new chunks.
pub fn install_synthetic_seed(seed: SyntheticSeed) {
    let arena = SyntheticArena {
        slot_owner: vec![OwnerKey::Base; seed.slots.len()],
        slots: seed.slots,
        aliases: seed.aliases,
        datas: seed
            .datas
            .into_iter()
            .map(|chunk| {
                chunk.map(|nodes| nodes.into_iter().map(OnceCell::from).collect::<DataChunk>())
            })
            .collect(),
        lists: seed.lists,
        slices: seed.slices,
        base: OwnerChunks::default(),
        owners: FxHashMap::default(),
        last: None,
        slots_made: seed.slots_made,
    };
    ARENA.with(|a| *a.borrow_mut() = arena);
}

/// Leaks the synthetic nodes of this thread instead of freeing them when the
/// thread ends. A checker worker of a one-program process calls it at the
/// end of the process, where freeing only costs time (like the checker, see
/// `program::create_checkers`).
pub fn forget_synthetic_nodes() {
    ARENA.with(|a| {
        std::mem::forget(std::mem::replace(
            &mut *a.borrow_mut(),
            SyntheticArena::new(),
        ));
    });
}

/// Frees the synthetic nodes of this thread. Their handles must not be read
/// again on this thread. A checker worker of a released program calls it
/// (`program::release_program`).
pub fn free_synthetic_nodes() {
    let nodes = ARENA.with(|a| std::mem::replace(&mut *a.borrow_mut(), SyntheticArena::new()));
    drop(nodes);
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
pub fn resolve_synthetic_id(id: crate::astdata::NodeId) -> Node {
    ARENA.with(|a| a.borrow().resolve(id.index()))
}

/// Reads the node slot of a synthetic handle.
fn with_node<R>(n: Node, f: impl FnOnce(&SyntheticNode) -> R) -> R {
    ARENA.with(|a| f(a.borrow().node(n)))
}

/// Writes the node slot of a synthetic handle. Panics on a parsed node.
fn with_node_mut<R>(n: Node, f: impl FnOnce(&mut SyntheticNode) -> R) -> R {
    assert!(
        is_synthetic_node(n),
        "cannot mutate a parsed node (kind {:?})",
        n.kind()
    );
    ARENA.with(|a| match a.borrow_mut().slot_mut(slot_index(n)) {
        Slot::Node(s) => f(s),
        _ => panic!("synthetic handle does not name a node slot"),
    })
}

// ──────────────────────────────────────────────────────────────────────
// Node data reads
// ──────────────────────────────────────────────────────────────────────

/// The astdata node of a synthetic node, held apart from the arena by its
/// chunk (see `SyntheticArena::datas`).
struct HeldNode {
    chunk: DataChunk,
    cell: usize,
}

impl std::ops::Deref for HeldNode {
    type Target = crate::astdata::Node;

    #[inline]
    fn deref(&self) -> &crate::astdata::Node {
        self.chunk[self.cell]
            .get()
            .expect("synthetic node data entry is not filled")
    }
}

/// The astdata node (kind and data) of synthetic node `n`, held apart from
/// the arena, so the reader can make and change synthetic nodes.
#[cold]
#[inline(never)]
fn synthetic_ast_node(n: Node) -> HeldNode {
    ARENA.with(|a| {
        let a = a.borrow();
        let i = a.node(n).data as usize;
        HeldNode {
            chunk: Rc::clone(a.datas[i / DATA_CHUNK].as_ref().expect(FREED)),
            cell: i % DATA_CHUNK,
        }
    })
}

/// The astdata node of a parsed (store) node, or `None` for a synthetic
/// node. Go dereferences the pointer, so nil panics.
// In a one-program process almost every read after the publish is a tier 0
// store node, so only that path is inlined into callers. The synthetic file
// index is never a store id, so checking the store tables first gives the
// same result as the order that `static_ast_node_slow` keeps (synthetic,
// store).
#[inline]
#[must_use]
pub fn static_ast_node(n: Node) -> Option<&'static crate::astdata::Node> {
    assert!(n.is_some(), "nil node dereference");
    match frozen_store_ast_node(n) {
        Some(node) => Some(node),
        None => static_ast_node_slow(n),
    }
}

/// `static_ast_node` for a node that is not a published store node: a
/// synthetic node (`None`) or an unpublished (built or detached) store node.
/// Panics for any other node. A freeable file version reads its node column
/// in its node shell, inline (`ast::store`, `node_shell`).
#[cold]
#[inline(never)]
fn static_ast_node_slow(n: Node) -> Option<&'static crate::astdata::Node> {
    if n.file_index() == SYNTHETIC_NODE_FILE {
        return None;
    }
    match try_store_ast_node(n) {
        Some(node) => Some(node),
        None => panic!("node {n:?} is not synthetic and has no store"),
    }
}

/// The astdata data of parsed node `n`, for code that reads parsed nodes
/// only: the binder, which loads the data of a node once and passes it to
/// the `_in` field reads (`data_accessor!`). Panics on a synthetic node.
#[inline]
#[must_use]
pub fn parsed_node_data(n: Node) -> &'static NodeData {
    match static_ast_node(n) {
        Some(node) => &node.data,
        None => panic!("synthetic node where a parsed node is read"),
    }
}

/// Calls `f` with the astdata node (kind and data) of any node, parsed or
/// synthetic. Go dereferences the pointer, so nil panics. `f` cannot keep a
/// reference into the node. For a synthetic node the arena is not borrowed
/// while `f` runs, so `f` can make and change synthetic nodes. Hot node
/// reads use the `with_data!` macro instead.
#[inline]
pub fn with_ast_node<R>(n: Node, f: impl FnOnce(&crate::astdata::Node) -> R) -> R {
    // One call of `f`, so a small `f` is inlined (see `with_data!`).
    let synthetic;
    let node = match static_ast_node(n) {
        Some(node) => node,
        None => {
            synthetic = synthetic_ast_node(n);
            &*synthetic
        }
    };
    f(node)
}

/// Calls `f` with the astdata data of any node, parsed or synthetic.
#[inline]
pub fn with_ast_data<R>(n: Node, f: impl FnOnce(&NodeData) -> R) -> R {
    with_ast_node(n, |node| f(&node.data))
}

/// `with_ast_node` for a synthetic node, out of line.
#[cold]
#[inline(never)]
pub fn with_synthetic_ast_node<R>(n: Node, f: impl FnOnce(&crate::astdata::Node) -> R) -> R {
    f(&synthetic_ast_node(n))
}

/// `$body` with `$d` bound to the astdata data (`&NodeData`) of node `$n`,
/// parsed or synthetic, like `with_ast_data`. Go dereferences the pointer, so
/// nil panics. `$body` cannot keep a reference into the data, and it cannot
/// `return` from the caller.
// PERF: the macro writes `$body` twice: inline for a parsed node (the
// `&'static` read, with no closure call) and in a closure that runs out of
// line for a synthetic node. That closure holds the node data apart from the
// arena, so `$body` can make synthetic nodes. A closure with two call sites
// is not inlined, which cost about 1% of instructions in multiprog. To write
// `$body` once instead, make this `with_ast_data($n, |$d| $body)`; no call
// site changes.
macro_rules! with_data {
    ($n:expr, |$d:ident| $body:expr) => {{
        let n__: $crate::core::Node = $n;
        match $crate::ast::synthetic::static_ast_node(n__) {
            Some(node__) => {
                let $d: &crate::astdata::NodeData = &node__.data;
                $body
            }
            None => $crate::ast::synthetic::with_synthetic_ast_node(n__, |node__| {
                let $d: &crate::astdata::NodeData = &node__.data;
                $body
            }),
        }
    }};
}
pub(crate) use with_data;

/// The `NodeList` that the selector `|$d| $body` (a `ListSel` body) finds in
/// the data of node `$n` (nil for a Go `nil` field), or `None` when the kind
/// of `$n` has no such field. Like `with_data!`, the selector runs inline for
/// a parsed node; a synthetic node gets it as a `ListSel`.
macro_rules! list_of {
    ($n:expr, |$d:ident| $body:expr) => {{
        let n__: $crate::core::Node = $n;
        match $crate::ast::synthetic::static_ast_node(n__) {
            Some(node__) => {
                let $d: &'static crate::astdata::NodeData = &node__.data;
                let found: Option<Option<$crate::ast::synthetic::AnyList<'static>>> = $body;
                found.map(|l| {
                    $crate::ast::NodeList::from_ts(
                        n__.file_index(),
                        l.map($crate::ast::synthetic::AnyList::nodes),
                    )
                })
            }
            None => $crate::ast::synthetic::synthetic_node_list_of(n__, |$d| $body),
        }
    }};
}
pub(crate) use list_of;

/// `list_of!` for a modifier list field.
macro_rules! modifiers_of {
    ($n:expr, |$d:ident| $body:expr) => {{
        let n__: $crate::core::Node = $n;
        match $crate::ast::synthetic::static_ast_node(n__) {
            Some(node__) => {
                let $d: &'static crate::astdata::NodeData = &node__.data;
                let found: Option<Option<$crate::ast::synthetic::AnyList<'static>>> = $body;
                found.map(|m| {
                    $crate::ast::ModifierList::from_ts(
                        n__.file_index(),
                        m.map($crate::ast::synthetic::AnyList::modifiers),
                    )
                })
            }
            None => $crate::ast::synthetic::synthetic_modifiers_of(n__, |$d| $body),
        }
    }};
}
pub(crate) use modifiers_of;

/// A list or modifier list read from node data.
#[derive(Clone, Copy)]
pub enum AnyList<'a> {
    Nodes(&'a crate::astdata::NodeList),
    Modifiers(&'a crate::astdata::ModifierList),
}

impl<'a> AnyList<'a> {
    /// The node list (for a modifier list, its `NodeList`).
    #[must_use]
    pub fn nodes(self) -> &'a crate::astdata::NodeList {
        match self {
            Self::Nodes(l) => l,
            Self::Modifiers(m) => &m.list,
        }
    }

    /// The modifier list. Panics on a node list.
    #[must_use]
    pub fn modifiers(self) -> &'a crate::astdata::ModifierList {
        match self {
            Self::Modifiers(m) => m,
            Self::Nodes(_) => panic!("a NodeList is not a ModifierList"),
        }
    }

    /// The address of the node list, for Go pointer equality.
    fn ptr(self) -> *const () {
        std::ptr::from_ref(self.nodes()).cast()
    }
}

/// Finds a list field in node data. `None`: the data has no such field (a
/// kind without it). `Some(None)`: the field is Go `nil`.
pub type ListSel = for<'a> fn(&'a NodeData) -> Option<Option<AnyList<'a>>>;

/// `list_of!` for a synthetic node: a `Field` handle.
#[cold]
#[inline(never)]
#[must_use]
pub fn synthetic_node_list_of(n: Node, sel: ListSel) -> Option<NodeList> {
    synthetic_list_of(n, sel).map(|l| match l {
        Some(l) => NodeList::synthetic(l),
        None => NodeList::NIL,
    })
}

/// `modifiers_of!` for a synthetic node: a `Field` handle.
#[cold]
#[inline(never)]
#[must_use]
pub fn synthetic_modifiers_of(n: Node, sel: ListSel) -> Option<ModifierList> {
    synthetic_list_of(n, sel).map(|m| match m {
        Some(m) => ModifierList::synthetic(m),
        None => ModifierList::NIL,
    })
}

/// Go `node.Text()` (and the `RawText` of template literals) of synthetic
/// node `n`: the text that `text` finds in its data, or "" for `None`. The
/// text is interned (`Name`), so it lives for the process, but each
/// distinct text is kept once.
// PORT: the text is in the node data, which the thread frees. `Node::text`
// returns `&'static str`, so a synthetic text is interned instead.
#[must_use]
pub fn synthetic_text(n: Node, text: impl FnOnce(&NodeData) -> Option<&str>) -> &'static str {
    with_synthetic_ast_node(n, |node| match text(&node.data) {
        Some(s) => Name::from(s).as_str(),
        None => "",
    })
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

/// Hook for `Node::bind` on a synthetic node. The data belongs to the
/// thread, so it is read by value.
#[must_use]
pub fn synthetic_bind(n: Node) -> NodeBindData {
    with_node(n, |s| s.bind.as_deref().copied().unwrap_or(EMPTY_BIND))
}

/// Go `node.AsSyntheticExpression().Type.(*Type)`.
#[must_use]
pub fn synthetic_expression_type(n: Node) -> TypeId {
    debug_assert!(n.kind() == SyntaxKind::SyntheticExpression);
    with_node(n, |s| s.synthetic_type)
}

// ──────────────────────────────────────────────────────────────────────
// Lists of synthetic data
// ──────────────────────────────────────────────────────────────────────

/// A list of synthetic data: the `NodeList`, `ModifierList` and `NodeSlice`
/// form of a list that this thread's arena owns. It is an index, so it is
/// only valid on the thread that made it (like a synthetic `Node`).
#[derive(Clone, Copy)]
pub enum SyntheticList {
    /// The list field that `sel` finds in node data `data`
    /// (`SyntheticNode::data`).
    Field { data: u32, sel: ListSel },
    /// A factory list.
    Own { index: u32 },
    /// A node slice that a read made (`NodeSlice` only).
    Slice { index: u32 },
}

impl std::fmt::Debug for SyntheticList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Field { data, .. } => write!(f, "Field({data})"),
            Self::Own { index } => write!(f, "Own({index})"),
            Self::Slice { index } => write!(f, "Slice({index})"),
        }
    }
}

/// The list field that `sel` finds in the data of synthetic node `n`. `None`
/// when the data has no such field; `Some(None)` when it is Go `nil`.
#[must_use]
pub fn synthetic_list_of(n: Node, sel: ListSel) -> Option<Option<SyntheticList>> {
    ARENA.with(|a| {
        let a = a.borrow();
        let data = a.node(n).data;
        sel(&a.data(data).data).map(|l| l.map(|_| SyntheticList::Field { data, sel }))
    })
}

/// Calls `f` with the list that `list` names. Panics on a node slice. The
/// arena stays borrowed while `f` runs, so `f` must not make or change
/// synthetic nodes.
pub fn with_synthetic_list<R>(list: SyntheticList, f: impl FnOnce(AnyList<'_>) -> R) -> R {
    ARENA.with(|a| f(a.borrow().list(list)))
}

/// The number of nodes in `list`.
#[must_use]
pub fn synthetic_list_len(list: SyntheticList) -> usize {
    ARENA.with(|a| {
        let a = a.borrow();
        match list {
            SyntheticList::Slice { index } => a.slices[index as usize].len(),
            _ => a.list(list).nodes().nodes.len(),
        }
    })
}

/// Node `i` of `list`. Panics when `i` is out of range, like Go.
#[must_use]
pub fn synthetic_list_node(list: SyntheticList, i: usize) -> Node {
    ARENA.with(|a| {
        let a = a.borrow();
        match list {
            SyntheticList::Slice { index } => a.slices[index as usize][i],
            _ => a.resolve(a.list(list).nodes().nodes[i].index()),
        }
    })
}

/// Go pointer equality of two lists.
#[must_use]
pub fn synthetic_list_eq(x: SyntheticList, y: SyntheticList) -> bool {
    match (x, y) {
        (SyntheticList::Own { index: i }, SyntheticList::Own { index: j })
        | (SyntheticList::Slice { index: i }, SyntheticList::Slice { index: j }) => i == j,
        (SyntheticList::Field { data: d, .. }, SyntheticList::Field { data: e, .. }) => {
            d == e
                && ARENA.with(|a| {
                    let a = a.borrow();
                    a.list(x).ptr() == a.list(y).ptr()
                })
        }
        _ => false,
    }
}

/// The address of the node list that `list` names, for Go pointer keys
/// (`NodeList::list_ptr`). It stays the same while the owner of the list
/// lives: node data and factory lists are in chunks that do not move.
#[must_use]
pub fn synthetic_list_ptr(list: SyntheticList) -> *const () {
    ARENA.with(|a| a.borrow().list(list).ptr())
}

/// A new node slice of this thread (Go allocates one on each call, for
/// example in `Node.Decorators()`). It belongs to the thread: `node.rs`
/// keeps one per node.
#[must_use]
pub fn new_synthetic_slice(nodes: Vec<Node>) -> SyntheticList {
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        a.slices.push(nodes.into_boxed_slice());
        SyntheticList::Slice {
            index: (a.slices.len() - 1) as u32,
        }
    })
}

/// A factory list with a copy of `list`, a list of synthetic node data that
/// a read has in place (the `Node::for_each_child_and_lists` hook). The
/// thread's arena owns the copy.
#[must_use]
pub fn copy_synthetic_list(list: &crate::astdata::NodeList) -> NodeList {
    NodeList::synthetic(push_own_list(OwnList::Nodes(list.clone())))
}

/// Parser `createMissingList` for synthetic `list` (see
/// `NodeList::with_missing_marker`): a new empty factory list at the `Loc`
/// of `list`, with the astdata `has_trailing_comma` bit set.
#[must_use]
pub fn synthetic_missing_list(list: SyntheticList) -> SyntheticList {
    let range = with_synthetic_list(list, |l| l.nodes().range);
    push_own_list(OwnList::Nodes(crate::astdata::NodeList {
        range,
        nodes: Vec::new(),
        has_trailing_comma: true,
    }))
}

fn push_own_list(list: OwnList) -> SyntheticList {
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        let owner = a.current_owner();
        SyntheticList::Own {
            index: a.push_list(owner, list),
        }
    })
}

// ──────────────────────────────────────────────────────────────────────
// Go field writes on factory nodes
// ──────────────────────────────────────────────────────────────────────

/// Go `node.Parent = parent`. Works on factory nodes and on nodes of a
/// ported-parser file that is not finished.
pub fn set_node_parent(n: Node, parent: Node) {
    if is_store_node(n) {
        return set_store_node_parent(n, parent);
    }
    with_node_mut(n, |s| s.parent = parent);
}

/// Go `node.Loc = loc`.
pub fn set_node_loc(n: Node, loc: TextRange) {
    if is_store_node(n) {
        return set_store_node_loc(n, loc);
    }
    with_node_mut(n, |s| s.loc = loc);
}

/// Go `node.Flags = flags`.
pub fn set_node_flags(n: Node, flags: NodeFlags) {
    if is_store_node(n) {
        return set_store_node_flags(n, flags);
    }
    with_node_mut(n, |s| s.flags = flags);
}

/// Gives synthetic node `n` a new astdata node that `f` makes from the
/// current one. The old one stays in the arena for the list handles taken
/// before (see `SyntheticNode::data`). The new one belongs to the owner of
/// `n`. `f` must not make or change synthetic nodes.
fn replace_synthetic_ast_node(
    n: Node,
    f: impl FnOnce(&crate::astdata::Node) -> crate::astdata::Node,
) {
    assert!(
        is_synthetic_node(n),
        "cannot mutate a parsed node (kind {:?})",
        n.kind()
    );
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        let index = slot_index(n);
        let node = f(a.data(a.node(n).data));
        let owner = a.slot_owner[index / SLOT_CHUNK];
        let data = a.push_data(owner, node);
        let Slot::Node(s) = a.slot_mut(index) else {
            panic!("synthetic handle does not name a node slot");
        };
        s.data = data;
    });
}

/// A Go write to a data field of a node (`node.AsX().Field = v`): `data` is
/// the node's data with that field changed. Works on factory nodes and on
/// nodes of a ported-parser file that is not finished.
// PORT: astdata data is shared, so the node gets a new astdata node with the
// same kind. Writes are rare.
pub fn replace_node_data(n: Node, data: NodeData) {
    if is_store_node(n) {
        return replace_store_node_data(n, data);
    }
    replace_synthetic_ast_node(n, |old| {
        let kind = old.kind;
        debug_assert!(
            data.matches_syntax_kind(kind),
            "{kind:?} does not fit its NodeData"
        );
        new_ts_node(kind, data)
    });
}

/// Go `node.Kind = kind` on a factory node. The new kind must fit the node
/// data (Go only does this between kinds with one data struct, such as
/// `KindJSImportDeclaration` to `KindImportDeclaration`).
// PORT: the kind lives in the astdata node, so the node gets a new astdata
// node with the same data.
pub fn set_node_kind(n: Node, kind: SyntaxKind) {
    replace_synthetic_ast_node(n, |old| {
        let data = old.data.clone();
        assert!(
            data.matches_syntax_kind(kind),
            "{kind:?} does not fit the data of {:?}",
            old.kind
        );
        new_ts_node(kind, data)
    });
}

/// A astdata node for synthetic data. Only kind and data are read; the
/// header lives in the slot.
fn new_ts_node(kind: SyntaxKind, data: NodeData) -> crate::astdata::Node {
    crate::astdata::Node {
        kind,
        flags: crate::astdata::NodeFlags(0),
        range: undefined_ts_range(),
        parent: None,
        data,
    }
}

/// Go `node.AsMutable().SetModifiers(modifiers)`.
// Go: ast/ast.go:227 (n *MutableNode) SetModifiers
// PORT: Go dispatches to `setModifiers` on the data. The kinds with a
// `modifiers` field set it (ModifiersBase, NamedMemberBase,
// BinaryExpression); other kinds do nothing, like Go `NodeDefault`.
pub fn set_node_modifiers(n: Node, modifiers: ModifierList) {
    let mods = synthetic_modifiers_value(modifiers);
    let mut data = with_ast_data(n, Clone::clone);
    match &mut data {
        NodeData::ArrowFunction(d) => d.modifiers = mods,
        NodeData::BinaryExpression(d) => d.modifiers = mods,
        NodeData::ClassDeclaration(d) => d.modifiers = mods,
        NodeData::ClassExpression(d) => d.modifiers = mods,
        NodeData::ClassStaticBlockDeclaration(d) => d.modifiers = mods,
        NodeData::ConstructorDeclaration(d) => d.modifiers = mods,
        NodeData::ConstructorTypeNode(d) => d.modifiers = mods,
        NodeData::EnumDeclaration(d) => d.modifiers = mods,
        NodeData::EnumMember(d) => d.modifiers = mods,
        NodeData::ExportAssignment(d) => d.modifiers = mods,
        NodeData::ExportDeclaration(d) => d.modifiers = mods,
        NodeData::FunctionDeclaration(d) => d.modifiers = mods,
        NodeData::FunctionExpression(d) => d.modifiers = mods,
        NodeData::FunctionTypeNode(d) => d.modifiers = mods,
        NodeData::GetAccessorDeclaration(d) => d.modifiers = mods,
        NodeData::ImportDeclaration(d) => d.modifiers = mods,
        NodeData::ImportEqualsDeclaration(d) => d.modifiers = mods,
        NodeData::IndexSignatureDeclaration(d) => d.modifiers = mods,
        NodeData::InterfaceDeclaration(d) => d.modifiers = mods,
        NodeData::MethodDeclaration(d) => d.modifiers = mods,
        NodeData::MethodSignatureDeclaration(d) => d.modifiers = mods,
        NodeData::MissingDeclaration(d) => d.modifiers = mods,
        NodeData::ModuleDeclaration(d) => d.modifiers = mods,
        NodeData::NamespaceExportDeclaration(d) => d.modifiers = mods,
        NodeData::ParameterDeclaration(d) => d.modifiers = mods,
        NodeData::PropertyAssignment(d) => d.modifiers = mods,
        NodeData::PropertyDeclaration(d) => d.modifiers = mods,
        NodeData::PropertySignatureDeclaration(d) => d.modifiers = mods,
        NodeData::SetAccessorDeclaration(d) => d.modifiers = mods,
        NodeData::ShorthandPropertyAssignment(d) => d.modifiers = mods,
        NodeData::TypeAliasDeclaration(d) => d.modifiers = mods,
        NodeData::TypeParameterDeclaration(d) => d.modifiers = mods,
        NodeData::VariableStatement(d) => d.modifiers = mods,
        _ => return,
    }
    replace_node_data(n, data);
}

/// Changes the binder data of a factory node: Go
/// `node.FlowNodeData().FlowNode = f`, `node.AsX().Symbol = s`, ...
pub fn update_node_bind(n: Node, f: impl FnOnce(&mut NodeBindData)) {
    with_node_mut(n, |s| f(s.bind.get_or_insert_with(|| Box::new(EMPTY_BIND))));
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
/// `Loc = UndefinedTextRange()`, nil parent, no flags and no binder data. It
/// belongs to the current owner (see "Owners" in the module comment).
pub fn alloc_synthetic_node(kind: SyntaxKind, data: NodeData) -> Node {
    debug_assert!(
        data.matches_syntax_kind(kind),
        "{kind:?} does not fit its NodeData"
    );
    let node = new_ts_node(kind, data);
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        let owner = a.current_owner();
        let data = a.push_data(owner, node);
        handle(a.push_slot(
            owner,
            Slot::Node(SyntheticNode {
                data,
                parent: Node::NIL,
                flags: NodeFlags::NONE,
                loc: TextRange::undefined(),
                bind: None,
                synthetic_type: TypeId::NIL,
                source_file: None,
            }),
        ))
    })
}

/// Sets the Go `SyntheticExpression.Type` of a new node.
pub(crate) fn set_synthetic_expression_type(n: Node, t: TypeId) {
    with_node_mut(n, |s| s.synthetic_type = t);
}

// ──────────────────────────────────────────────────────────────────────
// Factory SourceFile fields
// ──────────────────────────────────────────────────────────────────────

/// Attaches the Go `ast.SourceFile` fields to a new factory SourceFile.
pub(crate) fn set_synthetic_source_file_data(n: Node, data: SyntheticSourceFileData) {
    debug_assert!(n.kind() == SyntaxKind::SourceFile);
    with_node_mut(n, |s| s.source_file = Some(Box::new(data)));
}

/// True when `n` is a SourceFile that the factory made.
#[must_use]
pub fn is_synthetic_source_file(n: Node) -> bool {
    is_synthetic_node(n) && with_node(n, |s| s.source_file.is_some())
}

/// Reads the Go `ast.SourceFile` fields of a factory SourceFile.
pub fn with_synthetic_source_file<R>(n: Node, f: impl FnOnce(&SyntheticSourceFileData) -> R) -> R {
    with_node(n, |s| {
        f(s.source_file
            .as_deref()
            .expect("node is not a factory SourceFile"))
    })
}

/// Go writes to the fields of a factory SourceFile
/// (`file.AsSourceFile().IsDeclarationFile = true`, ...). Panics on a
/// parsed SourceFile (see the module comment).
pub fn update_synthetic_source_file<R>(
    n: Node,
    f: impl FnOnce(&mut SyntheticSourceFileData) -> R,
) -> R {
    with_node_mut(n, |s| {
        f(s.source_file
            .as_deref_mut()
            .expect("node is not a factory SourceFile"))
    })
}

/// Go `file.Text()` of a factory SourceFile.
#[must_use]
pub fn synthetic_source_file_text(n: Node) -> &'static str {
    with_synthetic_source_file(n, |d| d.text)
}

/// Go `file.FileName()` of a factory SourceFile.
#[must_use]
pub fn synthetic_source_file_file_name(n: Node) -> &'static str {
    with_synthetic_source_file(n, |d| d.file_name)
}

/// Go `file.AsSourceFile().ReferencedFiles`, `TypeReferenceDirectives` and
/// `LibReferenceDirectives`, `IsDeclarationFile` of any SourceFile, parsed
/// or factory-made.
// PORT: `SourceFileInfo` is `&'static` for parsed files only, so readers that
// must also see a factory SourceFile use this copy.
#[must_use]
pub fn source_file_parser_fields(file: Node) -> SyntheticSourceFileData {
    if is_synthetic_node(file) {
        return with_synthetic_source_file(file, Clone::clone);
    }
    let info = source_file_info(file);
    SyntheticSourceFileData {
        file_name: source_file_file_name(file),
        path: info.path.clone(),
        text: source_file_text(file),
        language_variant: info.language_variant,
        script_kind: info.script_kind,
        is_declaration_file: info.is_declaration_file,
        uses_uri_style_node_core_modules: info.uses_uri_style_node_core_modules,
        imports: info.imports.clone(),
        module_augmentations: info.module_augmentations.clone(),
        ambient_module_names: info.ambient_module_names.clone(),
        comment_directives: info.comment_directives.clone(),
        pragmas: info.pragmas.clone(),
        referenced_files: info.referenced_files.clone(),
        type_reference_directives: info.type_reference_directives.clone(),
        lib_reference_directives: info.lib_reference_directives.clone(),
        common_js_module_indicator: info.common_js_module_indicator,
        external_module_indicator: info.external_module_indicator,
    }
}

// Go: ast/ast.go:2663 (node *SourceFile) copyFrom
/// Copies the parser fields of `other` (parsed or factory-made) to the
/// factory SourceFile `node`.
pub fn source_file_copy_from(node: Node, other: Node) {
    // Do not copy fields set by NewSourceFile (Text, FileName, Path, or Statements)
    let o = source_file_parser_fields(other);
    update_synthetic_source_file(node, |d| {
        d.language_variant = o.language_variant;
        d.script_kind = o.script_kind;
        d.is_declaration_file = o.is_declaration_file;
        d.uses_uri_style_node_core_modules = o.uses_uri_style_node_core_modules;
        d.imports = o.imports;
        d.module_augmentations = o.module_augmentations;
        d.ambient_module_names = o.ambient_module_names;
        d.comment_directives = o.comment_directives;
        d.pragmas = o.pragmas;
        d.referenced_files = o.referenced_files;
        d.type_reference_directives = o.type_reference_directives;
        d.lib_reference_directives = o.lib_reference_directives;
        d.common_js_module_indicator = o.common_js_module_indicator;
        d.external_module_indicator = o.external_module_indicator;
    });
    set_node_flags(node, node.flags() | other.flags());
}

/// The synthetic-space id that stands for `n` inside synthetic `NodeData`.
/// Nil maps to the nil slot. A parsed node gets (or reuses) an alias slot,
/// which belongs to the thread.
#[must_use]
pub fn synthetic_child_id(n: Node) -> crate::astdata::NodeId {
    if n.is_nil() {
        return crate::astdata::NodeId::new(NIL_SLOT);
    }
    if n.file_index() == SYNTHETIC_NODE_FILE {
        return crate::astdata::NodeId::new(slot_index(n) as u32);
    }
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        if let Some(&index) = a.aliases.get(&n) {
            return crate::astdata::NodeId::new(index);
        }
        let index = a.push_slot(OwnerKey::Base, Slot::Alias(n));
        a.aliases.insert(n, index);
        crate::astdata::NodeId::new(index)
    })
}

/// Like `synthetic_child_id`, for astdata fields that are `Option<NodeId>`.
#[must_use]
pub fn synthetic_opt_child_id(n: Node) -> Option<crate::astdata::NodeId> {
    if n.is_nil() {
        None
    } else {
        Some(synthetic_child_id(n))
    }
}

/// Go `core.UndefinedTextRange()` in astdata form. `TextPos` is `u32`; the
/// `as i32` in `node.rs` `text_range_of` turns `u32::MAX` back into `-1`.
fn undefined_ts_range() -> crate::astdata::text::TextRange {
    ts_range(TextRange::undefined())
}

/// A Go `core.TextRange` in astdata form (`-1` is stored as `u32::MAX`).
fn ts_range(loc: TextRange) -> crate::astdata::text::TextRange {
    crate::astdata::text::TextRange {
        start: crate::astdata::text::TextPos::new(loc.pos() as u32),
        end: crate::astdata::text::TextPos::new(loc.end() as u32),
    }
}

/// The astdata list for a synthetic node's list field.
fn ts_list(nodes: &[Node], loc: TextRange, has_trailing_comma: bool) -> crate::astdata::NodeList {
    crate::astdata::NodeList {
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
    let list = ts_list(nodes, loc, false);
    NodeList::synthetic(push_own_list(OwnList::Nodes(list)))
}

/// Go `f.NewModifierList(nodes)` with a given `Loc`. `modifier_flags()` in
/// node.rs recomputes `ModifiersToFlags(nodes)`, as the Go factory does.
#[must_use]
pub fn new_synthetic_modifier_list(nodes: &[Node], loc: TextRange) -> ModifierList {
    let list = crate::astdata::ModifierList {
        list: ts_list(nodes, loc, false),
        flags: crate::astdata::ModifierFlags(modifiers_to_flags(nodes).0 as u32),
    };
    ModifierList::synthetic(push_own_list(OwnList::Modifiers(list)))
}

/// A list value to store inside new synthetic `NodeData`. Go stores the
/// `*NodeList` pointer; a list that already is synthetic is copied as is, and
/// a parsed list is rebuilt over alias ids with its own `Loc`.
// PORT: astdata stores lists by value, so a synthetic node that takes a
// parsed (or another synthetic) list gets a copy. `NodeList` equality on the
// copy is false where Go compares equal pointers.
#[must_use]
pub fn synthetic_list_value(list: NodeList) -> Option<crate::astdata::NodeList> {
    if list.is_nil() {
        return None;
    }
    if let Some(l) = list.synthetic_list() {
        return Some(with_synthetic_list(l, |l| l.nodes().clone()));
    }
    let nodes = list.nodes().to_vec();
    Some(ts_list(&nodes, list.loc(), list.stored_trailing_comma()))
}

/// Like `synthetic_list_value` for a list field that astdata requires. Go
/// `nil` becomes an empty list with an undefined `Loc`.
// PORT: Go keeps `nil`; `NodeList::is_nil` on that field is false here.
#[must_use]
pub fn synthetic_req_list_value(list: NodeList) -> crate::astdata::NodeList {
    synthetic_list_value(list).unwrap_or_else(|| ts_list(&[], TextRange::undefined(), false))
}

/// A modifier list value to store inside new synthetic `NodeData`.
#[must_use]
pub fn synthetic_modifiers_value(modifiers: ModifierList) -> Option<crate::astdata::ModifierList> {
    if modifiers.is_nil() {
        return None;
    }
    if let Some(m) = modifiers.synthetic_list() {
        return Some(with_synthetic_list(m, |m| m.modifiers().clone()));
    }
    let nodes = modifiers.nodes().to_vec();
    Some(crate::astdata::ModifierList {
        list: ts_list(
            &nodes,
            modifiers.loc(),
            modifiers.node_list().stored_trailing_comma(),
        ),
        flags: crate::astdata::ModifierFlags(modifiers_to_flags(&nodes).0 as u32),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // The test runs on its own thread, so `free_synthetic_nodes` frees only
    // the nodes it made.
    #[test]
    fn synthetic_lists_keep_go_pointer_identity_until_freed() {
        std::thread::spawn(|| {
            let f = NodeFactory::new();
            let a = f.new_identifier("a");
            let statements = f.new_node_list(&[a]);
            let block = f.new_block(statements, false);

            // Reads of one list field give one list. The node data holds a
            // copy of the factory list (`synthetic_list_value`).
            let read = block.statement_list();
            assert_eq!(read, block.statement_list());
            assert_eq!(read.list_ptr(), block.statement_list().list_ptr());
            assert_ne!(read, statements);
            assert_eq!(read.nodes().to_vec(), vec![a]);
            assert_eq!(a.text(), "a");

            // A data write gives the field a new list. The old handle still
            // reads the old list, like a Go pointer.
            replace_node_data(block, with_ast_data(block, Clone::clone));
            assert_ne!(block.statement_list(), read);
            assert_eq!(read.nodes().get(0), a);

            assert!(synthetic_slot_count() > 1);
            free_synthetic_nodes();
            assert_eq!(synthetic_slot_count(), 1);
        })
        .join()
        .expect("test thread panicked");
    }

    // Node data and factory lists fill chunks. A new chunk does not move an
    // earlier entry, and a read that holds a node can make more nodes.
    #[test]
    fn synthetic_entries_stay_in_place_across_chunks() {
        std::thread::spawn(|| {
            let f = NodeFactory::new();
            let first = f.new_identifier("first");
            let list = f.new_node_list(&[first]);
            let ptr = list.list_ptr();
            let last = with_ast_data(first, |_| {
                let mut last = NodeList::NIL;
                for i in 0..2 * DATA_CHUNK.max(LIST_CHUNK) {
                    last = f.new_node_list(&[f.new_identifier(format!("n{i}"))]);
                }
                last
            });
            assert_eq!(list.list_ptr(), ptr);
            assert_eq!(list.nodes().to_vec(), vec![first]);
            assert_eq!(first.text(), "first");
            let last_text = format!("n{}", 2 * DATA_CHUNK.max(LIST_CHUNK) - 1);
            assert_eq!(last.nodes().get(0).text(), last_text);

            // The seed copy keeps every index.
            let seed = synthetic_seed();
            std::thread::spawn(move || {
                install_synthetic_seed(seed);
                assert_eq!(list.nodes().to_vec(), vec![first]);
                assert_eq!(first.text(), "first");
                assert_eq!(last.nodes().get(0).text(), last_text);
            })
            .join()
            .expect("seed thread panicked");
            free_synthetic_nodes();
        })
        .join()
        .expect("test thread panicked");
    }

    /// The message of a caught panic.
    fn panic_message(payload: &(dyn std::any::Any + Send)) -> Option<&str> {
        payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
    }

    // A program version that is an owner owns the entries made while it is
    // current, and keeps their identity while it lives. Its free drops them
    // and keeps the base entries. A freed handle panics, and a new node gets
    // a new index.
    #[test]
    fn program_owner_frees_its_entries() {
        std::thread::spawn(|| {
            let program: &'static GoProgram = Box::leak(Box::new(GoProgram {
                id: next_program_id(),
                source_file_order: Vec::new(),
                options: CompilerOptions::default(),
                bound_symbols: std::sync::OnceLock::new(),
                state: std::sync::OnceLock::new(),
            }));
            let f = NodeFactory::new();
            let base = f.new_identifier("base");
            let base_slots = synthetic_live_slot_count();

            open_synthetic_owner(program.id);
            let (statement, list, block) = {
                let _program = enter_program(Some(program));
                let statement = f.new_expression_statement(base);
                let list = f.new_node_list(&[statement]);
                let block = f.new_block(list, false);
                assert_eq!(block.statement_list(), block.statement_list());
                assert_eq!(block.statement_list().nodes().to_vec(), vec![statement]);
                assert_eq!(list.nodes().to_vec(), vec![statement]);
                // A data write goes to the owner of the node: the base.
                replace_node_data(base, with_ast_data(base, Clone::clone));
                assert!(synthetic_live_slot_count() > base_slots);
                (statement, list, block)
            };
            free_synthetic_owner(program.id);

            assert_eq!(synthetic_live_slot_count(), base_slots);
            assert_eq!(base.text(), "base");
            let freed = std::panic::catch_unwind(|| block.kind())
                .expect_err("a node of a freed owner is read");
            assert_eq!(panic_message(&*freed), Some(FREED));
            let freed =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| list.nodes().to_vec()))
                    .expect_err("a list of a freed owner is read");
            assert_eq!(panic_message(&*freed), Some(FREED));
            let fresh = f.new_identifier("fresh");
            assert!(fresh != statement && fresh != block);
            assert_eq!(fresh.text(), "fresh");

            // A seed keeps the base indexes and the holes.
            let seed = synthetic_seed();
            std::thread::spawn(move || {
                install_synthetic_seed(seed);
                assert_eq!(base.text(), "base");
                assert_eq!(fresh.text(), "fresh");
                assert!(std::panic::catch_unwind(|| block.kind()).is_err());
            })
            .join()
            .expect("seed thread panicked");
            free_synthetic_nodes();
        })
        .join()
        .expect("test thread panicked");
    }
}
