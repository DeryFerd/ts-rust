//! Per-file Go node stores (the nodes the ported Go parser creates) and the
//! file registry (the published stores and the `GoFile` of each file id).
//!
//! Go parser nodes are ordinary `*ast.Node` values made by `ast.NodeFactory`.
//! Here each parsed file gets one store. The store id is the file id, so a
//! store node is a normal `Node` handle: high 32 bits are the file id, low 32
//! bits are the slot index + 1.
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
//! Phases of a store:
//! - Build: the parser runs on one thread and writes the stores of that
//!   thread (`BUILD`). The header and the data can change until the parser
//!   finishes the file (`finishNode`, parent setting, JSDoc flags,
//!   reparser.go writes). Then the parser freezes the file, which also
//!   builds the per-store tables that a publish puts in the registry. The
//!   build stores of a thread get consecutive ids from `BuildStores::base`,
//!   the published count when its first store was made. The last store
//!   made on a thread is its `ACTIVE` store: the parser reads and writes it
//!   without a store lookup.
//! - Detached: a parse worker (`files_parser.rs` prefetch) parses one file
//!   into a store with a provisional id (`DETACHED_STORE_BASE` + job) that
//!   only its thread sees (`DETACHED`). The loading thread adopts the
//!   finished store when the loader asks for that file
//!   (`adopt_detached_store`). The store then gets the next real id, so ids
//!   still follow the serial parse order.
//! - Published: the loader calls `publish_file_stores` with the `GoFile` of
//!   each build store before it installs the program. The stores and their
//!   `GoFile`s move into the process-wide, read-only registry. Node reads
//!   then need no thread-local and no `RefCell` borrow, and any thread can
//!   read them. Writes to a published store panic. A table that needs the
//!   real id of an adopted store is built then, on scoped threads for a
//!   large publish (`publish_stores`).
//!
//! The registry:
//! - One file id is one file version. Ids only grow (`PUBLISHED` is the
//!   next unused id), and a published file is never changed or freed. A new
//!   program version shares the ids of its unchanged files.
//! - Tier 0 (`FROZEN`) is the first publish: program 1, or the files of the
//!   legacy loader. The hot node reads in `node.rs` read only its dense
//!   tables, inline, and return `None` on a miss.
//! - Tier 1 (`LATER`) holds every later publish (edited files, other
//!   programs). One slot per id points at the `Frozen` of its publish. Reads
//!   reach it out of line, after a tier 0 miss.
//! - After a tier 0 miss, a synthetic id has no store (two compares, no
//!   call). Any other id takes one cold call: tier 1, then the detached
//!   store, then the build stores of this thread.
//!
//! Binder data is not stored here: it stays in `GoFile::node_bind`, indexed
//! by slot index.
//!
//! PORT: a program is either all legacy files or all store files. A legacy
//! publish has only `GoFile`s. It must be the only publish: file ids are
//! store ids, so no store can be made or published after it.

use crate::frontend::parser::SourceFileParseOptions;
use crate::prelude::*;
use std::cell::Cell;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};
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
    /// Set by `mark_source_file_roots`: Go `GetSourceFileOfNode(node)` is the
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
/// The default value is an empty placeholder with no slots.
#[derive(Default)]
struct FileStore {
    file_name: &'static str,
    text: &'static str,
    headers: Vec<NodeHeader>,
    /// The ts_ast node (kind and data) of each node slot. `None` for the nil
    /// slot and alias slots.
    nodes: Vec<Option<&'static ts_ast::Node>>,
    /// Alias slot of each foreign node, so one node gets one slot. Emptied
    /// by `publish_file_stores`.
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
    /// until the file is published (its `GoFile` holds it then), so
    /// `publish_file_stores` empties it.
    jsdoc_cache: FxHashMap<Node, &'static [Node]>,
    /// Go `file.hasLazyJSDoc`, set by `finishSourceFile` for a non-JS file,
    /// with the inputs that Go `parseJSDocForNode` reads from the file
    /// (`ParseOptions()` and `ScriptKind`; the text is `text`). Node reads
    /// use it until the file is published (the program then keeps the
    /// inputs), so `publish_file_stores` drops it.
    lazy_js_doc: Option<(SourceFileParseOptions, ScriptKind)>,
    /// Go `file.jsdocCache` entries that `resolveJSDoc` adds before the file
    /// is published.
    // PORT: the parsed JSDoc nodes are synthetic nodes of the thread that
    // parsed them, so they are kept apart from `jsdoc_cache`.
    // `adopt_detached_store` (another thread) and `publish_file_stores`
    // drop them.
    lazy_jsdoc_cache: FxHashMap<Node, &'static [Node]>,
    /// Go `file.LanguageVariant`, the parse `file.Diagnostics()` and
    /// `file.ContainsNonASCII`, set by `finishSourceFile`. Reads of a file
    /// that is not published use them (`ast::source_file_language_variant`,
    /// `ast::source_file_diagnostics`, `ast::source_file_get_position_map`),
    /// for example the format tests, which parse a file with no program.
    language_variant: LanguageVariant,
    diagnostics: &'static [Diagnostic],
    contains_non_ascii: bool,
    /// The SourceFile node of this store, set by `publish_file_stores`.
    root: Node,
    /// Go `SourceFile.ECMALineMap()`, computed on first use after publish
    /// and shared by every thread.
    ecma_line_starts: OnceLock<Box<[i32]>>,
    /// `headers[i].kind` for every slot (`Frozen::kinds`). Made when the
    /// file is frozen. A length other than `headers.len()` means "not made".
    kinds: Box<[SyntaxKind]>,
    /// `resolve_slot` for every slot (`Frozen::resolved`), with the file id
    /// of the store. Same length rule as `kinds`.
    resolved: Box<[Node]>,
}

/// A store that is not published yet. It lives in a leaked cell of the
/// thread that made it, so `ACTIVE` can keep a plain reference to it.
type StoreCell = &'static RefCell<FileStore>;

/// The build stores of one thread. `stores[i]` has file id `base + i`.
#[derive(Default)]
struct BuildStores {
    /// `PUBLISHED` when the first of `stores` was made.
    base: usize,
    stores: Vec<StoreCell>,
}

impl BuildStores {
    /// The file id of the next store of this thread. Only a publish changes
    /// `PUBLISHED`, so the ids of one build are consecutive.
    fn next_id(&mut self) -> usize {
        let published = PUBLISHED.load(Ordering::Acquire);
        if self.stores.is_empty() {
            self.base = published;
        } else {
            assert_eq!(
                self.base, published,
                "another thread published node stores while this thread built stores"
            );
        }
        let id = self.base + self.stores.len();
        assert!(id < TIER1_LIMIT, "too many file ids");
        id
    }
}

thread_local! {
    /// The stores of this thread, while the parser runs.
    static BUILD: RefCell<BuildStores> = const {
        RefCell::new(BuildStores {
            base: 0,
            stores: Vec::new(),
        })
    };
    /// The detached store of a parse worker and its provisional id.
    static DETACHED: Cell<Option<(usize, StoreCell)>> = const { Cell::new(None) };
    /// The emptied cell of the last detached store of this thread. The next
    /// detached store reuses it.
    static SPARE_CELL: Cell<Option<StoreCell>> = const { Cell::new(None) };
    /// The store this thread made or adopted last, and its id: during a
    /// parse, the store of the file the parser reads and writes. It is also
    /// in `BUILD` or `DETACHED`, so clearing it is always safe.
    // PERF: query Q8. Node reads have no parser or factory to ask, so the
    // store of the parsed file is found here. The type has no destructor,
    // so a read is one thread-local load and an id compare: no `FROZEN`
    // check, no detached check and no `RefCell` borrow of `BUILD`.
    // `publish_file_stores` and `take_detached_file_store` clear it before
    // they empty its cell, and a thread publishes only its own build
    // stores, so an active store is never published. (One loading thread
    // builds at a time: `BuildStores::next_id` and the publish check it.)
    static ACTIVE: Cell<Option<(usize, StoreCell)>> = const { Cell::new(None) };
}

/// The cell of store `file` when it is the active store of this thread.
#[inline]
fn active_store(file: usize) -> Option<StoreCell> {
    match ACTIVE.get() {
        Some((id, store)) if id == file => Some(store),
        _ => None,
    }
}

/// The unpublished store `file` of this thread (active, detached or
/// built), or `None` when this thread has no such store.
#[inline]
fn build_store(file: usize) -> Option<StoreCell> {
    match active_store(file) {
        Some(store) => Some(store),
        None => inactive_build_store(file),
    }
}

/// `build_store` without the `ACTIVE` check.
#[inline(never)]
fn inactive_build_store(file: usize) -> Option<StoreCell> {
    if is_detached_id(file) {
        return DETACHED
            .get()
            .and_then(|(id, store)| (id == file).then_some(store));
    }
    BUILD.with(|b| {
        let b = b.borrow();
        b.stores.get(file.wrapping_sub(b.base)).copied()
    })
}

/// File index that marks a parent in the same store inside a stored
/// header. Reads give the handle of the store (`NodeHeader::read`), so a
/// store keeps its headers when its id changes (`adopt_detached_store`).
const LOCAL_STORE: usize = 0x7fff_ffff;

/// First provisional store id. Real file ids stay below `TIER1_LIMIT`;
/// synthetic node and flow ids are above every provisional id.
pub const DETACHED_STORE_BASE: usize = 0x8000_0000;
/// Number of provisional ids.
pub const DETACHED_STORE_LIMIT: usize = 0x4000_0000;

/// Every real file id is below this. Tier 1 has one slot per id.
const TIER1_LIMIT: usize = 1 << 22;
/// Slots per tier 1 chunk.
const LATER_CHUNK: usize = 256;

#[inline]
fn is_detached_id(file: usize) -> bool {
    (DETACHED_STORE_BASE..DETACHED_STORE_BASE + DETACHED_STORE_LIMIT).contains(&file)
}

/// True for an id that never has a store: a synthetic node or flow id, or
/// any other id at or above `TIER1_LIMIT` that is not a provisional id.
#[inline]
fn is_storeless_id(file: usize) -> bool {
    file >= TIER1_LIMIT && !is_detached_id(file)
}

/// The stores and `GoFile`s of one publish, read-only, with dense
/// per-store header and node tables for the hot node reads. File `file` of
/// the publish is at index `file - base`. Tier 0 has `base` 0, so its hot
/// reads index the tables by file id.
struct Frozen {
    /// The first file id of the publish.
    base: usize,
    stores: &'static [FileStore],
    headers: Box<[&'static [NodeHeader]]>,
    nodes: Box<[&'static [Option<&'static ts_ast::Node>]]>,
    /// `headers[file][i].kind`, packed (`FileStore::kinds`). `Node::kind`
    /// reads only this.
    kinds: Box<[&'static [SyntaxKind]]>,
    /// `try_resolve_store_id(file, i)` for every slot, computed once
    /// (`FileStore::resolved`). `Node::new` reads only this.
    resolved: Box<[&'static [Node]]>,
    /// The `GoFile` of each file id of the publish.
    go_files: Box<[GoFile]>,
    /// True for the legacy loader: `go_files` only, no stores.
    legacy: bool,
}

/// Tier 0: the first publish.
static FROZEN: OnceLock<Frozen> = OnceLock::new();

/// The tier 1 slots of `LATER_CHUNK` consecutive file ids.
type LaterChunk = [OnceLock<&'static Frozen>; LATER_CHUNK];

/// Tier 1: the publish of each file id after the first publish. Each later
/// publish is leaked once, and the slot of each of its ids names it.
static LATER: [OnceLock<Box<LaterChunk>>; TIER1_LIMIT / LATER_CHUNK] =
    [const { OnceLock::new() }; TIER1_LIMIT / LATER_CHUNK];

/// The next unused file id. Only `publish_file_stores` changes it.
static PUBLISHED: AtomicUsize = AtomicUsize::new(0);

/// The tier 1 publish of file `file` and the index of `file` in it.
#[cold]
#[inline(never)]
fn later(file: usize) -> Option<(&'static Frozen, usize)> {
    let chunk = LATER.get(file / LATER_CHUNK)?.get()?;
    let frozen: &'static Frozen = *chunk[file % LATER_CHUNK].get()?;
    Some((frozen, file - frozen.base))
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

/// Runs `f` on an unpublished store of this thread: its active, detached
/// or build store. `None` when this thread has no store `file`.
#[inline]
fn with_thread_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> Option<R> {
    build_store(file).map(|store| f(&store.borrow()))
}

/// A store read after a tier 0 miss: a synthetic id (or any id when tier 0
/// is legacy) has no store; any other id takes one cold call.
#[inline]
fn after_tier0_miss<R>(tier0: &Frozen, file: usize, f: impl FnOnce(&FileStore) -> R) -> Option<R> {
    if is_storeless_id(file) || tier0.legacy {
        return None;
    }
    with_later_store(file, f)
}

/// The cold part of `after_tier0_miss`: tier 1, then the detached store,
/// then the build stores of this thread.
#[cold]
#[inline(never)]
fn with_later_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> Option<R> {
    match later(file) {
        Some((frozen, local)) => Some(f(&frozen.stores[local])),
        None => with_thread_store(file, f),
    }
}

/// A published tier 1 store, for readers that need it `'static`. `None`
/// after a tier 0 miss when `file` is not published in tier 1.
#[inline]
fn later_store(tier0: &Frozen, file: usize) -> Option<&'static FileStore> {
    if file >= TIER1_LIMIT || tier0.legacy {
        return None;
    }
    later(file).map(|(frozen, local)| &frozen.stores[local])
}

/// Runs `f` on store `file`: published, or an unpublished store of this
/// thread. `None` when this thread cannot see a store `file`.
#[inline]
fn try_with_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> Option<R> {
    match FROZEN.get() {
        Some(tier0) => match tier0.stores.get(file) {
            Some(store) => Some(f(store)),
            None => after_tier0_miss(tier0, file, f),
        },
        None => with_thread_store(file, f),
    }
}

fn with_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> R {
    try_with_store(file, f)
        .unwrap_or_else(|| panic!("file {file:#x} has no node store on this thread"))
}

/// Runs `f` on unpublished store `file` of this thread. Panics when `file`
/// is published or this thread has no store `file`.
fn with_store_mut<R>(file: usize, f: impl FnOnce(&mut FileStore) -> R) -> R {
    // PERF: query Q8. The parse writes the active store, which is never
    // published (see `ACTIVE`), so it needs no publish check.
    let store = match active_store(file) {
        Some(store) => store,
        None => inactive_unpublished_store(file),
    };
    f(&mut store.borrow_mut())
}

/// The store that `with_store_mut` writes when it is not the active store.
#[inline(never)]
fn inactive_unpublished_store(file: usize) -> StoreCell {
    assert!(
        !is_published(file),
        "cannot change the node store of published file {file:#x}"
    );
    inactive_build_store(file)
        .unwrap_or_else(|| panic!("file {file:#x} has no node store on this thread"))
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

/// Makes the store of the next parsed file and returns its file id. Ids
/// follow parse order (see `BuildStores`). The store becomes the active
/// store of this thread.
pub fn new_file_store(file_name: &'static str, text: &'static str) -> usize {
    assert_no_legacy_publish();
    let store: StoreCell = leak_in_ast_arena(RefCell::new(FileStore::new(file_name, text)));
    let id = BUILD.with(|b| {
        let mut b = b.borrow_mut();
        let id = b.next_id();
        b.stores.push(store);
        id
    });
    ACTIVE.set(Some((id, store)));
    id
}

/// Panics when tier 0 is a legacy publish: its file ids would collide with
/// store ids.
fn assert_no_legacy_publish() {
    assert!(
        FROZEN.get().is_none_or(|tier0| !tier0.legacy),
        "a legacy program is published; file ids would collide with store ids"
    );
}

impl FileStore {
    fn new(file_name: &'static str, text: &'static str) -> Self {
        Self {
            file_name,
            text,
            headers: vec![NodeHeader::target(Node::NIL)],
            nodes: vec![None],
            ..Self::default()
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
    assert!(job < DETACHED_STORE_LIMIT, "too many detached stores");
    let id = DETACHED_STORE_BASE + job;
    assert!(
        DETACHED.get().is_none(),
        "this thread already has a detached store"
    );
    let store = SPARE_CELL
        .take()
        .unwrap_or_else(|| leak_in_ast_arena(RefCell::default()));
    *store.borrow_mut() = FileStore::new(file_name, text);
    DETACHED.set(Some((id, store)));
    ACTIVE.set(Some((id, store)));
    id
}

/// Removes the detached store of this thread, if any.
pub fn take_detached_file_store() -> Option<DetachedStore> {
    let (id, cell) = DETACHED.take()?;
    if active_store(id).is_some() {
        ACTIVE.set(None);
    }
    let store = cell.take();
    SPARE_CELL.set(Some(cell));
    Some(DetachedStore { id, store })
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
/// handle map for the values the parse returned with it. The store becomes
/// the active store of this thread.
pub fn adopt_detached_store(detached: DetachedStore) -> StoreRemap {
    assert_no_legacy_publish();
    assert!(
        detached.is_self_contained(),
        "cannot adopt a store that names other stores"
    );
    let DetachedStore { id, mut store } = detached;
    let (remap, cell) = BUILD.with(|b| {
        let mut b = b.borrow_mut();
        let remap = StoreRemap {
            from: id,
            to: b.next_id(),
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
        // The lazy JSDoc nodes are synthetic nodes of the parse worker.
        store.lazy_jsdoc_cache = FxHashMap::default();
        // The resolved table holds handles of the store id, which changes
        // here. `publish_file_stores` makes it for the real id.
        store.resolved = Box::default();
        let cell: StoreCell = leak_in_ast_arena(RefCell::new(store));
        b.stores.push(cell);
        (remap, cell)
    });
    ACTIVE.set(Some((remap.to, cell)));
    remap
}

// ──────────────────────────────────────────────────────────────────────
// File registry
// ──────────────────────────────────────────────────────────────────────

/// The `GoFile` of published file `file`. Panics when it is not published.
#[inline]
#[must_use]
pub fn go_file(file: usize) -> &'static GoFile {
    if let Some(tier0) = FROZEN.get()
        && let Some(go_file) = tier0.go_files.get(file)
    {
        return go_file;
    }
    go_file_slow(file)
}

#[cold]
#[inline(never)]
fn go_file_slow(file: usize) -> &'static GoFile {
    try_go_file(file).unwrap_or_else(|| panic!("file {file} is not published"))
}

/// `go_file`, or `None` for a store still being built, a synthetic id or
/// an unknown id.
#[inline]
#[must_use]
pub fn try_go_file(file: usize) -> Option<&'static GoFile> {
    let tier0 = FROZEN.get()?;
    if let Some(go_file) = tier0.go_files.get(file) {
        return Some(go_file);
    }
    if file >= TIER1_LIMIT || tier0.legacy {
        return None;
    }
    later(file).map(|(frozen, local)| &frozen.go_files[local])
}

/// True when `file` has a `GoFile` in the registry (tier 0 or tier 1).
#[inline]
#[must_use]
pub fn is_published(file: usize) -> bool {
    try_go_file(file).is_some()
}

/// Ids of the stores that this thread built and did not publish, in id
/// order. The next publish of this thread gives them their `GoFile`s.
#[must_use]
pub fn unpublished_file_ids() -> std::ops::Range<usize> {
    BUILD.with(|b| {
        let b = b.borrow();
        if b.stores.is_empty() {
            let next = PUBLISHED.load(Ordering::Acquire);
            return next..next;
        }
        b.base..b.base + b.stores.len()
    })
}

/// True when file `file` was parsed by the ported parser.
#[inline]
#[must_use]
pub fn has_file_store(file: usize) -> bool {
    match FROZEN.get() {
        Some(tier0) => {
            file < tier0.headers.len()
                || (!tier0.legacy
                    && !is_storeless_id(file)
                    && with_later_store(file, |_| ()).is_some())
        }
        None => build_store(file).is_some(),
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

/// Go `result.LanguageVariant`, `result.diagnostics` and
/// `result.ContainsNonASCII` in `finishSourceFile`.
// PORT: the diagnostics are leaked so reads can return a `&'static` slice,
// like `GoFile::info.diagnostics` after the publish. A parse without errors
// leaks nothing.
pub fn set_file_store_parse_fields(
    file: usize,
    language_variant: LanguageVariant,
    diagnostics: &[Diagnostic],
    contains_non_ascii: bool,
) {
    let diagnostics: &'static [Diagnostic] = Box::leak(diagnostics.to_vec().into_boxed_slice());
    with_store_mut(file, |s| {
        s.language_variant = language_variant;
        s.diagnostics = diagnostics;
        s.contains_non_ascii = contains_non_ascii;
    });
}

/// Go `file.LanguageVariant` of a store file.
#[must_use]
pub fn file_store_language_variant(file: usize) -> LanguageVariant {
    with_store(file, |s| s.language_variant)
}

/// Go `file.Diagnostics()` (the parse diagnostics) of a store file.
#[must_use]
pub fn file_store_diagnostics(file: usize) -> &'static [Diagnostic] {
    with_store(file, |s| s.diagnostics)
}

/// Go `file.ContainsNonASCII` of a store file: true when the scanner
/// decoded a non-ASCII rune. False for a store that `finishSourceFile` did
/// not finish.
#[must_use]
pub fn file_store_contains_non_ascii(file: usize) -> bool {
    with_store(file, |s| s.contains_non_ascii)
}

/// Go `file.jsdocCache[node]` of a store file whose program is not
/// installed yet. It never parses (Go `EagerJSDoc`).
#[must_use]
pub fn file_store_js_doc(file: usize, node: Node) -> Option<&'static [Node]> {
    with_store(file, |s| {
        s.jsdoc_cache
            .get(&node)
            .or_else(|| s.lazy_jsdoc_cache.get(&node))
            .copied()
    })
}

/// Go `result.SetHasLazyJSDoc(true)` in `finishSourceFile`. The store keeps
/// the parse options and script kind of the file for
/// `resolve_file_store_js_doc`.
pub fn set_file_store_lazy_js_doc(
    file: usize,
    parse_options: &SourceFileParseOptions,
    script_kind: ScriptKind,
) {
    let lazy = Some((parse_options.clone(), script_kind));
    with_store_mut(file, |s| s.lazy_js_doc = lazy);
}

// Go: ast/ast.go:2614 (*SourceFile).resolveJSDoc
/// Go `node.JSDoc(file)` of a store file whose program is not installed
/// yet: the cache, then, in a lazy file (`set_file_store_lazy_js_doc`), Go
/// `parseJSDocForNode`, whose result the cache keeps. None on a cache miss
/// in a file that is not lazy.
// PORT: Go takes `jsdocMu`. A store that is not published has one thread.
// The lists are leaked so reads can return `&'static` slices.
#[must_use]
pub fn resolve_file_store_js_doc(file: usize, node: Node) -> Option<&'static [Node]> {
    if let Some(jsdocs) = file_store_js_doc(file, node) {
        return Some(jsdocs);
    }
    let (parse_options, script_kind, text) = with_store(file, |s| {
        s.lazy_js_doc
            .clone()
            .map(|(parse_options, script_kind)| (parse_options, script_kind, s.text))
    })?;
    let jsdocs: &'static [Node] = Box::leak(
        crate::frontend::parser::parse_js_doc_for_node(&parse_options, text, script_kind, node)
            .into_boxed_slice(),
    );
    with_store_mut(file, |s| s.lazy_jsdoc_cache.insert(node, jsdocs));
    Some(jsdocs)
}

/// True when node reads of store file `file` must use the store, because
/// the file is not published yet (the parser is still running).
#[must_use]
pub fn is_file_store_before_program(file: usize) -> bool {
    !is_published(file) && has_file_store(file)
}

/// Ends the parse of a file. Header and data writes panic after this.
/// Headers cannot change after this, so it also marks the source file roots
/// (`mark_source_file_roots`) and builds the tables that the publish puts
/// in the registry (`FileStore::kinds`, `FileStore::resolved`) on the
/// parsing thread.
pub fn freeze_file_store(file: usize) {
    with_store_mut(file, |s| s.freeze(file));
}

impl FileStore {
    /// `freeze_file_store` for this store, which has id `file`.
    fn freeze(&mut self, file: usize) {
        self.end_parse();
        // One pass over the headers for the parser flags and the kinds.
        let mut flags = Vec::with_capacity(self.headers.len());
        let mut kinds = Vec::with_capacity(self.headers.len());
        for h in &self.headers {
            flags.push(h.flags);
            kinds.push(h.kind);
        }
        self.parser_flags = Some(flags);
        self.kinds = kinds.into_boxed_slice();
        // PERF: query Q7. The table is made here, on the parse thread, not
        // in `publish_file_stores` on the loader. A detached store gets its
        // real id only when the loader adopts it, so its table waits for
        // `publish_file_stores`.
        if !is_detached_id(file) {
            self.resolved = self.resolved_table(file);
        }
    }

    /// Marks the store finished and marks its source file roots.
    fn end_parse(&mut self) {
        self.frozen = true;
        self.headers.shrink_to_fit();
        self.nodes.shrink_to_fit();
        mark_source_file_roots(self);
    }

    /// `resolve_slot(file, i, ..)` for every slot, for store id `file`.
    fn resolved_table(&self, file: usize) -> Box<[Node]> {
        (0..self.headers.len())
            .map(|i| resolve_slot(file, i, &self.nodes, &self.headers))
            .collect()
    }

    /// The part of `publish_file_stores` for this store, which has id
    /// `file`: drops what only the parse and the loader used, and makes a
    /// table that `freeze_file_store` did not make or that no longer fits
    /// the slots.
    fn publish(&mut self, file: usize) {
        if !self.frozen {
            // PORT: a store whose parse did not finish (a parse panic).
            self.end_parse();
        }
        self.aliases = FxHashMap::default();
        self.jsdoc_cache = FxHashMap::default();
        self.lazy_js_doc = None;
        self.lazy_jsdoc_cache = FxHashMap::default();
        self.parser_flags = None;
        if self.root_slot != NIL_SLOT {
            self.root = handle(file, self.root_slot);
        }
        if self.kinds.len() != self.headers.len() {
            self.kinds = self.headers.iter().map(|h| h.kind).collect();
        }
        if self.resolved.len() != self.headers.len() {
            self.resolved = self.resolved_table(file);
        }
    }

    /// About how much work `publish` does, in slots: a fixed part for the
    /// maps it drops and one per slot of each table it still makes.
    fn publish_work(&self) -> usize {
        let slots = self.headers.len();
        let mut work = PUBLISH_WORK_PER_STORE;
        if self.kinds.len() != slots {
            work += slots;
        }
        if self.resolved.len() != slots {
            work += slots;
        }
        work
    }
}

/// `FileStore::publish_work` of one store without tables to make: about
/// the cost of its map drops, in slots.
const PUBLISH_WORK_PER_STORE: usize = 32;
/// `publish_stores` uses scoped threads from this much work on. Below it
/// the thread starts cost more than they save.
const PARALLEL_PUBLISH_WORK: usize = 1 << 17;
/// Threads for `publish_stores`, the calling thread included.
const PUBLISH_THREADS: usize = 4;

/// `FileStore::publish` for every store; store `i` has id `base + i`.
// PERF: effect R2-13. The stores are independent, so a large program is
// split into `PUBLISH_THREADS` runs of about equal work, one per scoped
// thread. The result does not depend on the split.
fn publish_stores(stores: &mut [FileStore], base: usize) {
    let total: usize = stores.iter().map(FileStore::publish_work).sum();
    if total < PARALLEL_PUBLISH_WORK {
        publish_run(stores, base);
        return;
    }
    let share = total.div_ceil(PUBLISH_THREADS);
    std::thread::scope(|scope| {
        let mut rest = stores;
        let mut first = base;
        for _ in 1..PUBLISH_THREADS {
            if rest.is_empty() {
                break;
            }
            let mut end = 0;
            let mut work = 0;
            while end < rest.len() && work < share {
                work += rest[end].publish_work();
                end += 1;
            }
            let (run, tail) = std::mem::take(&mut rest).split_at_mut(end);
            scope.spawn(move || publish_run(run, first));
            first += end;
            rest = tail;
        }
        publish_run(rest, first);
    });
}

/// `FileStore::publish` for `stores`, whose first store has id `first`.
fn publish_run(stores: &mut [FileStore], first: usize) {
    for (i, store) in stores.iter_mut().enumerate() {
        store.publish(first + i);
    }
}

/// True when the parse of store file `file` is over: the file is published
/// or `freeze_file_store` ran.
#[must_use]
pub fn is_file_store_frozen(file: usize) -> bool {
    is_published(file) || with_store(file, |s| s.frozen)
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
    if is_published(file) {
        return with_store(file, computed);
    }
    with_store_mut(file, |s| {
        s.parser_flags.take().unwrap_or_else(|| computed(s))
    })
}

/// Publishes the build stores of this thread: `go_files[i]` is the
/// `GoFile` of id `unpublished_file_ids().start + i`. The legacy loader has
/// no stores and passes its files. The loader calls this once per program,
/// before `core::set_prog`. The stores are then read-only, and any thread
/// can read them. The first publish is tier 0; later ones go to tier 1. An
/// empty later publish does nothing.
// PORT: Go needs no publish; its nodes are heap objects. The publish also
// computes `NodeHeader::source_file_is_root` for `get_source_file_of_node`.
pub fn publish_file_stores(go_files: Vec<GoFile>) {
    // The cells stay leaked and empty. Nothing reads them after this.
    ACTIVE.set(None);
    let BuildStores {
        base,
        stores: cells,
    } = BUILD.with(|b| std::mem::take(&mut *b.borrow_mut()));
    let base = if cells.is_empty() {
        PUBLISHED.load(Ordering::Acquire)
    } else {
        base
    };
    let legacy = cells.is_empty() && !go_files.is_empty();
    assert!(
        legacy || go_files.len() == cells.len(),
        "a publish needs one GoFile per store ({} stores, {} GoFiles)",
        cells.len(),
        go_files.len()
    );
    let tier0 = FROZEN.get();
    if let Some(tier0) = tier0 {
        assert!(
            !tier0.legacy && !legacy,
            "a legacy program must be the only publish; file ids would collide with store ids"
        );
        if go_files.is_empty() {
            return;
        }
    }
    let count = cells.len().max(go_files.len());
    assert!(base + count <= TIER1_LIMIT, "too many file ids");
    if let Err(published) =
        PUBLISHED.compare_exchange(base, base + count, Ordering::AcqRel, Ordering::Acquire)
    {
        panic!(
            "another thread published file ids while this thread built ids {base}.. (now {published})"
        );
    }
    let mut stores: Vec<FileStore> = cells.iter().map(|cell| cell.take()).collect();
    publish_stores(&mut stores, base);
    let stores: &'static [FileStore] = Box::leak(stores.into_boxed_slice());
    // PERF: query Q7. The per-store tables are made already, so this only
    // collects slices.
    let frozen = Frozen {
        base,
        stores,
        headers: stores.iter().map(|s| &s.headers[..]).collect(),
        nodes: stores.iter().map(|s| &s.nodes[..]).collect(),
        kinds: stores.iter().map(|s| &s.kinds[..]).collect(),
        resolved: stores.iter().map(|s| &s.resolved[..]).collect(),
        go_files: go_files.into_boxed_slice(),
        legacy,
    };
    if tier0.is_none() {
        assert_eq!(base, 0, "the first publish must start at file id 0");
        assert!(
            FROZEN.set(frozen).is_ok(),
            "another thread made the first publish"
        );
        return;
    }
    let frozen: &'static Frozen = Box::leak(Box::new(frozen));
    for file in base..base + count {
        let chunk = LATER[file / LATER_CHUNK]
            .get_or_init(|| Box::new([const { OnceLock::new() }; LATER_CHUNK]));
        assert!(
            chunk[file % LATER_CHUNK].set(frozen).is_ok(),
            "file {file} is already published"
        );
    }
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
    if let Some(f) = FROZEN.get()
        && file < f.nodes.len()
    {
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
    if let Some(f) = FROZEN.get()
        && n.file_index() < f.nodes.len()
    {
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
    if let Some(f) = FROZEN.get()
        && n.file_index() < f.headers.len()
    {
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
/// loc): one thread-local load for the active store, one table lookup in
/// tier 0, one more thread-local access before the first publish. `None`
/// for nil, synthetic and legacy nodes. With it a node read needs no
/// separate `has_file_store` call.
// PERF: query Q8. The active store is checked first and inline; every
// other case is out of line.
#[inline]
#[must_use]
pub fn try_store_header(n: Node) -> Option<NodeHeader> {
    if n.is_nil() {
        return None;
    }
    match active_store_header(n) {
        Some(header) => Some(header),
        None => try_store_header_slow(n.file_index(), slot_index(n)),
    }
}

/// `try_store_header` for a node that is not in the active store.
#[inline(never)]
fn try_store_header_slow(file: usize, index: usize) -> Option<NodeHeader> {
    let read = |s: &FileStore| s.headers[index].read(file);
    match FROZEN.get() {
        Some(f) => match f.headers.get(file) {
            Some(headers) => Some(headers[index].read(file)),
            None => after_tier0_miss(f, file, read),
        },
        None => inactive_build_store(file).map(|store| read(&store.borrow())),
    }
}

/// The header of `n` when `n` is a node of the active store of this thread
/// (see `ACTIVE`): the parse fast path of the node reads. That store is not
/// published. `None` for any other node.
#[inline]
#[must_use]
pub fn active_store_header(n: Node) -> Option<NodeHeader> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    let store = active_store(file)?;
    Some(store.borrow().headers[slot_index(n)].read(file))
}

/// Go `node.Kind` of a tier 0 store node. `None` for any other node: nil,
/// synthetic, legacy, tier 1 and unpublished store nodes.
#[inline]
#[must_use]
pub fn frozen_store_kind(n: Node) -> Option<SyntaxKind> {
    if n.is_nil() {
        return None;
    }
    let kinds = FROZEN.get()?.kinds.get(n.file_index())?;
    Some(kinds[slot_index(n)])
}

/// The header of a tier 0 store node, by reference, so a read of one field
/// does not copy the whole header. The parent is still in its stored
/// form (see `LOCAL_STORE`). `None` as for `frozen_store_kind`.
#[inline]
fn frozen_header(n: Node) -> Option<&'static NodeHeader> {
    if n.is_nil() {
        return None;
    }
    let headers = FROZEN.get()?.headers.get(n.file_index())?;
    Some(&headers[slot_index(n)])
}

/// Parser `node.Flags` of a tier 0 store node (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_flags(n: Node) -> Option<NodeFlags> {
    frozen_header(n).map(|h| h.flags)
}

/// Go `node.Loc` of a tier 0 store node (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_loc(n: Node) -> Option<TextRange> {
    frozen_header(n).map(|h| h.loc)
}

/// Go `node.Parent` of a tier 0 store node (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_parent(n: Node) -> Option<Node> {
    frozen_header(n).map(|h| h.read(n.file_index()).parent)
}

/// The ts_ast node of a tier 0 store node: the inlined fast path of
/// `ast_node_of`. `None` as for `frozen_store_kind`. Panics like
/// `try_store_ast_node` on a nil or alias slot.
#[inline]
#[must_use]
pub fn frozen_store_ast_node(n: Node) -> Option<&'static ts_ast::Node> {
    if n.is_nil() {
        return None;
    }
    let nodes = FROZEN.get()?.nodes.get(n.file_index())?;
    Some(nodes[slot_index(n)].expect("store handle does not name a node slot"))
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
    // PERF: query Q8, see `ACTIVE`.
    if let Some(store) = active_store(file) {
        return Some(slot_node(store.borrow().nodes[index]));
    }
    try_store_ast_node_slow(file, index)
}

/// `try_store_ast_node` for a node that is not in the active store.
#[inline(never)]
fn try_store_ast_node_slow(file: usize, index: usize) -> Option<&'static ts_ast::Node> {
    let read = |s: &FileStore| slot_node(s.nodes[index]);
    match FROZEN.get() {
        Some(f) => match f.nodes.get(file) {
            Some(nodes) => Some(slot_node(nodes[index])),
            None => after_tier0_miss(f, file, read),
        },
        None => inactive_build_store(file).map(|store| read(&store.borrow())),
    }
}

/// The ts_ast node of a node slot. Panics on the nil slot and alias slots.
#[inline]
fn slot_node(slot: Option<&'static ts_ast::Node>) -> &'static ts_ast::Node {
    slot.expect("store handle does not name a node slot")
}

/// `resolve_store_id(file, id)` when `file` has a store, in one lookup (see
/// `try_store_header`). `None` when it has none.
#[inline]
#[must_use]
pub fn try_resolve_store_id(file: usize, id: ts_ast::NodeId) -> Option<Node> {
    let index = id.index();
    // PERF: query Q8, see `ACTIVE`.
    if let Some(store) = active_store(file) {
        let s = store.borrow();
        return Some(resolve_slot(file, index, &s.nodes, &s.headers));
    }
    try_resolve_store_id_slow(file, index)
}

/// `try_resolve_store_id` for a file that is not the active store.
#[inline(never)]
fn try_resolve_store_id_slow(file: usize, index: usize) -> Option<Node> {
    let resolve = |s: &FileStore| resolve_slot(file, index, &s.nodes, &s.headers);
    match FROZEN.get() {
        Some(f) => match f.resolved.get(file) {
            Some(resolved) => Some(resolved[index]),
            None => after_tier0_miss(f, file, resolve),
        },
        None => inactive_build_store(file).map(|store| resolve(&store.borrow())),
    }
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

/// `try_resolve_store_id(file, _)` for every slot of tier 0 store `file`,
/// indexed by `NodeId::index()`. `None` for any other file.
#[inline]
#[must_use]
pub fn frozen_resolved(file: usize) -> Option<&'static [Node]> {
    FROZEN.get()?.resolved.get(file).copied()
}

/// Go `SourceFile.ECMALineMap()` of published store file `file`. It is
/// computed once and shared by every thread. `None` for an unpublished
/// store or a file without a store.
#[must_use]
pub fn frozen_file_ecma_line_starts(file: usize) -> Option<&'static [i32]> {
    let tier0 = FROZEN.get()?;
    let store = match tier0.stores.get(file) {
        Some(store) => store,
        None => later_store(tier0, file)?,
    };
    Some(store.ecma_line_starts.get_or_init(|| {
        crate::scanner_util::compute_ecma_line_starts(store.text).into_boxed_slice()
    }))
}

/// Go `GetSourceFileOfNode(n)` in O(1), when `n` is a published store node
/// whose parent walk ends at its store root. `None` means "walk".
#[inline]
#[must_use]
pub fn frozen_source_file_of_node(n: Node) -> Option<Node> {
    if n.is_nil() {
        return None;
    }
    let f = FROZEN.get()?;
    let file = n.file_index();
    let Some(headers) = f.headers.get(file) else {
        let store = later_store(f, file)?;
        return store.headers[slot_index(n)]
            .source_file_is_root
            .then_some(store.root);
    };
    headers[slot_index(n)]
        .source_file_is_root
        .then(|| f.stores[file].root)
}

// ──────────────────────────────────────────────────────────────────────
// Go field writes during the parse
// ──────────────────────────────────────────────────────────────────────

/// Runs `f` on the header of `n` when `n` is a node slot of an unpublished
/// store of this thread (built or detached), with one thread-local access.
/// False when `n` is not such a node (for example a synthetic or a
/// published node). Panics on a finished store, like `with_slot_mut`.
fn try_with_build_header(n: Node, f: impl FnOnce(&mut NodeHeader)) -> bool {
    if n.is_nil() {
        return false;
    }
    let file = n.file_index();
    // A tier 0 node or a synthetic node leaves here, inline: one load and
    // two compares, as the one-program `FROZEN` check. The active store is
    // never in tier 0 (its id is at least the published count).
    if let Some(tier0) = FROZEN.get()
        && (file < tier0.headers.len() || is_storeless_id(file) || tier0.legacy)
    {
        return false;
    }
    // PERF: query Q8. The parse writes the active store, which is never
    // published (see `ACTIVE`).
    let store = match active_store(file) {
        Some(store) => store,
        None => match inactive_thread_store(file) {
            Some(store) => store,
            None => return false,
        },
    };
    let mut s = store.borrow_mut();
    assert!(!s.frozen, "cannot mutate a node of a finished file");
    let index = slot_index(n);
    assert!(
        s.nodes[index].is_some(),
        "store handle does not name a node slot"
    );
    f(&mut s.headers[index]);
    true
}

/// `try_with_build_header` for a file that is not in tier 0 and not the
/// active store: `None` for a tier 1 file (published), else the detached
/// store, then the build stores of this thread.
#[inline(never)]
fn inactive_thread_store(file: usize) -> Option<StoreCell> {
    if FROZEN.get().is_some() && later(file).is_some() {
        return None;
    }
    inactive_build_store(file)
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

thread_local! {
    /// The size of the first chunk of this thread's AST arena
    /// (`set_ast_arena_start`).
    static AST_ARENA_START: Cell<usize> = const { Cell::new(1 << 20) };
    /// Set when this thread made its AST arena.
    static AST_ARENA_MADE: Cell<bool> = const { Cell::new(false) };
    /// AST nodes and lists live for the whole process. One leaked bump
    /// arena per thread holds them, so each node costs a pointer bump, not
    /// a malloc. The arena never drops, like the `Box::leak` it replaces.
    static AST_ARENA: &'static bumpalo::Bump = {
        AST_ARENA_MADE.set(true);
        Box::leak(Box::new(bumpalo::Bump::with_capacity(AST_ARENA_START.get())))
    };
}

/// Moves `value` into this thread's leaked AST arena.
pub(crate) fn leak_in_ast_arena<T>(value: T) -> &'static T {
    AST_ARENA.with(|arena| &*arena.alloc(value))
}

/// Sets the size of the first chunk of this thread's AST arena (1 MiB by
/// default). Later chunks double in size. Call it before the thread makes
/// its first node. A released program leaks the arenas of its checker
/// workers, and the part of a chunk that no node uses leaks with them, so
/// the workers of a later program version size the chunk from what the
/// workers of a released one used (`program.rs` `worker_arena_start`).
pub(crate) fn set_ast_arena_start(bytes: usize) {
    AST_ARENA_START.set(bytes);
}

/// The bytes that the nodes of this thread's AST arena use, or 0 when the
/// thread made no arena (asking does not make one).
pub(crate) fn ast_arena_used() -> usize {
    if !AST_ARENA_MADE.get() {
        return 0;
    }
    AST_ARENA.with(|arena| arena.allocated_bytes() - arena.chunk_capacity())
}

/// A leaked ts_ast node. Only kind and data are read for store and
/// synthetic nodes; the header lives in the slot.
fn leak_ast_node(kind: SyntaxKind, data: NodeData) -> &'static ts_ast::Node {
    leak_in_ast_arena(ts_ast::Node {
        kind,
        flags: ts_ast::NodeFlags(0),
        range: ts_range(TextRange::undefined()),
        parent: None,
        data,
    })
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
    let list: &'static ts_ast::NodeList = leak_in_ast_arena(ts_list(file, nodes, loc));
    NodeList {
        file: file as u32,
        list: Some(list),
    }
}

/// Go `f.NewModifierList(nodes)` followed by `list.Loc = loc`, in store
/// `file`. `ModifierFlags = ModifiersToFlags(nodes)` as in Go.
#[must_use]
pub fn new_store_modifier_list(file: usize, nodes: &[Node], loc: TextRange) -> ModifierList {
    let list: &'static ts_ast::ModifierList = leak_in_ast_arena(ts_ast::ModifierList {
        list: ts_list(file, nodes, loc),
        flags: ts_ast::ModifierFlags(modifiers_to_flags(nodes).0 as u32),
    });
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
