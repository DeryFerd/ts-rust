//! Shared handles and stores for the Go port. Read `PORTING.md` first.
//!
//! Every Go pointer to a shared object becomes a `Copy` handle. Handle value
//! zero is Go `nil`, so Go `x == nil` ports to `x.is_nil()`.

use indexmap::IndexMap;
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::sync::Arc;

/// `IndexMap` with the Fx hasher. Keys are small ids or short names, so Fx
/// is faster than SipHash. Iteration order is still insertion order.
pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
/// `IndexSet` with the Fx hasher.
pub type FxIndexSet<K> = indexmap::IndexSet<K, FxBuildHasher>;

use crate::flags::{CheckFlags, FlowFlags, NodeFlags, SymbolFlags};

macro_rules! handle {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Debug)]
        pub struct $name(pub u32);

        impl $name {
            /// Go `nil`.
            pub const NIL: Self = Self(0);

            #[must_use]
            pub const fn is_nil(self) -> bool {
                self.0 == 0
            }

            #[must_use]
            pub const fn is_some(self) -> bool {
                self.0 != 0
            }

            /// Arena index. Arenas keep a dummy entry at index 0.
            #[must_use]
            pub const fn index(self) -> usize {
                self.0 as usize
            }

            /// Returns `None` for nil.
            #[must_use]
            pub const fn get(self) -> Option<Self> {
                if self.0 == 0 { None } else { Some(self) }
            }
        }
    };
}

handle!(
    /// Go `*Type`. Index into `Checker::types`.
    TypeId
);
handle!(
    /// Go `*ast.Symbol`. Index into `SymbolArena::symbols`.
    SymbolId
);
handle!(
    /// Go `*Signature`. Index into `Checker::signatures`.
    SignatureId
);
handle!(
    /// Go `*IndexInfo`. Index into `Checker::index_infos`.
    IndexInfoId
);
handle!(
    /// Go `*TypePredicate`. Index into `Checker::type_predicates`.
    TypePredicateId
);
handle!(
    /// Go `*TypeMapper`. Index into `Checker::mappers`.
    MapperId
);
handle!(
    /// Go `*InferenceContext`. Index into `Checker::inference_contexts`.
    InferenceContextId
);
handle!(
    /// Go `ast.SymbolTable` (a Go map, so it has reference semantics).
    /// Index into `SymbolArena::tables`. Nil is a nil map: reads see it as empty.
    SymbolTable
);

/// Go `*ast.FlowNode`. High 32 bits: file index. Low 32 bits: index + 1 into
/// that file's `GoFile::flow_nodes`. Zero is nil. Read with `flow.get_flow()`
/// (defined in `crate::ast`).
#[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Debug)]
pub struct FlowNodeId(pub u64);

impl FlowNodeId {
    pub const NIL: Self = Self(0);

    #[must_use]
    pub const fn is_nil(self) -> bool {
        self.0 == 0
    }

    #[must_use]
    pub const fn is_some(self) -> bool {
        self.0 != 0
    }

    #[must_use]
    pub const fn new(file: usize, index: usize) -> Self {
        Self(((file as u64) << 32) | (index as u64 + 1))
    }

    #[must_use]
    pub const fn file_index(self) -> usize {
        (self.0 >> 32) as usize
    }

    #[must_use]
    pub const fn local_index(self) -> usize {
        ((self.0 & 0xffff_ffff) - 1) as usize
    }
}

/// Go `*ast.Node` (and every alias: `*ast.Expression`, `*ast.TypeNode`,
/// `*ast.SourceFile`, ...). High 32 bits: file index in `GoProgram::files`.
/// For a ported-parser file this is also its store id (`ast/store.rs`).
/// Low 32 bits: `ts_ast::NodeId::index() + 1`. Zero is nil.
/// Node methods (kind, parent, fields, binder data) live in `crate::ast`.
#[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Debug)]
pub struct Node(pub u64);

impl Node {
    pub const NIL: Self = Self(0);

    #[must_use]
    pub const fn is_nil(self) -> bool {
        self.0 == 0
    }

    #[must_use]
    pub const fn is_some(self) -> bool {
        self.0 != 0
    }

    #[must_use]
    pub const fn get(self) -> Option<Self> {
        if self.0 == 0 { None } else { Some(self) }
    }

    #[must_use]
    pub fn new(file: usize, node: ts_ast::NodeId) -> Self {
        // Child ids inside factory-made nodes live in the synthetic id space.
        if file == crate::ast::SYNTHETIC_NODE_FILE {
            return crate::ast::resolve_synthetic_id(node);
        }
        // Child ids inside nodes of a ported-parser file are store slots.
        if let Some(n) = crate::ast::try_resolve_store_id(file, node) {
            return n;
        }
        Self(((file as u64) << 32) | (node.index() as u64 + 1))
    }

    /// File index in `GoProgram::files`.
    #[must_use]
    pub const fn file_index(self) -> usize {
        (self.0 >> 32) as usize
    }

    #[must_use]
    pub fn node_id(self) -> ts_ast::NodeId {
        ts_ast::NodeId::new(((self.0 & 0xffff_ffff) - 1) as u32)
    }
}

/// A symbol name and symbol table key (Go `string`). Every distinct text is
/// stored once for the whole process (see `intern`), and a `Name` is the
/// 4-byte id of that text. Clones copy the id. Equal names have equal ids,
/// so `==` compares ids. It orders, hashes and prints like the `str` it
/// holds.
#[derive(PartialEq, Eq)]
pub struct Name(u32);

impl Name {
    /// The text. Interned text lives until the process ends.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        intern::text(self.0)
    }
}

// PORT: not `Copy`, so existing `.clone()` calls stay clean for clippy.
impl Clone for Name {
    #[inline]
    fn clone(&self) -> Self {
        Name(self.0)
    }
}

impl Default for Name {
    fn default() -> Self {
        Name(0)
    }
}

impl std::hash::Hash for Name {
    // Hashes the text, so `Borrow<str>` lookups stay correct.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl PartialOrd for Name {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Name {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.0 == other.0 {
            return std::cmp::Ordering::Equal;
        }
        self.as_str().cmp(other.as_str())
    }
}

impl std::ops::Deref for Name {
    type Target = str;
    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl std::borrow::Borrow<str> for Name {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl std::fmt::Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.as_str(), f)
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.as_str(), f)
    }
}

impl From<&str> for Name {
    fn from(s: &str) -> Self {
        intern::intern(s)
    }
}

impl From<String> for Name {
    fn from(s: String) -> Self {
        intern::intern(&s)
    }
}

impl From<&String> for Name {
    fn from(s: &String) -> Self {
        intern::intern(s)
    }
}

impl From<&Name> for Name {
    fn from(s: &Name) -> Self {
        s.clone()
    }
}

impl From<Name> for String {
    fn from(s: Name) -> Self {
        s.as_str().to_owned()
    }
}

impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&str> for Name {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<String> for Name {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<Name> for str {
    fn eq(&self, other: &Name) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<Name> for &str {
    fn eq(&self, other: &Name) -> bool {
        *self == other.as_str()
    }
}

impl PartialEq<Name> for String {
    fn eq(&self, other: &Name) -> bool {
        self == other.as_str()
    }
}

/// The process-wide string interner behind `Name`. Text is copied once into
/// leaked blocks and never freed. Ids are dense and start at 1; id 0 is "".
/// `text` reads without a lock; `intern` takes one shard lock on a miss in
/// the per-thread cache.
mod intern {
    use super::Name;
    use rustc_hash::{FxBuildHasher, FxHashMap};
    use std::cell::RefCell;
    use std::sync::atomic::{AtomicU32, Ordering};
    use std::sync::{Mutex, OnceLock, PoisonError};

    /// Chunk `k` holds `FIRST_CHUNK << k` ids, so a few chunks cover all ids.
    const FIRST_CHUNK_SHIFT: u32 = 10;
    const CHUNKS: usize = 23;
    const SHARDS: usize = 32;
    const BLOCK: usize = 16 * 1024;
    const CACHE_SLOTS: usize = 1024;

    type Slots = Box<[OnceLock<&'static str>]>;
    static TEXTS: [OnceLock<Slots>; CHUNKS] = [const { OnceLock::new() }; CHUNKS];
    static NEXT: AtomicU32 = AtomicU32::new(1);

    struct Shard {
        ids: FxHashMap<&'static str, u32>,
        /// Unused tail of the current text block.
        free: &'static mut [u8],
    }

    static SHARD_LOCKS: OnceLock<Box<[Mutex<Shard>]>> = OnceLock::new();

    thread_local! {
        /// Direct-mapped cache of recent `intern` results: (hash, id).
        static CACHE: RefCell<Vec<(u64, u32)>> = const { RefCell::new(Vec::new()) };
    }

    /// Fx hash of `s`. Symbol tables use it too.
    #[inline]
    pub(super) fn hash_str(s: &str) -> u64 {
        use std::hash::Hasher;
        let mut hasher = rustc_hash::FxHasher::default();
        hasher.write(s.as_bytes());
        hasher.finish()
    }

    /// Chunk and slot of `id`.
    #[inline]
    fn slot(id: u32) -> (usize, usize) {
        let v = (id >> FIRST_CHUNK_SHIFT) + 1;
        let k = 31 - v.leading_zeros();
        let start = ((1u32 << k) - 1) << FIRST_CHUNK_SHIFT;
        (k as usize, (id - start) as usize)
    }

    /// The text of name id `id`.
    #[inline]
    pub(super) fn text(id: u32) -> &'static str {
        if id == 0 {
            return "";
        }
        let (chunk, index) = slot(id);
        TEXTS[chunk]
            .get()
            .and_then(|slots| slots[index].get())
            .copied()
            .expect("unknown name id")
    }

    /// The name for `s`, created on first use.
    pub(super) fn intern(s: &str) -> Name {
        if s.is_empty() {
            return Name(0);
        }
        let hash = hash_str(s);
        let cache_slot = (hash as usize) & (CACHE_SLOTS - 1);
        let cached = CACHE.with(|cache| {
            let cache = cache.borrow();
            let &(h, id) = cache.get(cache_slot)?;
            (id != 0 && h == hash && text(id) == s).then_some(id)
        });
        if let Some(id) = cached {
            return Name(id);
        }
        let id = intern_shared(s, hash);
        CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            if cache.is_empty() {
                cache.resize(CACHE_SLOTS, (0, 0));
            }
            cache[cache_slot] = (hash, id);
        });
        Name(id)
    }

    fn intern_shared(s: &str, hash: u64) -> u32 {
        let shards = SHARD_LOCKS.get_or_init(|| {
            (0..SHARDS)
                .map(|_| {
                    Mutex::new(Shard {
                        ids: FxHashMap::with_hasher(FxBuildHasher),
                        free: Default::default(),
                    })
                })
                .collect()
        });
        let mut shard = shards[(hash >> 59) as usize % SHARDS]
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some(&id) = shard.ids.get(s) {
            return id;
        }
        if shard.free.len() < s.len() {
            shard.free = Box::leak(vec![0u8; BLOCK.max(s.len())].into_boxed_slice());
        }
        let (head, tail) = std::mem::take(&mut shard.free).split_at_mut(s.len());
        head.copy_from_slice(s.as_bytes());
        shard.free = tail;
        let head: &'static [u8] = head;
        let stored = std::str::from_utf8(head).expect("interned text is UTF-8");
        let id = NEXT.fetch_add(1, Ordering::Relaxed);
        assert!(id != u32::MAX, "name id overflow");
        let (chunk, index) = slot(id);
        let slots = TEXTS[chunk].get_or_init(|| {
            (0..(1usize << (FIRST_CHUNK_SHIFT as usize + chunk)))
                .map(|_| OnceLock::new())
                .collect()
        });
        let _ = slots[index].set(stored);
        shard.ids.insert(stored, id);
        id
    }
}

/// `Symbol::declarations` (Go `[]*ast.Node`). An empty list allocates
/// nothing and a single declaration is stored inline. Longer lists share one
/// `Vec` between clones; the first write copies it, so each symbol still owns
/// its own list, like a Go slice that is copied before an append.
#[derive(Clone, Default)]
pub struct Declarations(DeclarationList);

#[derive(Clone, Default)]
enum DeclarationList {
    #[default]
    Empty,
    One(Node),
    Many(Arc<Vec<Node>>),
}

impl Declarations {
    /// Go `append(declarations, node)`.
    pub fn push(&mut self, node: Node) {
        match &mut self.0 {
            DeclarationList::Empty => self.0 = DeclarationList::One(node),
            DeclarationList::One(first) => {
                self.0 = DeclarationList::Many(Arc::new(vec![*first, node]));
            }
            DeclarationList::Many(list) => Arc::make_mut(list).push(node),
        }
    }
}

impl std::ops::Deref for Declarations {
    type Target = [Node];
    #[inline]
    fn deref(&self) -> &[Node] {
        match &self.0 {
            DeclarationList::Empty => &[],
            DeclarationList::One(node) => std::slice::from_ref(node),
            DeclarationList::Many(list) => list,
        }
    }
}

impl std::ops::DerefMut for Declarations {
    fn deref_mut(&mut self) -> &mut [Node] {
        match &mut self.0 {
            DeclarationList::Empty => &mut [],
            DeclarationList::One(node) => std::slice::from_mut(node),
            DeclarationList::Many(list) => Arc::make_mut(list).as_mut_slice(),
        }
    }
}

impl std::fmt::Debug for Declarations {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&**self, f)
    }
}

impl From<Vec<Node>> for Declarations {
    fn from(v: Vec<Node>) -> Self {
        Declarations(match v.as_slice() {
            [] => DeclarationList::Empty,
            [node] => DeclarationList::One(*node),
            _ => DeclarationList::Many(Arc::new(v)),
        })
    }
}

impl From<Declarations> for Vec<Node> {
    fn from(d: Declarations) -> Self {
        match d.0 {
            DeclarationList::Empty => Vec::new(),
            DeclarationList::One(node) => vec![node],
            DeclarationList::Many(list) => Arc::unwrap_or_clone(list),
        }
    }
}

/// By-value iterator over `Declarations`. It reads the shared list in place.
pub struct DeclarationsIntoIter {
    list: Declarations,
    next: usize,
}

impl Iterator for DeclarationsIntoIter {
    type Item = Node;
    #[inline]
    fn next(&mut self) -> Option<Node> {
        let node = self.list.get(self.next).copied()?;
        self.next += 1;
        Some(node)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let left = self.list.len() - self.next;
        (left, Some(left))
    }
}

impl ExactSizeIterator for DeclarationsIntoIter {}

impl IntoIterator for Declarations {
    type Item = Node;
    type IntoIter = DeclarationsIntoIter;
    fn into_iter(self) -> Self::IntoIter {
        DeclarationsIntoIter {
            list: self,
            next: 0,
        }
    }
}

impl<'a> IntoIterator for &'a Declarations {
    type Item = &'a Node;
    type IntoIter = std::slice::Iter<'a, Node>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Go `*ast.Symbol`. Field names follow Go.
#[derive(Clone, Debug, Default)]
pub struct Symbol {
    pub flags: SymbolFlags,
    pub check_flags: CheckFlags,
    pub name: Name,
    pub declarations: Declarations,
    pub value_declaration: Node,
    pub members: SymbolTable,
    pub exports: SymbolTable,
    pub parent: SymbolId,
    pub export_symbol: SymbolId,
}

/// A growable array split into fixed-size chunks that clones share by `Arc`.
/// The first write to a shared chunk copies only that chunk (`Arc::make_mut`).
/// Reads cost one extra pointer hop compared to a `Vec`.
#[derive(Clone, Debug)]
pub struct CowChunks<T> {
    chunks: Vec<Arc<Vec<T>>>,
    len: usize,
}

const COW_CHUNK_SHIFT: usize = 8;
const COW_CHUNK_LEN: usize = 1 << COW_CHUNK_SHIFT;
const COW_CHUNK_MASK: usize = COW_CHUNK_LEN - 1;

impl<T: Clone> CowChunks<T> {
    /// The values in order, moved out of chunks that no clone shares.
    pub fn into_values(self) -> impl Iterator<Item = T> {
        self.chunks
            .into_iter()
            .flat_map(|chunk| Arc::unwrap_or_clone(chunk).into_iter())
    }

    #[must_use]
    pub fn new() -> Self {
        Self {
            chunks: Vec::new(),
            len: 0,
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn push(&mut self, value: T) {
        if self.len & COW_CHUNK_MASK == 0 {
            // The first chunk grows on demand, so a one-file arena on a bind
            // thread stays small.
            self.chunks.push(Arc::new(if self.len == 0 {
                Vec::new()
            } else {
                Vec::with_capacity(COW_CHUNK_LEN)
            }));
        }
        let chunk = self.chunks.last_mut().expect("cow chunk");
        Arc::make_mut(chunk).push(value);
        self.len += 1;
    }

    #[inline]
    #[must_use]
    pub fn get(&self, i: usize) -> &T {
        &self.chunks[i >> COW_CHUNK_SHIFT][i & COW_CHUNK_MASK]
    }

    /// Copies the chunk first if another clone still shares it.
    #[inline]
    pub fn get_mut(&mut self, i: usize) -> &mut T {
        &mut Arc::make_mut(&mut self.chunks[i >> COW_CHUNK_SHIFT])[i & COW_CHUNK_MASK]
    }
}

impl<T: Clone> Default for CowChunks<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// One symbol table entry. `hash` is the low half of `intern::hash_str` of
/// the name, so a lookup by text skips most entries without reading them.
#[derive(Clone, Copy, Debug)]
struct TableEntry {
    hash: u32,
    name: u32,
    symbol: SymbolId,
}

/// Tables up to this size are searched linearly and have no index.
const TABLE_LINEAR_MAX: usize = 8;

/// A Go `ast.SymbolTable`: entries in insertion order. Larger tables also
/// keep an open-addressing index. A slot holds `position % INDEX_MOD + 1`
/// (0 is empty); a table longer than `INDEX_MOD` checks every position with
/// that remainder.
#[derive(Clone, Debug, Default)]
struct Table {
    entries: Vec<TableEntry>,
    index: Box<[u16]>,
}

const INDEX_MOD: usize = u16::MAX as usize;

#[inline]
fn table_hash(name: &str) -> u32 {
    let hash = intern::hash_str(name);
    (hash ^ (hash >> 32)) as u32
}

impl Table {
    fn with_capacity(capacity: usize) -> Self {
        Table {
            entries: Vec::with_capacity(capacity),
            index: Box::default(),
        }
    }

    /// The position of `name`, whose `table_hash` is `hash`.
    #[inline]
    fn find(&self, hash: u32, name: &str) -> Option<usize> {
        if self.index.is_empty() {
            return self
                .entries
                .iter()
                .position(|e| e.hash == hash && intern::text(e.name) == name);
        }
        let mask = self.index.len() - 1;
        let mut slot = hash as usize & mask;
        loop {
            let stored = self.index[slot];
            if stored == 0 {
                return None;
            }
            let mut position = stored as usize - 1;
            while position < self.entries.len() {
                let entry = &self.entries[position];
                if entry.hash == hash && intern::text(entry.name) == name {
                    return Some(position);
                }
                position += INDEX_MOD;
            }
            slot = (slot + 1) & mask;
        }
    }

    /// Adds `position` to the index. The index has a free slot.
    fn index_insert(index: &mut [u16], hash: u32, position: usize) {
        let mask = index.len() - 1;
        let mut slot = hash as usize & mask;
        while index[slot] != 0 {
            slot = (slot + 1) & mask;
        }
        index[slot] = u16::try_from(position % INDEX_MOD + 1).expect("index slot");
    }

    /// Rebuilds the index for the current entries.
    fn reindex(&mut self) {
        if self.entries.len() <= TABLE_LINEAR_MAX {
            self.index = Box::default();
            return;
        }
        let size = (self.entries.len() * 2).next_power_of_two();
        let mut index = vec![0u16; size].into_boxed_slice();
        for (position, entry) in self.entries.iter().enumerate() {
            Self::index_insert(&mut index, entry.hash, position);
        }
        self.index = index;
    }

    /// Go `table[name] = symbol`. A new name goes last, like `IndexMap`.
    fn insert(&mut self, name: &Name, symbol: SymbolId) {
        let hash = table_hash(name);
        if let Some(position) = self.find(hash, name) {
            self.entries[position].symbol = symbol;
            return;
        }
        self.entries.push(TableEntry {
            hash,
            name: name.0,
            symbol,
        });
        let len = self.entries.len();
        if len <= TABLE_LINEAR_MAX {
            return;
        }
        if self.index.len() < len * 2 {
            self.reindex();
        } else {
            Self::index_insert(&mut self.index, hash, len - 1);
        }
    }

    /// Go `delete(table, name)`. Later entries keep their order.
    fn remove(&mut self, name: &str) {
        if let Some(position) = self.find(table_hash(name), name) {
            self.entries.remove(position);
            self.reindex();
        }
    }
}

/// Owns all symbols and symbol tables. The binder fills one arena. Each
/// checker starts from a clone, so binder ids stay valid and checker
/// (transient) symbols stay private to that checker. The clone shares the
/// binder's symbol and table chunks; a checker copies a chunk only when it
/// first writes to it.
#[derive(Clone, Debug)]
pub struct SymbolArena {
    symbols: CowChunks<Symbol>,
    tables: CowChunks<Table>,
}

impl Default for SymbolArena {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolArena {
    #[must_use]
    pub fn new() -> Self {
        let mut symbols = CowChunks::new();
        symbols.push(Symbol::default());
        let mut tables = CowChunks::new();
        tables.push(Table::default());
        Self { symbols, tables }
    }

    /// Go `&ast.Symbol{Flags: flags, Name: name}`.
    pub fn new_symbol(&mut self, flags: SymbolFlags, name: impl Into<Name>) -> SymbolId {
        let id = SymbolId(u32::try_from(self.symbols.len()).expect("symbol overflow"));
        self.symbols.push(Symbol {
            flags,
            name: name.into(),
            ..Symbol::default()
        });
        id
    }

    fn push_table(&mut self, table: Table) -> SymbolTable {
        let id = SymbolTable(u32::try_from(self.tables.len()).expect("table overflow"));
        self.tables.push(table);
        id
    }

    /// Go `make(ast.SymbolTable)`.
    pub fn new_table(&mut self) -> SymbolTable {
        self.push_table(Table::default())
    }

    /// Go `make(ast.SymbolTable, capacity)`.
    pub fn new_table_with_capacity(&mut self, capacity: usize) -> SymbolTable {
        self.push_table(Table::with_capacity(capacity))
    }

    /// Appends the symbols and tables of `file_arena`, an arena that one
    /// file was bound into on its own, and returns how its ids moved. The
    /// ids get the values that binding the file into this arena would give:
    /// every id moves by the number of entries already here.
    // PORT: the binder writes a symbol id into the names of private
    // identifier symbols (`get_symbol_name_for_private_identifier`), so those
    // names move with the ids.
    pub fn append_file_arena(&mut self, file_arena: SymbolArena) -> ArenaOffsets {
        let offsets = ArenaOffsets {
            symbols: u32::try_from(self.symbols.len() - 1).expect("symbol overflow"),
            tables: u32::try_from(self.tables.len() - 1).expect("table overflow"),
        };
        let SymbolArena { symbols, tables } = file_arena;
        // Move the entries instead of copying them: the file arena was
        // built on a bind thread, and its buffers stay in use here.
        for symbol in symbols.into_values().skip(1) {
            self.symbols.push(Symbol {
                name: offsets.name(&symbol.name),
                members: offsets.table(symbol.members),
                exports: offsets.table(symbol.exports),
                parent: offsets.symbol(symbol.parent),
                export_symbol: offsets.symbol(symbol.export_symbol),
                ..symbol
            });
        }
        for mut table in tables.into_values().skip(1) {
            let mut renamed = false;
            for entry in &mut table.entries {
                let name = offsets.name(&Name(entry.name));
                if name.0 != entry.name {
                    renamed = true;
                    entry.name = name.0;
                    entry.hash = table_hash(&name);
                }
                entry.symbol = offsets.symbol(entry.symbol);
            }
            if renamed {
                table.reindex();
            }
            self.tables.push(table);
        }
        offsets
    }

    /// Go `maps.Clone(table)`. A nil table clones to nil.
    pub fn clone_table(&mut self, table: SymbolTable) -> SymbolTable {
        if table.is_nil() {
            return SymbolTable::NIL;
        }
        let cloned = self.tables.get(table.index()).clone();
        self.push_table(cloned)
    }

    #[must_use]
    pub fn sym(&self, symbol: SymbolId) -> &Symbol {
        debug_assert!(symbol.is_some(), "nil symbol dereference");
        self.symbols.get(symbol.index())
    }

    pub fn sym_mut(&mut self, symbol: SymbolId) -> &mut Symbol {
        debug_assert!(symbol.is_some(), "nil symbol dereference");
        self.symbols.get_mut(symbol.index())
    }

    /// Go `table[name]`. A nil table reads as empty.
    #[must_use]
    pub fn get(&self, table: SymbolTable, name: &str) -> SymbolId {
        if table.is_nil() {
            return SymbolId::NIL;
        }
        let table = self.tables.get(table.index());
        if table.entries.is_empty() {
            return SymbolId::NIL;
        }
        table
            .find(table_hash(name), name)
            .map_or(SymbolId::NIL, |position| table.entries[position].symbol)
    }

    /// Go `table[name] = symbol`. Panics on a nil table, like Go.
    pub fn set(&mut self, table: SymbolTable, name: impl Into<Name>, symbol: SymbolId) {
        assert!(table.is_some(), "assignment to entry in nil map");
        let name = name.into();
        self.tables.get_mut(table.index()).insert(&name, symbol);
    }

    /// Go `delete(table, name)`.
    pub fn delete(&mut self, table: SymbolTable, name: &str) {
        if table.is_some() {
            self.tables.get_mut(table.index()).remove(name);
        }
    }

    /// Go `len(table)`.
    #[must_use]
    pub fn len(&self, table: SymbolTable) -> usize {
        if table.is_nil() {
            0
        } else {
            self.tables.get(table.index()).entries.len()
        }
    }

    fn table_entries(&self, table: SymbolTable) -> &[TableEntry] {
        if table.is_nil() {
            &[]
        } else {
            &self.tables.get(table.index()).entries
        }
    }

    /// Snapshot of `(name, symbol)` pairs in insertion order. Go map order is
    /// random, so Go code never depends on it; ours is deterministic.
    #[must_use]
    pub fn entries(&self, table: SymbolTable) -> Vec<(Name, SymbolId)> {
        self.table_entries(table)
            .iter()
            .map(|e| (Name(e.name), e.symbol))
            .collect()
    }

    /// Borrowed `(name, symbol)` pairs in insertion order. Use it instead of
    /// `entries` when the table does not change during the loop.
    pub fn iter(&self, table: SymbolTable) -> impl Iterator<Item = (&str, SymbolId)> {
        self.table_entries(table)
            .iter()
            .map(|e| (intern::text(e.name), e.symbol))
    }

    /// Snapshot of the values in insertion order.
    #[must_use]
    pub fn values(&self, table: SymbolTable) -> Vec<SymbolId> {
        self.table_entries(table).iter().map(|e| e.symbol).collect()
    }
}

/// How the ids of a file arena moved in `SymbolArena::append_file_arena`.
#[derive(Clone, Copy, Debug)]
pub struct ArenaOffsets {
    symbols: u32,
    tables: u32,
}

impl ArenaOffsets {
    /// The program id of file arena symbol `symbol`.
    #[must_use]
    pub fn symbol(self, symbol: SymbolId) -> SymbolId {
        if symbol.is_nil() {
            symbol
        } else {
            SymbolId(symbol.0 + self.symbols)
        }
    }

    /// The program id of file arena table `table`.
    #[must_use]
    pub fn table(self, table: SymbolTable) -> SymbolTable {
        if table.is_nil() {
            table
        } else {
            SymbolTable(table.0 + self.tables)
        }
    }

    /// `name`, with the symbol id in a private identifier name
    /// (`<prefix>#<id>@<description>`) moved.
    fn name(self, name: &Name) -> Name {
        const PRIVATE_PREFIX: &str = "\u{FFFE}#";
        if self.symbols == 0 || !name.starts_with(PRIVATE_PREFIX) {
            return name.clone();
        }
        let rest = &name[PRIVATE_PREFIX.len()..];
        let Some(at) = rest.find('@') else {
            return name.clone();
        };
        let Ok(id) = rest[..at].parse::<u32>() else {
            return name.clone();
        };
        let moved = self.symbol(SymbolId(id));
        Name::from(format!("{PRIVATE_PREFIX}{}{}", moved.0, &rest[at..]))
    }
}

/// Go `*ast.FlowNode`. `antecedents` replaces the Go `FlowList` linked list
/// in the same order.
#[derive(Clone, Debug, Default)]
pub struct FlowNode {
    pub flags: FlowFlags,
    pub node: Node,
    pub antecedent: FlowNodeId,
    pub antecedents: Vec<FlowNodeId>,
}

/// Go `ast.PatternAmbientModule`.
#[derive(Clone, Debug)]
pub struct PatternAmbientModule {
    pub pattern_prefix: String,
    pub pattern_suffix: String,
    pub symbol: SymbolId,
}

/// Binder output for one node. Go stores these on the node itself.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NodeBindData {
    pub symbol: SymbolId,
    pub local_symbol: SymbolId,
    pub locals: SymbolTable,
    pub next_container: Node,
    pub flow_node: FlowNodeId,
    pub end_flow_node: FlowNodeId,
    pub return_flow_node: FlowNodeId,
    /// Go `NodeFlags` bits the binder ORs into `node.Flags`.
    pub added_flags: NodeFlags,
}

/// Binder data of every node of one bound file, stored compactly. Most
/// nodes have no data, or the same data as the node before them (a run of
/// identifiers in one flow region), so they share one entry. Each node keeps
/// one byte: the offset of its entry from the first entry of its block.
#[derive(Debug, Default)]
pub struct FileNodeBind {
    /// Per node, by `NodeId::index()`: entry offset in its block, or
    /// `NO_NODE_BIND` for the empty data.
    slots: Vec<u8>,
    /// Per block of `NODE_BIND_BLOCK` nodes: the index of its first entry.
    bases: Vec<u32>,
    entries: Vec<NodeBindData>,
}

const NODE_BIND_BLOCK_BITS: usize = 7;
const NODE_BIND_BLOCK: usize = 1 << NODE_BIND_BLOCK_BITS;
const NO_NODE_BIND: u8 = u8::MAX;

/// The empty binder data.
static EMPTY_NODE_BIND: NodeBindData = NodeBindData {
    symbol: SymbolId::NIL,
    local_symbol: SymbolId::NIL,
    locals: SymbolTable::NIL,
    next_container: Node::NIL,
    flow_node: FlowNodeId::NIL,
    end_flow_node: FlowNodeId::NIL,
    return_flow_node: FlowNodeId::NIL,
    added_flags: NodeFlags::NONE,
};

impl FileNodeBind {
    /// Compacts the per-node data of a bound file.
    #[must_use]
    pub fn new(nodes: &[NodeBindData]) -> Self {
        let mut slots = Vec::with_capacity(nodes.len());
        let mut bases = Vec::with_capacity(nodes.len().div_ceil(NODE_BIND_BLOCK));
        let mut entries: Vec<NodeBindData> = Vec::new();
        let mut block_start = 0;
        for (index, data) in nodes.iter().enumerate() {
            if index & (NODE_BIND_BLOCK - 1) == 0 {
                block_start = entries.len();
                bases.push(u32::try_from(block_start).expect("node bind overflow"));
            }
            if *data == EMPTY_NODE_BIND {
                slots.push(NO_NODE_BIND);
                continue;
            }
            // Entries are shared only inside a block, so offsets stay small.
            if entries.len() == block_start || entries.last() != Some(data) {
                entries.push(*data);
            }
            slots.push(u8::try_from(entries.len() - 1 - block_start).expect("block offset"));
        }
        entries.shrink_to_fit();
        FileNodeBind {
            slots,
            bases,
            entries,
        }
    }

    /// The distinct data entries, for remapping ids in place. Non-empty data
    /// stays non-empty and distinct under an id remap.
    pub fn entries_mut(&mut self) -> &mut [NodeBindData] {
        &mut self.entries
    }

    /// The data of node `index` (`NodeId::index()`).
    #[inline]
    #[must_use]
    pub fn get(&self, index: usize) -> &NodeBindData {
        let offset = self.slots[index];
        if offset == NO_NODE_BIND {
            return &EMPTY_NODE_BIND;
        }
        &self.entries[self.bases[index >> NODE_BIND_BLOCK_BITS] as usize + offset as usize]
    }
}

/// Binder output for one source file. Go stores these on `ast.SourceFile`.
#[derive(Clone, Debug, Default)]
pub struct FileBindData {
    pub bind_diagnostics: Vec<Diagnostic>,
    pub bind_suggestion_diagnostics: Vec<Diagnostic>,
    pub end_flow_node: FlowNodeId,
    pub symbol_count: i32,
    /// Go `ClassifiableNames`. Nothing reads it; interned names keep it small.
    pub classifiable_names: rustc_hash::FxHashSet<Name>,
    pub pattern_ambient_modules: Vec<PatternAmbientModule>,
    pub global_exports: SymbolTable,
    /// Go `JSGlobalAugmentations`.
    pub js_global_augmentations: SymbolTable,
}

/// Go `*ast.Diagnostic`. Positions are Go positions (UTF-8 byte offsets).
/// `file` is the source file node, or nil for a global diagnostic.
#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub file: Node,
    pub pos: i32,
    pub end: i32,
    pub code: i32,
    pub category: ts_diagnostics::Category,
    pub message: &'static ts_diagnostics::Message,
    pub message_args: Vec<String>,
    pub message_chain: Vec<Diagnostic>,
    pub related_information: Vec<Diagnostic>,
    pub reports_unnecessary: bool,
    pub reports_deprecated: bool,
    /// Go `skippedOnNoEmit`: dropped from semantic diagnostics when noEmit is set.
    pub skipped_on_no_emit: bool,
}

/// Go `...any` diagnostic arguments. Go formats each with `%v`; we use
/// `ToString`. Example: `args![self.type_to_string(t), count]`.
#[macro_export]
macro_rules! args {
    ($($arg:expr),* $(,)?) => { vec![$(::std::string::ToString::to_string(&$arg)),*] };
}

/// A `LinkStore` key. Arena handles are dense small indexes, and node and
/// flow node handles are dense small indexes within a file, so their links
/// live in paged slot arrays instead of a hash map.
pub trait LinkKey: Copy + Eq + std::hash::Hash {
    /// The (group, index) of a key with paged slots, or `None` for a key
    /// that lives in the hash map.
    fn dense_key(self) -> Option<(usize, usize)>;
}

macro_rules! dense_link_key {
    ($($name:ident),*) => {$(
        impl LinkKey for $name {
            #[inline]
            fn dense_key(self) -> Option<(usize, usize)> {
                Some((0, self.index()))
            }
        }
    )*};
}

dense_link_key!(
    TypeId,
    SymbolId,
    SignatureId,
    IndexInfoId,
    TypePredicateId,
    MapperId,
    InferenceContextId,
    SymbolTable
);

/// Files with an index below this get paged node slots. Synthetic nodes
/// (a file index near `u32::MAX`) use the hash map.
const LINK_MAX_GROUPS: u64 = 1 << 20;

/// Splits a (file << 32 | local + 1) handle into (file, local + 1).
#[inline]
fn file_dense_key(handle: u64) -> Option<(usize, usize)> {
    let file = handle >> 32;
    (file < LINK_MAX_GROUPS).then_some((file as usize, (handle & 0xffff_ffff) as usize))
}

impl LinkKey for Node {
    #[inline]
    fn dense_key(self) -> Option<(usize, usize)> {
        file_dense_key(self.0)
    }
}

impl LinkKey for FlowNodeId {
    #[inline]
    fn dense_key(self) -> Option<(usize, usize)> {
        file_dense_key(self.0)
    }
}

/// Slots per page of a `LinkStore`. Small pages keep sparse stores small.
const LINK_PAGE_BITS: usize = 6;
const LINK_PAGE_SIZE: usize = 1 << LINK_PAGE_BITS;

type LinkPages = Vec<Option<Box<[u32; LINK_PAGE_SIZE]>>>;

/// Go `core.LinkStore[K, V]`: lazily created per-key link records.
/// Dense keys map through paged slots (value index + 1, zero is absent) into
/// `values`. Other keys use a hash map.
#[derive(Clone, Debug)]
pub struct LinkStore<K: LinkKey, V: Default> {
    /// Slot pages by key group (the file for node keys).
    groups: Vec<LinkPages>,
    /// Dense values in fixed-size chunks, so growth never copies or
    /// over-allocates a large block.
    values: Vec<Vec<V>>,
    len: usize,
    map: FxHashMap<K, V>,
}

/// Values per chunk of a dense `LinkStore`.
const LINK_CHUNK_BITS: usize = 12;
const LINK_CHUNK_SIZE: usize = 1 << LINK_CHUNK_BITS;

impl<K: LinkKey, V: Default> Default for LinkStore<K, V> {
    fn default() -> Self {
        Self {
            groups: Vec::new(),
            values: Vec::new(),
            len: 0,
            map: FxHashMap::default(),
        }
    }
}

impl<K: LinkKey, V: Default> LinkStore<K, V> {
    /// The value index for a dense key, if it has a record.
    #[inline]
    fn dense_slot(&self, group: usize, index: usize) -> Option<usize> {
        let page = self
            .groups
            .get(group)?
            .get(index >> LINK_PAGE_BITS)?
            .as_ref()?;
        let slot = page[index & (LINK_PAGE_SIZE - 1)];
        (slot != 0).then(|| slot as usize - 1)
    }

    #[inline]
    fn value(&self, value: usize) -> &V {
        &self.values[value >> LINK_CHUNK_BITS][value & (LINK_CHUNK_SIZE - 1)]
    }

    /// Go `store.Get(key)`: creates the record on first use.
    pub fn get(&mut self, key: K) -> &mut V {
        let Some((group, index)) = key.dense_key() else {
            return self.map.entry(key).or_default();
        };
        if group >= self.groups.len() {
            self.groups.resize_with(group + 1, Vec::new);
        }
        let pages = &mut self.groups[group];
        let page_index = index >> LINK_PAGE_BITS;
        if page_index >= pages.len() {
            pages.resize_with(page_index + 1, || None);
        }
        let page = pages[page_index].get_or_insert_with(|| Box::new([0; LINK_PAGE_SIZE]));
        let slot = &mut page[index & (LINK_PAGE_SIZE - 1)];
        if *slot == 0 {
            if self.len & (LINK_CHUNK_SIZE - 1) == 0 {
                // The first chunk grows on demand; small stores stay small.
                self.values.push(if self.len == 0 {
                    Vec::new()
                } else {
                    Vec::with_capacity(LINK_CHUNK_SIZE)
                });
            }
            self.values
                .last_mut()
                .expect("link chunk")
                .push(V::default());
            self.len += 1;
            *slot = u32::try_from(self.len).expect("link store overflow");
        }
        let value = *slot as usize - 1;
        &mut self.values[value >> LINK_CHUNK_BITS][value & (LINK_CHUNK_SIZE - 1)]
    }

    /// Go `store.Has(key)`.
    #[must_use]
    pub fn has(&self, key: K) -> bool {
        match key.dense_key() {
            Some((group, index)) => self.dense_slot(group, index).is_some(),
            None => self.map.contains_key(&key),
        }
    }

    /// Go `store.TryGet(key)`.
    #[must_use]
    pub fn try_get(&self, key: K) -> Option<&V> {
        match key.dense_key() {
            Some((group, index)) => self.dense_slot(group, index).map(|value| self.value(value)),
            None => self.map.get(&key),
        }
    }
}

/// Unported hits of every thread, by Go name.
static UNPORTED_NAMES: std::sync::Mutex<std::collections::BTreeMap<&'static str, u64>> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

/// Records one hit of unported Go code. The runner reports every name.
/// A run with any hit is not a match.
pub fn record_unported(go_name: &'static str) {
    let mut names = UNPORTED_NAMES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    *names.entry(go_name).or_default() += 1;
}

/// All unported names hit so far on any thread, with hit counts.
#[must_use]
pub fn unported_report() -> Vec<(&'static str, u64)> {
    let names = UNPORTED_NAMES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    names.iter().map(|(k, v)| (*k, *v)).collect()
}

/// Puts back the unported hits that `unported_report` returned. Work that
/// is thrown away and redone uses it, so the hits are not counted twice.
pub fn restore_unported(report: &[(&'static str, u64)]) {
    let mut names = UNPORTED_NAMES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    *names = report.iter().copied().collect();
}

/// Marks unported Go code. It records the hit, then panics so the gap is
/// loud. Use only where a port is missing, never as a fallback.
#[macro_export]
macro_rules! unported {
    ($go_name:expr) => {{
        $crate::core::record_unported($go_name);
        panic!("unported Go code: {}", $go_name)
    }};
}

/// One loaded source file. Parser data is ready when the program is
/// installed. The binder fills the `OnceLock` fields once per file.
pub struct GoFile {
    /// The ts_compiler source file (arena, text, file name). None for a
    /// file parsed by the Go frontend (`GOPORT_FRONTEND=go`), whose nodes
    /// live in a node store (`ast::store`).
    pub source: Option<&'static ts_compiler::SourceFile>,
    /// The `SourceFile` node.
    pub root: Node,
    /// Go `node.Flags` from the parser for each node, indexed by
    /// `NodeId::index()`. It includes the Go parser context flags.
    pub parser_flags: Vec<NodeFlags>,
    /// Go `ast.SourceFile` fields that the parser and program set.
    pub info: crate::program::SourceFileInfo,
    /// Binder data per node, indexed by `NodeId::index()`.
    pub node_bind: std::sync::OnceLock<FileNodeBind>,
    pub file_bind: std::sync::OnceLock<FileBindData>,
    pub flow_nodes: std::sync::OnceLock<Vec<FlowNode>>,
}

/// Go `Program` as the checker sees it. Installed once per process with
/// `crate::program::install`, then read with `prog()`.
pub struct GoProgram {
    /// The legacy graph. None on the Go frontend path.
    pub program: Option<&'static ts_compiler::Program>,
    /// Files by file index. `Node::file_index` indexes it. On the Go frontend
    /// path this holds every node store, including config files that are not
    /// program source files.
    pub files: Vec<GoFile>,
    /// File indexes in Go `Program.SourceFiles()` order.
    pub source_file_order: Vec<usize>,
    pub options: crate::options::CompilerOptions,
    /// Binder symbols. Each checker clones this.
    pub bound_symbols: std::sync::OnceLock<SymbolArena>,
}

impl GoFile {
    /// The legacy source file. Panics for a Go frontend file; callers check
    /// `ast::store::has_file_store` first.
    #[must_use]
    pub fn legacy_source(&self) -> &'static ts_compiler::SourceFile {
        self.source
            .expect("legacy source read for a Go frontend file")
    }
}

impl GoProgram {
    /// Go `Program.SourceFiles()`: the program files in Go order.
    pub fn source_files(&self) -> impl Iterator<Item = &GoFile> {
        self.source_file_order
            .iter()
            .map(|&index| &self.files[index])
    }
}

/// The installed program, shared by every thread (the checker workers read
/// it too). Set once.
static PROGRAM: std::sync::OnceLock<&'static GoProgram> = std::sync::OnceLock::new();

/// Installs the program for the process. Call once. Freezes the node
/// stores first (`ast::store::freeze_file_stores`): the parse is over.
pub fn set_prog(program: &'static GoProgram) {
    crate::ast::freeze_file_stores();
    assert!(PROGRAM.set(program).is_ok(), "GoProgram already installed");
}

/// The installed program, or `None` before `set_prog`. The ported parser
/// reads nodes before the program exists.
#[inline]
#[must_use]
pub fn try_prog() -> Option<&'static GoProgram> {
    PROGRAM.get().copied()
}

/// The installed program. Go code reads nodes without a context; this is
/// how node accessors reach the AST.
#[inline]
#[must_use]
pub fn prog() -> &'static GoProgram {
    PROGRAM.get().copied().expect("GoProgram not installed")
}

// Go: core/version.go:8 version
// PORT: Go keeps this in a var that ldflags can override. The pinned
// reference build does not override it.
const VERSION: &str = "7.0.0-dev";

// Go: core/version.go:10 Version
pub fn version() -> &'static str {
    VERSION
}

// Go: core/version.go:14 versionMajorMinor
// Go: core/version.go:31 VersionMajorMinor
pub fn version_major_minor() -> &'static str {
    let mut seen_major = false;
    let i = VERSION.find(|r: char| {
        if r == '.' {
            if seen_major {
                return true;
            }
            seen_major = true;
        }
        false
    });
    match i {
        Some(i) => &VERSION[..i],
        None => panic!("invalid version string: {VERSION}"),
    }
}
