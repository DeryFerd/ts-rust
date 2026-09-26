//! Shared handles and stores for the Go port. Read `PORTING.md` first.
//!
//! Every Go pointer to a shared object becomes a `Copy` handle. Handle value
//! zero is Go `nil`, so Go `x == nil` ports to `x.is_nil()`.

use indexmap::IndexMap;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
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
/// `*ast.SourceFile`, ...). High 32 bits: file id in the file registry
/// (`ast/store.rs`). For a ported-parser file this is also its store id.
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

    #[inline]
    #[must_use]
    pub fn new(file: usize, node: ts_ast::NodeId) -> Self {
        // After freeze, a store file resolves every child id in one read.
        // The synthetic file has no store, so it takes the slow path.
        if let Some(resolved) = crate::ast::frozen_resolved(file) {
            return resolved[node.index()];
        }
        Self::new_slow(file, node)
    }

    #[inline(never)]
    fn new_slow(file: usize, node: ts_ast::NodeId) -> Self {
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

    /// File id in the file registry (`crate::ast::go_file`).
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

    /// `table_hash` of the text. The interner keeps it, so this reads one
    /// number and does not touch the text.
    #[inline]
    fn table_hash(&self) -> u32 {
        intern::table_hash(self.0)
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
/// leaked blocks and never freed. Ids start at 1 and are close to dense
/// (see `next_id`); id 0 is "".
/// `text` reads without a lock; `intern` takes one shard lock on a miss in
/// the per-thread cache.
mod intern {
    use super::Name;
    use rustc_hash::{FxBuildHasher, FxHashMap};
    use std::cell::Cell;
    use std::collections::HashMap;
    use std::hash::{BuildHasherDefault, Hasher};
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
    /// The table hash (`super::fold_hash`) of each id's text, in the same
    /// chunks as `TEXTS`. A table lookup by `Name` reads it instead of
    /// reading and hashing the text again.
    static HASHES: [OnceLock<Box<[AtomicU32]>>; CHUNKS] = [const { OnceLock::new() }; CHUNKS];
    /// The next id block. Only `next_id` reads it.
    static NEXT: AtomicU32 = AtomicU32::new(1);
    /// Ids that a thread takes from `NEXT` at once.
    const ID_BLOCK: u32 = 64;

    /// Hasher for `u64` keys that already are a `hash_str` hash, so a
    /// lookup does not hash the text again. The halves swap because the
    /// shard index uses the top bits, and the map also reads the top bits.
    #[derive(Default)]
    struct HashIsKey(u64);

    impl Hasher for HashIsKey {
        fn finish(&self) -> u64 {
            self.0
        }

        fn write(&mut self, _: &[u8]) {
            unreachable!("HashIsKey takes only u64 keys");
        }

        fn write_u64(&mut self, hash: u64) {
            self.0 = hash.rotate_left(32);
        }
    }

    struct Shard {
        /// `(text, id)` by the `hash_str` hash of the text.
        ids: HashMap<u64, (&'static str, u32), BuildHasherDefault<HashIsKey>>,
        /// Texts whose hash another text in `ids` already has.
        collisions: FxHashMap<&'static str, u32>,
        /// Unused tail of the current text block.
        free: &'static mut [u8],
    }

    /// A shard lock on its own 128 bytes, so threads that lock neighboring
    /// shards do not share a cache line (x86 fetches lines in pairs).
    #[repr(align(128))]
    struct PaddedShard(Mutex<Shard>);

    static SHARD_LOCKS: OnceLock<[PaddedShard; SHARDS]> = OnceLock::new();

    /// One `CACHE` slot: (hash, id, text). Id 0 marks an empty slot.
    type CacheSlot = Cell<(u64, u32, &'static str)>;

    thread_local! {
        /// Direct-mapped cache of recent `intern` results. It is a const
        /// array with no destructor, so a hit reads thread-local memory
        /// directly and needs no lazy init, borrow flag or `text` lookup.
        static CACHE: [CacheSlot; CACHE_SLOTS] =
            const { [const { Cell::new((0, 0, "")) }; CACHE_SLOTS] };

        /// The ids this thread took from `NEXT` and did not use yet:
        /// (next, end).
        static IDS: Cell<(u32, u32)> = const { Cell::new((0, 0)) };
    }

    /// A new name id.
    // PERF: a thread takes `ID_BLOCK` ids from `NEXT` at once, so threads
    // that intern new names do not contend on one atomic, and the names of
    // one file get close ids (their `HASHES` and `TEXTS` slots share cache
    // lines). An id only has to be unique: ids already came in thread race
    // order, and no output orders by id (`Name` orders by text). A thread
    // that ends leaves its unused ids as empty slots.
    fn next_id() -> u32 {
        IDS.with(|ids| {
            let (mut next, mut end) = ids.get();
            if next == end {
                next = NEXT.fetch_add(ID_BLOCK, Ordering::Relaxed);
                // `end` fits, so no id is `u32::MAX`.
                end = next.checked_add(ID_BLOCK).expect("name id overflow");
            }
            ids.set((next + 1, end));
            next
        })
    }

    /// Fx hash of `s`. Symbol tables use it too.
    #[inline]
    pub(super) fn hash_str(s: &str) -> u64 {
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

    /// The table hash of the text of name id `id`.
    #[inline]
    pub(super) fn table_hash(id: u32) -> u32 {
        if id == 0 {
            return super::fold_hash(hash_str(""));
        }
        let (chunk, index) = slot(id);
        // Relaxed is enough: a thread gets `id` from `intern_shared` under
        // the shard lock or through a later handoff, and both order the
        // store in `intern_shared` before this load.
        HASHES[chunk].get().expect("unknown name id")[index].load(Ordering::Relaxed)
    }

    /// The name for `s`, created on first use.
    pub(super) fn intern(s: &str) -> Name {
        if s.is_empty() {
            return Name(0);
        }
        let hash = hash_str(s);
        let cache_slot = (hash as usize) & (CACHE_SLOTS - 1);
        let cached = CACHE.with(|cache| {
            let (h, id, stored) = cache[cache_slot].get();
            (id != 0 && h == hash && stored == s).then_some(id)
        });
        if let Some(id) = cached {
            return Name(id);
        }
        let (id, stored) = intern_shared(s, hash);
        CACHE.with(|cache| cache[cache_slot].set((hash, id, stored)));
        Name(id)
    }

    /// The id and stored text of `s`, from the shared map.
    fn intern_shared(s: &str, hash: u64) -> (u32, &'static str) {
        let shards = SHARD_LOCKS.get_or_init(|| {
            std::array::from_fn(|_| {
                PaddedShard(Mutex::new(Shard {
                    ids: HashMap::default(),
                    collisions: FxHashMap::with_hasher(FxBuildHasher),
                    free: Default::default(),
                }))
            })
        });
        let mut shard = shards[(hash >> 59) as usize % SHARDS]
            .0
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let hash_taken = match shard.ids.get(&hash) {
            Some(&(stored, id)) if stored == s => return (id, stored),
            Some(_) => {
                if let Some((&stored, &id)) = shard.collisions.get_key_value(s) {
                    return (id, stored);
                }
                true
            }
            None => false,
        };
        if shard.free.len() < s.len() {
            shard.free = Box::leak(vec![0u8; BLOCK.max(s.len())].into_boxed_slice());
        }
        let (head, tail) = std::mem::take(&mut shard.free).split_at_mut(s.len());
        head.copy_from_slice(s.as_bytes());
        shard.free = tail;
        let head: &'static [u8] = head;
        let stored = std::str::from_utf8(head).expect("interned text is UTF-8");
        let id = next_id();
        let (chunk, index) = slot(id);
        let chunk_len = 1usize << (FIRST_CHUNK_SHIFT as usize + chunk);
        let hashes =
            HASHES[chunk].get_or_init(|| (0..chunk_len).map(|_| AtomicU32::new(0)).collect());
        hashes[index].store(super::fold_hash(hash), Ordering::Relaxed);
        let slots = TEXTS[chunk].get_or_init(|| (0..chunk_len).map(|_| OnceLock::new()).collect());
        let _ = slots[index].set(stored);
        if hash_taken {
            shard.collisions.insert(stored, id);
        } else {
            shard.ids.insert(hash, (stored, id));
        }
        (id, stored)
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

/// A growable array split into fixed-size chunks. A chunk is either owned
/// by this array, so writes need no atomic operation, or shared with clones
/// by `Arc`. `share` turns the owned chunks into shared ones before the array
/// is cloned; a clone copies owned chunks. The first write to a shared chunk
/// takes it back (a copy only when a clone still uses it).
/// Reads cost one extra pointer hop compared to a `Vec`.
#[derive(Clone, Debug)]
pub struct CowChunks<T> {
    chunks: Vec<Chunk<T>>,
    len: usize,
}

#[derive(Clone, Debug)]
enum Chunk<T> {
    Owned(Vec<T>),
    Shared(Arc<Vec<T>>),
}

impl<T: Clone> Chunk<T> {
    #[inline]
    fn values(&self) -> &[T] {
        match self {
            Chunk::Owned(values) => values,
            Chunk::Shared(values) => values,
        }
    }

    /// The values, owned. Takes a shared chunk back first.
    #[inline]
    fn owned(&mut self) -> &mut Vec<T> {
        if matches!(self, Chunk::Shared(_)) {
            let taken = std::mem::replace(self, Chunk::Owned(Vec::new()));
            *self = Chunk::Owned(taken.into_values());
        }
        match self {
            Chunk::Owned(values) => values,
            Chunk::Shared(_) => unreachable!("chunk was just taken back"),
        }
    }

    fn into_values(self) -> Vec<T> {
        match self {
            Chunk::Owned(values) => values,
            Chunk::Shared(values) => Arc::unwrap_or_clone(values),
        }
    }
}

const COW_CHUNK_SHIFT: usize = 8;
const COW_CHUNK_LEN: usize = 1 << COW_CHUNK_SHIFT;
const COW_CHUNK_MASK: usize = COW_CHUNK_LEN - 1;

impl<T: Clone> CowChunks<T> {
    /// The values in order, moved out of chunks that no clone shares.
    pub fn into_values(self) -> impl Iterator<Item = T> {
        self.chunks.into_iter().flat_map(Chunk::into_values)
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
            self.chunks.push(Chunk::Owned(if self.len == 0 {
                Vec::new()
            } else {
                Vec::with_capacity(COW_CHUNK_LEN)
            }));
        }
        self.chunks
            .last_mut()
            .expect("cow chunk")
            .owned()
            .push(value);
        self.len += 1;
    }

    /// Pushes every value in order, like `push` in a loop. Each chunk is
    /// filled in one step.
    pub fn extend(&mut self, values: impl IntoIterator<Item = T>) {
        let mut values = values.into_iter();
        loop {
            if self.len & COW_CHUNK_MASK == 0 {
                // `push` starts the next chunk.
                let Some(value) = values.next() else { return };
                self.push(value);
            }
            let room = COW_CHUNK_LEN - (self.len & COW_CHUNK_MASK);
            let tail = self.chunks.last_mut().expect("cow chunk").owned();
            let before = tail.len();
            tail.extend(values.by_ref().take(room));
            let added = tail.len() - before;
            self.len += added;
            if added < room {
                return;
            }
        }
    }

    #[inline]
    #[must_use]
    pub fn get(&self, i: usize) -> &T {
        &self.chunks[i >> COW_CHUNK_SHIFT].values()[i & COW_CHUNK_MASK]
    }

    /// Takes the chunk back first if it is shared.
    #[inline]
    pub fn get_mut(&mut self, i: usize) -> &mut T {
        &mut self.chunks[i >> COW_CHUNK_SHIFT].owned()[i & COW_CHUNK_MASK]
    }

    /// Makes the chunks that hold values from index `from` on shared, so
    /// clones copy none of them. Pass 0 to share every chunk.
    pub fn share_from(&mut self, from: usize) {
        let first = (from >> COW_CHUNK_SHIFT).min(self.chunks.len());
        for chunk in &mut self.chunks[first..] {
            if let Chunk::Owned(values) = chunk {
                *chunk = Chunk::Shared(Arc::new(std::mem::take(values)));
            }
        }
    }

    /// Moves the values from index `skip` on into chunks for `append_aligned`
    /// at index `at` of another array, and runs `f` on each value first, in
    /// order. The chunks end where the chunks of that array end, so the
    /// append moves whole chunks and moves no value, except the values of a
    /// first chunk that fills a partial last chunk there.
    // PERF: a bind thread does the id remap (`f`) and the moves here, so
    // the loading thread only appends chunks (`SymbolArena::append_file_arena`).
    pub fn into_aligned(
        self,
        skip: usize,
        at: usize,
        mut f: impl FnMut(&mut T),
    ) -> AlignedChunks<T> {
        let len = self.len.saturating_sub(skip);
        let mut parts: Vec<Vec<T>> = Vec::with_capacity(len.div_ceil(COW_CHUNK_LEN) + 1);
        // The part being filled, the room left in it, and the values left.
        let mut room = COW_CHUNK_LEN - (at & COW_CHUNK_MASK);
        let mut left = len;
        let mut part: Vec<T> = Vec::with_capacity(if left == 0 {
            0
        } else if room < COW_CHUNK_LEN {
            // It fills the partial chunk at `at` and is emptied there.
            room.min(left)
        } else {
            COW_CHUNK_LEN
        });
        let mut skip = skip;
        for chunk in self.chunks {
            let mut values = chunk.into_values();
            if skip >= values.len() {
                skip -= values.len();
                continue;
            }
            let start = std::mem::take(&mut skip);
            for value in &mut values[start..] {
                f(value);
            }
            let mut moved = values.drain(start..);
            while moved.len() > 0 {
                let count = room.min(moved.len());
                part.extend(moved.by_ref().take(count));
                room -= count;
                left -= count;
                if room == 0 {
                    let next = Vec::with_capacity(if left == 0 { 0 } else { COW_CHUNK_LEN });
                    parts.push(std::mem::replace(&mut part, next));
                    room = COW_CHUNK_LEN;
                }
            }
        }
        debug_assert_eq!(left, 0, "aligned chunk count");
        if !part.is_empty() {
            parts.push(part);
        }
        AlignedChunks { at, len, parts }
    }

    /// Appends the values of `aligned`, which `into_aligned` made for the
    /// current length.
    pub fn append_aligned(&mut self, aligned: AlignedChunks<T>) {
        assert_eq!(
            self.len, aligned.at,
            "aligned chunks made for another index"
        );
        let mut parts = aligned.parts.into_iter();
        if self.len & COW_CHUNK_MASK != 0 {
            if let Some(mut first) = parts.next() {
                self.chunks
                    .last_mut()
                    .expect("cow chunk")
                    .owned()
                    .append(&mut first);
            }
        }
        self.chunks.extend(parts.map(Chunk::Owned));
        self.len += aligned.len;
    }
}

/// Values moved out of a `CowChunks` for `CowChunks::append_aligned` at
/// index `at`. Each part ends at a chunk end of the target, except the last.
#[derive(Debug)]
pub struct AlignedChunks<T> {
    at: usize,
    len: usize,
    parts: Vec<Vec<T>>,
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

/// The table hash of `name`. `Name::table_hash` gives the same value
/// without hashing.
#[inline]
fn table_hash(name: &str) -> u32 {
    fold_hash(intern::hash_str(name))
}

/// Folds an `intern::hash_str` hash to the 32-bit table hash.
#[inline]
fn fold_hash(hash: u64) -> u32 {
    (hash ^ (hash >> 32)) as u32
}

thread_local! {
    /// (address, length, table hash) of the text of the innermost
    /// `with_text_hash` call on this thread. Zeros when there is none: a
    /// `str` address is never 0.
    static TEXT_HASH: std::cell::Cell<(usize, usize, u32)> =
        const { std::cell::Cell::new((0, 0, 0)) };
}

/// Runs `f`. While it runs, `SymbolArena::get` reuses one hash of `text`
/// for lookups of this same `text` (same address and length). It is for
/// code that looks one text up in many tables through APIs that take
/// `&str`, such as `NameResolver::resolve` (one table per scope, through a
/// lookup callback).
///
/// This is exact: `text` stays borrowed until `f` returns, so any `str` with
/// the same address and length that is alive during `f` has the same bytes.
/// Calls nest; each one restores the outer text when it returns or unwinds.
pub fn with_text_hash<R>(text: &str, f: impl FnOnce() -> R) -> R {
    struct Restore((usize, usize, u32));
    impl Drop for Restore {
        fn drop(&mut self) {
            TEXT_HASH.set(self.0);
        }
    }
    let entry = (text.as_ptr().addr(), text.len(), table_hash(text));
    let _restore = Restore(TEXT_HASH.replace(entry));
    f()
}

/// The table hash of `text`, from the innermost `with_text_hash` when it
/// covers this exact text.
#[inline]
fn lookup_hash(text: &str) -> u32 {
    let (address, len, hash) = TEXT_HASH.get();
    if address == text.as_ptr().addr() && len == text.len() {
        hash
    } else {
        table_hash(text)
    }
}

/// A symbol table key for code that is called with either a `&Name` or a
/// `&str`. A `Name` finds its entry by id with the hash the interner keeps,
/// so it needs no hashing and no text compare.
#[derive(Clone, Copy, Debug)]
pub enum TableKey<'a> {
    Text(&'a str),
    Name(&'a Name),
}

impl<'a> TableKey<'a> {
    /// The key text.
    #[must_use]
    pub fn text(self) -> &'a str {
        match self {
            TableKey::Text(text) => text,
            TableKey::Name(name) => name.as_str(),
        }
    }
}

impl<'a> From<&'a str> for TableKey<'a> {
    fn from(text: &'a str) -> Self {
        TableKey::Text(text)
    }
}

impl<'a> From<&'a Name> for TableKey<'a> {
    fn from(name: &'a Name) -> Self {
        TableKey::Name(name)
    }
}

impl Table {
    fn with_capacity(capacity: usize) -> Self {
        Table {
            entries: Vec::with_capacity(capacity),
            // PERF: a table sized past `TABLE_LINEAR_MAX` gets its index now,
            // so filling it never reindexes. The index is lookup only.
            index: Self::empty_index(capacity),
        }
    }

    /// An empty index for `len` entries, or no index when a table of that
    /// size is searched linearly.
    fn empty_index(len: usize) -> Box<[u16]> {
        if len <= TABLE_LINEAR_MAX {
            return Box::default();
        }
        vec![0u16; (len * 2).next_power_of_two()].into_boxed_slice()
    }

    /// True when `additional` more entries fit without growing the entries
    /// or rebuilding the index.
    fn has_room(&self, additional: usize) -> bool {
        let len = self.entries.len() + additional;
        self.entries.capacity() >= len && (len <= TABLE_LINEAR_MAX || self.index.len() >= len * 2)
    }

    /// Makes room for `additional` more entries (see `has_room`). Entry
    /// order does not change.
    fn reserve(&mut self, additional: usize) {
        self.entries.reserve(additional);
        let len = self.entries.len() + additional;
        if len > TABLE_LINEAR_MAX && self.index.len() < len * 2 {
            let mut index = Self::empty_index(len);
            for (position, entry) in self.entries.iter().enumerate() {
                Self::index_insert(&mut index, entry.hash, position);
            }
            self.index = index;
        }
    }

    /// The position of `name`, whose `table_hash` is `hash`.
    #[inline]
    fn find(&self, hash: u32, name: &str) -> Option<usize> {
        self.find_by(hash, |e| intern::text(e.name) == name)
    }

    /// The position of name id `id`, whose `table_hash` is `hash`. Equal
    /// texts intern to one id, so the ids compare.
    #[inline]
    fn find_id(&self, hash: u32, id: u32) -> Option<usize> {
        self.find_by(hash, |e| e.name == id)
    }

    /// The position of the entry with hash `hash` that `is_name` accepts.
    #[inline]
    fn find_by(&self, hash: u32, is_name: impl Fn(&TableEntry) -> bool) -> Option<usize> {
        if self.index.is_empty() {
            return self
                .entries
                .iter()
                .position(|e| e.hash == hash && is_name(e));
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
                if entry.hash == hash && is_name(entry) {
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
        let mut index = Self::empty_index(self.entries.len());
        if !index.is_empty() {
            for (position, entry) in self.entries.iter().enumerate() {
                Self::index_insert(&mut index, entry.hash, position);
            }
        }
        self.index = index;
    }

    /// Go `table[name] = symbol`. A new name goes last, like `IndexMap`.
    fn insert(&mut self, name: &Name, symbol: SymbolId) {
        let hash = name.table_hash();
        match self.find_id(hash, name.0) {
            Some(position) => self.entries[position].symbol = symbol,
            None => self.push(hash, name.0, symbol),
        }
    }

    /// Appends an entry for name id `name`, which is not in the table.
    fn push(&mut self, hash: u32, name: u32, symbol: SymbolId) {
        self.entries.push(TableEntry { hash, name, symbol });
        let len = self.entries.len();
        // A table can have an index before it passes `TABLE_LINEAR_MAX`
        // (`with_capacity`, `reserve`). Every entry of an indexed table is in
        // the index.
        if self.index.len() >= len * 2 {
            Self::index_insert(&mut self.index, hash, len - 1);
        } else if len > TABLE_LINEAR_MAX {
            self.reindex();
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
/// checker starts from a copy (`for_checker`), so binder ids stay valid and
/// checker (transient) symbols stay private to that checker. The copy shares
/// the binder's symbol and table chunks; a checker copies a chunk only when
/// it first writes to it. The binder writes without atomic operations and
/// then shares what it wrote (`share_since`), so the copy copies nothing.
#[derive(Clone, Debug)]
pub struct SymbolArena {
    symbols: CowChunks<Symbol>,
    tables: CowChunks<Table>,
    /// The names that the binder gave private identifier symbols
    /// (`get_symbol_name_for_private_identifier`), as intern ids. Each holds
    /// a symbol id, which `prepare_file_arena` moves.
    private_names: Vec<u32>,
    /// Where `crate::ast::get_symbol_id` keeps the ids of these symbols.
    ids: SymbolIds,
}

/// Where `crate::ast::get_symbol_id` keeps the ids of the symbols of one
/// arena. Every binder arena of the process (the binder lineage in
/// `program.rs` and its copies) gives a symbol one id, like Go, where a
/// bound file keeps its symbols in every program. A checker arena
/// (`SymbolArena::for_checker`) adds its own symbols after the binder
/// symbols, at indexes where other checkers and later binds put other
/// symbols, so those symbols have ids of their own, kept by `key`.
#[derive(Debug)]
struct SymbolIds {
    /// Symbols below this index have the shared id of their index.
    shared: u32,
    /// Keys the ids of the other symbols. 0 when every symbol is shared.
    key: u32,
}

impl SymbolIds {
    /// Every symbol has the shared id of its index.
    const SHARED: SymbolIds = SymbolIds {
        shared: u32::MAX,
        key: 0,
    };

    /// Symbols from index `shared` on have ids of their own.
    fn own_from(shared: usize) -> SymbolIds {
        static NEXT_KEY: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(1);
        SymbolIds {
            shared: u32::try_from(shared).expect("symbol overflow"),
            key: NEXT_KEY.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        }
    }
}

impl Clone for SymbolIds {
    /// A copy of a checker arena holds copies of its own symbols, which are
    /// other symbols, so they get new ids.
    fn clone(&self) -> Self {
        if self.key == 0 {
            SymbolIds::SHARED
        } else {
            SymbolIds::own_from(self.shared as usize)
        }
    }
}

impl Drop for SymbolIds {
    /// Frees this thread's ids of the arena's own symbols.
    fn drop(&mut self) {
        if self.key != 0 {
            crate::ast::forget_own_symbol_ids(self.key);
        }
    }
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
        Self {
            symbols,
            tables,
            private_names: Vec::new(),
            ids: SymbolIds::SHARED,
        }
    }

    /// A copy of this binder arena for a checker (Go `NewChecker` reads the
    /// bound program). The symbols that the checker adds have ids of their
    /// own (`crate::ast::get_symbol_id`), so checkers of any program can
    /// share a thread.
    #[must_use]
    pub fn for_checker(&self) -> SymbolArena {
        debug_assert!(
            self.ids.key == 0,
            "a checker arena is made from a binder arena"
        );
        SymbolArena {
            symbols: self.symbols.clone(),
            tables: self.tables.clone(),
            private_names: self.private_names.clone(),
            ids: SymbolIds::own_from(self.symbols.len()),
        }
    }

    /// Where `crate::ast::get_symbol_id` keeps the id of `symbol`: None when
    /// every arena shares it (a binder symbol), else the key of this arena's
    /// own ids and the place of `symbol` among the symbols that have them.
    #[inline]
    #[must_use]
    pub fn own_symbol_id_slot(&self, symbol: SymbolId) -> Option<(u32, usize)> {
        let shared = self.ids.shared as usize;
        let index = symbol.index();
        (index >= shared).then(|| (self.ids.key, index - shared))
    }

    /// The number of symbols, with the nil symbol at index 0.
    #[must_use]
    pub fn symbol_count(&self) -> usize {
        self.symbols.len()
    }

    /// Notes that the binder gave `name` to a private identifier symbol
    /// (`get_symbol_name_for_private_identifier`), so the name holds a
    /// symbol id.
    pub fn note_private_name(&mut self, name: &Name) {
        self.private_names.push(name.0);
    }

    /// The current symbol and table counts, for `share_since`.
    #[must_use]
    pub fn mark(&self) -> ArenaMark {
        ArenaMark {
            symbols: self.symbols.len(),
            tables: self.tables.len(),
        }
    }

    /// Shares the symbols and tables added since `mark` with future clones.
    /// Call it after binding, before the arena is cloned.
    pub fn share_since(&mut self, mark: ArenaMark) {
        self.symbols.share_from(mark.symbols);
        self.tables.share_from(mark.tables);
    }

    /// Go `&ast.Symbol{Flags: flags, Name: name}`.
    pub fn new_symbol(&mut self, flags: SymbolFlags, name: impl Into<Name>) -> SymbolId {
        self.push_symbol(Symbol {
            flags,
            name: name.into(),
            ..Symbol::default()
        })
    }

    /// Pushes a complete symbol and returns its id. Use it instead of
    /// `new_symbol` plus `sym_mut` writes when every field is known.
    pub fn push_symbol(&mut self, symbol: Symbol) -> SymbolId {
        let id = SymbolId(u32::try_from(self.symbols.len()).expect("symbol overflow"));
        self.symbols.push(symbol);
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

    /// Makes room for `additional` more entries in `table`, so the inserts
    /// that follow do not grow it or rebuild its index. Entry order and
    /// lookups do not change. A nil table stays nil. A table that has room
    /// is not written, so a shared chunk is not taken back.
    pub fn reserve(&mut self, table: SymbolTable, additional: usize) {
        if table.is_nil() || self.tables.get(table.index()).has_room(additional) {
            return;
        }
        self.tables.get_mut(table.index()).reserve(additional);
    }

    /// Go `table[name]`, plus the slot of `name` in `table`, so that
    /// `set_slot` stores it without a second lookup. The table must not
    /// change between the two calls. A nil table reads as empty.
    #[must_use]
    pub fn get_slot(&self, table: SymbolTable, name: &Name) -> (SymbolId, TableSlot) {
        let hash = name.table_hash();
        let mut found = (SymbolId::NIL, None);
        if table.is_some() {
            let current = self.tables.get(table.index());
            if let Some(position) = current.find_id(hash, name.0) {
                found = (current.entries[position].symbol, Some(position));
            }
        }
        let slot = TableSlot {
            table,
            hash,
            name: name.0,
            position: found.1,
        };
        (found.0, slot)
    }

    /// Go `table[name] = symbol` for the `table` and `name` of `slot`
    /// (`get_slot`). Panics on a nil table, like Go.
    pub fn set_slot(&mut self, slot: TableSlot, symbol: SymbolId) {
        assert!(slot.table.is_some(), "assignment to entry in nil map");
        let current = self.tables.get_mut(slot.table.index());
        match slot.position {
            Some(position) => current.entries[position].symbol = symbol,
            None => {
                debug_assert!(
                    current.find_id(slot.hash, slot.name).is_none(),
                    "table changed after get_slot"
                );
                current.push(slot.hash, slot.name, symbol);
            }
        }
    }

    /// The id offsets that a file arena appended now gets
    /// (`append_file_arena`): every id moves by the number of entries already
    /// here.
    #[must_use]
    pub fn next_file_offsets(&self) -> ArenaOffsets {
        ArenaOffsets {
            symbols: u32::try_from(self.symbols.len() - 1).expect("symbol overflow"),
            tables: u32::try_from(self.tables.len() - 1).expect("table overflow"),
        }
    }

    /// Appends the symbols and tables of `file_arena`, an arena that one
    /// file was bound into on its own, and returns how its ids moved. The
    /// ids get the values that binding the file into this arena would give:
    /// every id moves by the number of entries already here.
    pub fn append_file_arena(&mut self, file_arena: SymbolArena) -> ArenaOffsets {
        let offsets = self.next_file_offsets();
        self.append_prepared_file_arena(file_arena.prepare_file_arena(offsets))
    }

    /// Moves every id in this file arena by `offsets`, in place, and puts
    /// the entries in chunks for `append_prepared_file_arena` with the same
    /// offsets. It can run on another thread once the offsets are known.
    // PORT: the binder writes a symbol id into the names of private
    // identifier symbols (`get_symbol_name_for_private_identifier`), so those
    // names move with the ids. Source text can spell a name of the same form
    // (the byte 0xFE + "#1@#p", see `ast::INTERNAL_SYMBOL_NAME_PREFIX`). Go
    // keeps such a name as written, so only a symbol that a private
    // identifier declares moves, with its entries in the tables. Go gives
    // symbol ids in a different order, so a source name that is equal to a
    // private identifier name in Go is not always equal to it here.
    // PERF: the entries are changed in place and moved by chunk. Rebuilding
    // each symbol in an iterator chain was most of the join time.
    #[must_use]
    pub fn prepare_file_arena(self, offsets: ArenaOffsets) -> PreparedFileArena {
        let SymbolArena {
            symbols,
            tables,
            private_names,
            ids: _,
        } = self;
        // The file symbols whose names hold a symbol id.
        let mut private_symbols = FxHashSet::default();
        if offsets.symbols != 0 && !private_names.is_empty() {
            let private_names: FxHashSet<u32> = private_names.into_iter().collect();
            for i in 1..symbols.len() {
                let symbol = symbols.get(i);
                if private_names.contains(&symbol.name.0)
                    && symbol.declarations.iter().any(|&declaration| {
                        crate::ast::is_private_identifier(crate::ast::get_name_of_declaration(
                            declaration,
                        ))
                    })
                {
                    private_symbols.insert(i as u32);
                }
            }
        }
        // `into_aligned` visits the symbols in order from index 1.
        let mut index = 0u32;
        let symbols = symbols.into_aligned(1, offsets.symbols as usize + 1, |symbol| {
            index += 1;
            if private_symbols.contains(&index) {
                symbol.name = offsets.private_name(&symbol.name);
            }
            symbol.members = offsets.table(symbol.members);
            symbol.exports = offsets.table(symbol.exports);
            symbol.parent = offsets.symbol(symbol.parent);
            symbol.export_symbol = offsets.symbol(symbol.export_symbol);
        });
        let tables = tables.into_aligned(1, offsets.tables as usize + 1, |table| {
            let mut renamed = false;
            for entry in &mut table.entries {
                if private_symbols.contains(&entry.symbol.0) {
                    let name = offsets.private_name(&Name(entry.name));
                    if name.0 != entry.name {
                        renamed = true;
                        entry.name = name.0;
                        entry.hash = name.table_hash();
                    }
                }
                entry.symbol = offsets.symbol(entry.symbol);
            }
            if renamed {
                table.reindex();
            }
        });
        PreparedFileArena {
            symbols,
            tables,
            offsets,
        }
    }

    /// Appends a file arena that `prepare_file_arena` prepared with the
    /// offsets that `next_file_offsets` gives now, and returns them.
    pub fn append_prepared_file_arena(&mut self, prepared: PreparedFileArena) -> ArenaOffsets {
        let offsets = self.next_file_offsets();
        assert_eq!(
            offsets, prepared.offsets,
            "file arena prepared for other offsets"
        );
        let mark = self.mark();
        // The entries were moved on the bind thread; their buffers stay in
        // use here.
        self.symbols.append_aligned(prepared.symbols);
        self.tables.append_aligned(prepared.tables);
        self.share_since(mark);
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

    #[inline(always)]
    #[must_use]
    pub fn sym(&self, symbol: SymbolId) -> &Symbol {
        debug_assert!(symbol.is_some(), "nil symbol dereference");
        self.symbols.get(symbol.index())
    }

    #[inline]
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
            .find(lookup_hash(name), name)
            .map_or(SymbolId::NIL, |position| table.entries[position].symbol)
    }

    /// Go `table[name]` for a caller that has a `Name`. It compares ids
    /// instead of texts, with the hash the interner keeps.
    #[must_use]
    pub fn get_name(&self, table: SymbolTable, name: &Name) -> SymbolId {
        if table.is_nil() {
            return SymbolId::NIL;
        }
        let table = self.tables.get(table.index());
        if table.entries.is_empty() {
            return SymbolId::NIL;
        }
        table
            .find_id(name.table_hash(), name.0)
            .map_or(SymbolId::NIL, |position| table.entries[position].symbol)
    }

    /// Go `table[name]` by `get` or `get_name`, whichever `key` holds.
    #[inline]
    #[must_use]
    pub fn get_key(&self, table: SymbolTable, key: TableKey<'_>) -> SymbolId {
        match key {
            TableKey::Text(text) => self.get(table, text),
            TableKey::Name(name) => self.get_name(table, name),
        }
    }

    /// Go `table[name] = symbol`. Panics on a nil table, like Go.
    pub fn set(&mut self, table: SymbolTable, name: impl Into<Name>, symbol: SymbolId) {
        assert!(table.is_some(), "assignment to entry in nil map");
        let name = name.into();
        self.tables.get_mut(table.index()).insert(&name, symbol);
    }

    /// Go `if table[name] == nil { table[name] = symbol }` with one lookup.
    /// Returns true when it stored `symbol`. Panics on a nil table, like Go.
    pub fn set_if_absent(&mut self, table: SymbolTable, name: &Name, symbol: SymbolId) -> bool {
        self.set_if_absent_or(table, name, symbol, |_| false)
    }

    /// Like `set_if_absent`, but it also replaces a stored symbol that
    /// `replace` accepts: Go
    /// `if s := table[name]; s == nil || replace(s) { table[name] = symbol }`.
    /// One lookup. A replaced entry keeps its position.
    pub fn set_if_absent_or(
        &mut self,
        table: SymbolTable,
        name: &Name,
        symbol: SymbolId,
        replace: impl FnOnce(&Symbol) -> bool,
    ) -> bool {
        assert!(table.is_some(), "assignment to entry in nil map");
        let hash = name.table_hash();
        let found = {
            let current = self.tables.get(table.index());
            current
                .find_id(hash, name.0)
                .map(|position| (position, current.entries[position].symbol))
        };
        if let Some((_, old)) = found {
            if old.is_some() && !replace(self.sym(old)) {
                return false;
            }
        }
        // Only a write takes a shared table chunk back, like `set`.
        let current = self.tables.get_mut(table.index());
        match found {
            Some((position, _)) => current.entries[position].symbol = symbol,
            None => current.push(hash, name.0, symbol),
        }
        true
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

/// Where a name is, or goes, in one symbol table (`SymbolArena::get_slot`).
#[derive(Clone, Copy, Debug)]
pub struct TableSlot {
    table: SymbolTable,
    hash: u32,
    name: u32,
    position: Option<usize>,
}

/// Symbol and table counts of a `SymbolArena` at one point
/// (`SymbolArena::mark`).
#[derive(Clone, Copy, Debug)]
pub struct ArenaMark {
    symbols: usize,
    tables: usize,
}

/// Prefix of private identifier symbol names (`<prefix>#<id>@<description>`):
/// `ast::INTERNAL_SYMBOL_NAME_PREFIX` + "#".
const PRIVATE_PREFIX: &str = "\u{FDD0}\u{10F7FE}#";

/// A file arena with its ids moved to program ids
/// (`SymbolArena::prepare_file_arena`).
#[derive(Debug)]
pub struct PreparedFileArena {
    symbols: AlignedChunks<Symbol>,
    tables: AlignedChunks<Table>,
    offsets: ArenaOffsets,
}

/// How the ids of a file arena moved in `SymbolArena::append_file_arena`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArenaOffsets {
    symbols: u32,
    tables: u32,
}

impl ArenaOffsets {
    /// The offsets of the file after a file with these offsets, where
    /// `file_arena` is the `SymbolArena::mark` of that file's own arena.
    /// Parallel binding adds the counts of the earlier files this way.
    #[must_use]
    pub fn after(self, file_arena: ArenaMark) -> ArenaOffsets {
        let count = |len: usize| u32::try_from(len - 1).expect("arena overflow");
        ArenaOffsets {
            symbols: self
                .symbols
                .checked_add(count(file_arena.symbols))
                .expect("symbol overflow"),
            tables: self
                .tables
                .checked_add(count(file_arena.tables))
                .expect("table overflow"),
        }
    }

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

    /// The private identifier name `name` (`<prefix>#<id>@<description>`,
    /// see `SymbolArena::note_private_name`) with its symbol id moved.
    #[cold]
    fn private_name(self, name: &Name) -> Name {
        let Some(rest) = name.strip_prefix(PRIVATE_PREFIX) else {
            return name.clone();
        };
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
    /// Compacts the per-node data of a bound file, given in node order.
    #[must_use]
    pub fn new<'a>(nodes: impl ExactSizeIterator<Item = &'a NodeBindData>) -> Self {
        let mut slots = Vec::with_capacity(nodes.len());
        let mut bases = Vec::with_capacity(nodes.len().div_ceil(NODE_BIND_BLOCK));
        let mut entries: Vec<NodeBindData> = Vec::new();
        let mut block_start = 0;
        for (index, data) in nodes.enumerate() {
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
    // PORT: Go also keeps `ClassifiableNames` here. Nothing reads it, so the
    // binder does not collect it.
    pub pattern_ambient_modules: Vec<PatternAmbientModule>,
    pub global_exports: SymbolTable,
    /// Go `JSGlobalAugmentations`.
    pub js_global_augmentations: SymbolTable,
    /// Go `SourceFile.CommonJSModuleIndicator` (set by the binder).
    pub common_js_module_indicator: Node,
    /// Rust-only: the binder gave an expando assignment (Go
    /// `bindDeferredExpandoAssignment`) a symbol. When false, no node of the
    /// file has an `ASSIGNMENT` symbol, so the declaration transformer skips
    /// its expando walk (`transform_source_file`).
    pub has_expando_assignments: bool,
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
    /// Go `repopulateInfo`: lets an incremental build recompute a module
    /// resolution diagnostic chain. `Arc` because diagnostics cross the
    /// checker threads.
    pub repopulate_info: Option<std::sync::Arc<crate::ast::RepopulateDiagnosticInfo>>,
}

/// Go `...any` diagnostic arguments. Go formats each with `%v`; we use
/// `ToString`. Example: `args![self.type_to_string(t), count]`.
#[macro_export]
macro_rules! args {
    ($($arg:expr),* $(,)?) => { vec![$(::std::string::ToString::to_string(&$arg)),*] };
}

/// Where a `LinkStore` keeps the record of a key.
#[derive(Clone, Copy, Debug)]
pub enum LinkSlot {
    /// An arena handle (`TypeId`, `SymbolId`, ...): an index into one page
    /// table for the whole arena.
    Arena(usize),
    /// A node or flow node handle: (file, local index + 1). Each file has
    /// its own page table.
    File(usize, usize),
    /// Any other key (a synthetic node): the hash map.
    Map,
}

/// A `LinkStore` key. Arena handles are dense small indexes, and node and
/// flow node handles are dense small indexes within a file, so their links
/// live in paged slot arrays instead of a hash map.
pub trait LinkKey: Copy + Eq + std::hash::Hash {
    /// Where the record of this key lives.
    fn link_slot(self) -> LinkSlot;
}

macro_rules! arena_link_key {
    ($($name:ident),*) => {$(
        impl LinkKey for $name {
            #[inline]
            fn link_slot(self) -> LinkSlot {
                LinkSlot::Arena(self.index())
            }
        }
    )*};
}

arena_link_key!(
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
const LINK_MAX_FILES: u64 = 1 << 20;

/// The slot of a (file << 32 | local + 1) handle.
#[inline]
fn file_link_slot(handle: u64) -> LinkSlot {
    let file = handle >> 32;
    if file < LINK_MAX_FILES {
        LinkSlot::File(file as usize, (handle & 0xffff_ffff) as usize)
    } else {
        LinkSlot::Map
    }
}

impl LinkKey for Node {
    #[inline]
    fn link_slot(self) -> LinkSlot {
        file_link_slot(self.0)
    }
}

impl LinkKey for FlowNodeId {
    #[inline]
    fn link_slot(self) -> LinkSlot {
        file_link_slot(self.0)
    }
}

/// Slots per page for arena keys. Pages are allocated on first use, so a
/// store that few keys use stays small. Larger pages make the page table
/// smaller, but cost memory in sparse stores (check query peak RSS).
const ARENA_PAGE_SIZE: usize = 1 << 6;
/// Slots per page for file keys. Small pages keep sparse stores small.
const FILE_PAGE_SIZE: usize = 1 << 6;

/// A page table: pages of `N` slots, allocated on first use. A slot holds
/// the value index + 1; zero is absent.
type SlotPages<const N: usize> = Vec<Option<Box<[u32; N]>>>;

/// The slot of `index` in `pages`, or zero when its page is absent.
#[inline]
fn page_slot<const N: usize>(pages: &[Option<Box<[u32; N]>>], index: usize) -> u32 {
    match pages.get(index / N) {
        Some(Some(page)) => page[index % N],
        _ => 0,
    }
}

/// The slot of `index` in `pages`. Adds the page if it is absent.
fn page_slot_mut<const N: usize>(pages: &mut SlotPages<N>, index: usize) -> &mut u32 {
    let page = index / N;
    if page >= pages.len() {
        pages.resize_with(page + 1, || None);
    }
    &mut pages[page].get_or_insert_with(|| Box::new([0; N]))[index % N]
}

/// Go `core.LinkStore[K, V]`: lazily created per-key link records.
/// Dense keys map through paged slots into `values`. Other keys use a hash
/// map. `get` reads an existing record inline and adds a new one out of line.
#[derive(Clone, Debug)]
pub struct LinkStore<K: LinkKey, V: Default> {
    /// Slot pages of arena keys. One flat table, so a hit reads the page
    /// pointer, the slot and the value, with no per-group hop.
    arena: SlotPages<ARENA_PAGE_SIZE>,
    /// Slot pages of file keys, by file.
    files: Vec<SlotPages<FILE_PAGE_SIZE>>,
    /// Dense values in fixed-size chunks, so growth never copies or
    /// over-allocates a large block.
    values: Vec<Vec<V>>,
    len: usize,
    map: FxHashMap<K, V>,
}

/// Values per chunk of a dense `LinkStore`.
const LINK_CHUNK_SIZE: usize = 1 << 12;

impl<K: LinkKey, V: Default> Default for LinkStore<K, V> {
    fn default() -> Self {
        Self {
            arena: Vec::new(),
            files: Vec::new(),
            values: Vec::new(),
            len: 0,
            map: FxHashMap::default(),
        }
    }
}

impl<K: LinkKey, V: Default> LinkStore<K, V> {
    /// The value index of a key with slots, if it has a record.
    #[inline]
    fn slot_value(&self, slot: LinkSlot) -> Option<usize> {
        let stored = match slot {
            LinkSlot::Arena(index) => page_slot(&self.arena, index),
            LinkSlot::File(file, index) => self
                .files
                .get(file)
                .map_or(0, |pages| page_slot(pages, index)),
            LinkSlot::Map => 0,
        };
        (stored as usize).checked_sub(1)
    }

    #[inline]
    fn value(&self, value: usize) -> &V {
        &self.values[value / LINK_CHUNK_SIZE][value % LINK_CHUNK_SIZE]
    }

    /// Go `store.Get(key)`: creates the record on first use.
    #[inline]
    pub fn get(&mut self, key: K) -> &mut V {
        let slot = key.link_slot();
        if matches!(slot, LinkSlot::Map) {
            return self.map_get(key);
        }
        let value = match self.slot_value(slot) {
            Some(value) => value,
            None => self.create(slot),
        };
        &mut self.values[value / LINK_CHUNK_SIZE][value % LINK_CHUNK_SIZE]
    }

    #[cold]
    #[inline(never)]
    fn map_get(&mut self, key: K) -> &mut V {
        self.map.entry(key).or_default()
    }

    /// Adds the record of a key with slots, which has none, and returns its
    /// value index. Records get value indexes in creation order.
    #[cold]
    #[inline(never)]
    fn create(&mut self, slot: LinkSlot) -> usize {
        let stored = match slot {
            LinkSlot::Arena(index) => page_slot_mut(&mut self.arena, index),
            LinkSlot::File(file, index) => {
                if file >= self.files.len() {
                    self.files.resize_with(file + 1, Vec::new);
                }
                page_slot_mut(&mut self.files[file], index)
            }
            LinkSlot::Map => unreachable!("map keys have no slot"),
        };
        if self.len % LINK_CHUNK_SIZE == 0 {
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
        let value = self.len;
        self.len += 1;
        *stored = u32::try_from(self.len).expect("link store overflow");
        value
    }

    /// Go `store.Has(key)`.
    #[must_use]
    pub fn has(&self, key: K) -> bool {
        match key.link_slot() {
            LinkSlot::Map => self.map.contains_key(&key),
            slot => self.slot_value(slot).is_some(),
        }
    }

    /// Go `store.TryGet(key)`.
    #[must_use]
    pub fn try_get(&self, key: K) -> Option<&V> {
        match key.link_slot() {
            LinkSlot::Map => self.map.get(&key),
            slot => self.slot_value(slot).map(|value| self.value(value)),
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

/// The panic payload of `go_panic`.
pub struct GoPanic {
    /// The Go panic value as the Go runtime prints it (port form).
    pub message: String,
    /// The port site, for the stderr report.
    pub location: &'static std::panic::Location<'static>,
}

/// Go `panic(message)` at a site where the pinned Go panics on the same
/// input. It is not a port gap, so the run ends as the Go runtime ends it:
/// guards that keep a run going after a port gap pass it on
/// (`resume_go_panic`), and the bins write the output so far, print it with
/// `print_go_panic` and exit `EXIT_GO_PANIC`. Other panics stay port gaps
/// (`execute::tsc::EXIT_UNPORTED`).
#[track_caller]
pub fn go_panic(message: String) -> ! {
    std::panic::panic_any(GoPanic {
        message,
        location: std::panic::Location::caller(),
    })
}

/// The Go runtime exit code after a panic that nothing recovers.
pub const EXIT_GO_PANIC: i32 = 2;

/// Continues a caught `go_panic`. Returns any other payload.
pub fn resume_go_panic(payload: Box<dyn std::any::Any + Send>) -> Box<dyn std::any::Any + Send> {
    if payload.is::<GoPanic>() {
        std::panic::resume_unwind(payload);
    }
    payload
}

/// Prints a caught `go_panic` to stderr and returns true. The first line is
/// the Go runtime one (`panic: <message>`). The port site takes the place of
/// the goroutine trace. False for any other payload.
pub fn print_go_panic(payload: &(dyn std::any::Any + Send)) -> bool {
    let Some(panic) = payload.downcast_ref::<GoPanic>() else {
        return false;
    };
    let text = format!(
        "panic: {}\n\n\t{}:{}\n",
        panic.message,
        panic.location.file(),
        panic.location.line()
    );
    use std::io::Write;
    let _ = std::io::stderr().write_all(&crate::scanner_util::go_string_bytes(&text));
    true
}

/// One version of a loaded source file: one per file id. The file registry
/// (`ast/store.rs`) owns it from `publish_file_stores` on; read it with
/// `crate::ast::go_file`. Program versions that share a file version share
/// this value. Parser data is ready when the file is published. The binder
/// fills the `OnceLock` fields once per file version.
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

/// Go `Program` as the checker sees it: one per program version (Go makes a
/// new `Program` for each edit). Read the current one with `prog()`. Its
/// files live in the file registry (`crate::ast::go_file`), and versions
/// share the file versions they have in common.
pub struct GoProgram {
    /// Unique in the process, from `next_program_id`. It keys the checker
    /// pool and the frontend of the program on the loading thread.
    pub id: u32,
    /// The legacy graph. None on the Go frontend path.
    pub program: Option<&'static ts_compiler::Program>,
    /// File ids in Go `Program.SourceFiles()` order.
    pub source_file_order: Vec<usize>,
    pub options: crate::options::CompilerOptions,
    /// Binder symbols. Each checker clones this.
    pub bound_symbols: std::sync::OnceLock<SymbolArena>,
    /// Program state (`program::state()`). Set once, after the files are
    /// published.
    pub(crate) state: std::sync::OnceLock<&'static crate::program::ProgramState>,
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
    pub fn source_files(&self) -> impl Iterator<Item = &'static GoFile> {
        self.source_file_order
            .iter()
            .map(|&index| crate::ast::go_file(index))
    }
}

static NEXT_PROGRAM_ID: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(1);

/// A new `GoProgram::id`: 1 for the first program of the process, then 2, 3...
#[must_use]
pub fn next_program_id() -> u32 {
    NEXT_PROGRAM_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

thread_local! {
    /// The current program of this thread. Const init with no destructor,
    /// so `prog()` reads it with one thread-local load.
    static CURRENT: std::cell::Cell<Option<&'static GoProgram>> =
        const { std::cell::Cell::new(None) };
}

/// The program of a one-program process (`set_prog`). A thread with no
/// current program reads it. A multi-program process never sets it, so a
/// missed `enter_program` panics and does not read the wrong program.
static DEFAULT: std::sync::OnceLock<&'static GoProgram> = std::sync::OnceLock::new();

/// Set by `register_program_version`. Then `set_prog` panics.
static MULTI: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Installs the program of a one-program process and makes it current on
/// this thread. Call once. The caller publishes the files of the program
/// first (`crate::ast::publish_file_stores`).
pub fn set_prog(program: &'static GoProgram) {
    assert!(
        !MULTI.load(std::sync::atomic::Ordering::SeqCst),
        "set_prog in a multi-program process"
    );
    assert!(DEFAULT.set(program).is_ok(), "GoProgram already installed");
    CURRENT.set(Some(program));
}

/// Registers a program version of a multi-program process (watch, language
/// server, tests). It does not make `program` current; use `enter_program`.
pub fn register_program_version(program: &'static GoProgram) {
    MULTI.store(true, std::sync::atomic::Ordering::SeqCst);
    assert!(
        DEFAULT.get().is_none(),
        "program version {} registered in a one-program process",
        program.id
    );
}

/// Sets the current program of this thread with no restore. Only for thread
/// setup (`program::WorkerSeed` on checker and bind threads).
pub fn set_thread_program(program: Option<&'static GoProgram>) {
    CURRENT.set(program);
}

/// Makes `program` current on this thread until the scope drops. `None`
/// clears it, for example while the frontend parses a new version.
#[must_use = "the program is current only while the scope lives"]
pub fn enter_program(program: Option<&'static GoProgram>) -> ProgramScope {
    ProgramScope {
        previous: CURRENT.replace(program),
        _not_send: std::marker::PhantomData,
    }
}

/// From `enter_program`. On drop it restores the previous current program.
/// It is `!Send`, so it drops on the thread that made it.
pub struct ProgramScope {
    previous: Option<&'static GoProgram>,
    _not_send: std::marker::PhantomData<*const ()>,
}

impl Drop for ProgramScope {
    fn drop(&mut self) {
        CURRENT.set(self.previous);
    }
}

/// The current program of this thread, or `None`. The ported parser reads
/// nodes before the program exists.
#[inline]
#[must_use]
pub fn try_prog() -> Option<&'static GoProgram> {
    CURRENT.get().or_else(default_prog)
}

/// `try_prog` on a thread with no current program.
#[cold]
#[inline(never)]
fn default_prog() -> Option<&'static GoProgram> {
    DEFAULT.get().copied()
}

/// The current program of this thread. Go code reads nodes without a
/// context; this is how node accessors reach the AST.
#[inline]
#[must_use]
pub fn prog() -> &'static GoProgram {
    try_prog().expect("no current program; use core::enter_program")
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
