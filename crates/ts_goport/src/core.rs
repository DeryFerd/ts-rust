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
        if crate::ast::has_file_store(file) {
            return crate::ast::resolve_store_id(file, node);
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

/// A symbol name and symbol table key (Go `string`). Clones share one
/// allocation, so copying a name into a new symbol or table does not copy
/// the text. It compares, hashes and prints like the `str` it holds.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(Arc<str>);

impl Name {
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Default for Name {
    fn default() -> Self {
        Name(Arc::from(""))
    }
}

impl std::ops::Deref for Name {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl std::borrow::Borrow<str> for Name {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&*self.0, f)
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&*self.0, f)
    }
}

impl From<&str> for Name {
    fn from(s: &str) -> Self {
        Name(Arc::from(s))
    }
}

impl From<String> for Name {
    fn from(s: String) -> Self {
        Name(Arc::from(s))
    }
}

impl From<&String> for Name {
    fn from(s: &String) -> Self {
        Name(Arc::from(s.as_str()))
    }
}

impl From<&Name> for Name {
    fn from(s: &Name) -> Self {
        s.clone()
    }
}

impl From<Name> for String {
    fn from(s: Name) -> Self {
        s.0.to_string()
    }
}

impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool {
        *self.0 == *other
    }
}

impl PartialEq<&str> for Name {
    fn eq(&self, other: &&str) -> bool {
        *self.0 == **other
    }
}

impl PartialEq<String> for Name {
    fn eq(&self, other: &String) -> bool {
        *self.0 == **other
    }
}

impl PartialEq<Name> for str {
    fn eq(&self, other: &Name) -> bool {
        *self == *other.0
    }
}

impl PartialEq<Name> for &str {
    fn eq(&self, other: &Name) -> bool {
        **self == *other.0
    }
}

impl PartialEq<Name> for String {
    fn eq(&self, other: &Name) -> bool {
        **self == *other.0
    }
}

/// `Symbol::declarations` (Go `[]*ast.Node`). Clones share one `Vec`; the
/// first write through `DerefMut` copies it, so each symbol still owns its
/// own list, like a Go slice that is copied before an append. An empty list
/// allocates nothing.
#[derive(Clone, Default)]
pub struct Declarations(Option<Arc<Vec<Node>>>);

static NO_DECLARATIONS: Vec<Node> = Vec::new();

impl std::ops::Deref for Declarations {
    type Target = Vec<Node>;
    fn deref(&self) -> &Vec<Node> {
        self.0.as_deref().unwrap_or(&NO_DECLARATIONS)
    }
}

impl std::ops::DerefMut for Declarations {
    fn deref_mut(&mut self) -> &mut Vec<Node> {
        Arc::make_mut(self.0.get_or_insert_with(Arc::default))
    }
}

impl std::fmt::Debug for Declarations {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&**self, f)
    }
}

impl From<Vec<Node>> for Declarations {
    fn from(v: Vec<Node>) -> Self {
        Declarations(Some(Arc::new(v)))
    }
}

impl From<Declarations> for Vec<Node> {
    fn from(d: Declarations) -> Self {
        d.0.map(Arc::unwrap_or_clone).unwrap_or_default()
    }
}

impl IntoIterator for Declarations {
    type Item = Node;
    type IntoIter = std::vec::IntoIter<Node>;
    fn into_iter(self) -> Self::IntoIter {
        Vec::from(self).into_iter()
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
            self.chunks
                .push(Arc::new(Vec::with_capacity(COW_CHUNK_LEN)));
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

/// Owns all symbols and symbol tables. The binder fills one arena. Each
/// checker starts from a clone, so binder ids stay valid and checker
/// (transient) symbols stay private to that checker. The clone shares the
/// binder's symbol chunks and tables; a checker copies a chunk or table only
/// when it first writes to it.
#[derive(Clone, Debug)]
pub struct SymbolArena {
    symbols: CowChunks<Symbol>,
    tables: Vec<Arc<FxIndexMap<Name, SymbolId>>>,
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
        Self {
            symbols,
            tables: vec![Arc::default()],
        }
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

    /// Go `make(ast.SymbolTable)`.
    pub fn new_table(&mut self) -> SymbolTable {
        let id = SymbolTable(u32::try_from(self.tables.len()).expect("table overflow"));
        self.tables.push(Arc::default());
        id
    }

    /// Go `make(ast.SymbolTable, capacity)`.
    pub fn new_table_with_capacity(&mut self, capacity: usize) -> SymbolTable {
        let id = SymbolTable(u32::try_from(self.tables.len()).expect("table overflow"));
        self.tables
            .push(Arc::new(FxIndexMap::with_capacity_and_hasher(
                capacity,
                FxBuildHasher,
            )));
        id
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
        for i in 1..symbols.len() {
            let symbol = symbols.get(i);
            self.symbols.push(Symbol {
                flags: symbol.flags,
                check_flags: symbol.check_flags,
                name: offsets.name(&symbol.name),
                declarations: symbol.declarations.clone(),
                value_declaration: symbol.value_declaration,
                members: offsets.table(symbol.members),
                exports: offsets.table(symbol.exports),
                parent: offsets.symbol(symbol.parent),
                export_symbol: offsets.symbol(symbol.export_symbol),
            });
        }
        for table in tables.into_iter().skip(1) {
            let mut moved = FxIndexMap::with_capacity_and_hasher(table.len(), FxBuildHasher);
            for (name, &symbol) in table.iter() {
                moved.insert(offsets.name(name), offsets.symbol(symbol));
            }
            self.tables.push(Arc::new(moved));
        }
        offsets
    }

    /// Go `maps.Clone(table)`. A nil table clones to nil.
    pub fn clone_table(&mut self, table: SymbolTable) -> SymbolTable {
        if table.is_nil() {
            return SymbolTable::NIL;
        }
        let id = SymbolTable(u32::try_from(self.tables.len()).expect("table overflow"));
        let cloned = FxIndexMap::clone(&self.tables[table.index()]);
        self.tables.push(Arc::new(cloned));
        id
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
        self.tables[table.index()]
            .get(name)
            .copied()
            .unwrap_or_default()
    }

    /// Go `table[name] = symbol`. Panics on a nil table, like Go.
    pub fn set(&mut self, table: SymbolTable, name: impl Into<Name>, symbol: SymbolId) {
        assert!(table.is_some(), "assignment to entry in nil map");
        Arc::make_mut(&mut self.tables[table.index()]).insert(name.into(), symbol);
    }

    /// Go `delete(table, name)`.
    pub fn delete(&mut self, table: SymbolTable, name: &str) {
        if table.is_some() {
            Arc::make_mut(&mut self.tables[table.index()]).shift_remove(name);
        }
    }

    /// Go `len(table)`.
    #[must_use]
    pub fn len(&self, table: SymbolTable) -> usize {
        if table.is_nil() {
            0
        } else {
            self.tables[table.index()].len()
        }
    }

    /// Snapshot of `(name, symbol)` pairs in insertion order. Go map order is
    /// random, so Go code never depends on it; ours is deterministic.
    #[must_use]
    pub fn entries(&self, table: SymbolTable) -> Vec<(Name, SymbolId)> {
        if table.is_nil() {
            return Vec::new();
        }
        self.tables[table.index()]
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect()
    }

    /// Borrowed `(name, symbol)` pairs in insertion order. Use it instead of
    /// `entries` when the table does not change during the loop.
    pub fn iter(&self, table: SymbolTable) -> impl Iterator<Item = (&str, SymbolId)> {
        let map = if table.is_nil() {
            None
        } else {
            Some(&self.tables[table.index()])
        };
        map.into_iter()
            .flat_map(|map| map.iter().map(|(k, v)| (k.as_str(), *v)))
    }

    /// Snapshot of the values in insertion order.
    #[must_use]
    pub fn values(&self, table: SymbolTable) -> Vec<SymbolId> {
        if table.is_nil() {
            return Vec::new();
        }
        self.tables[table.index()].values().copied().collect()
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
#[derive(Clone, Copy, Debug, Default)]
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

/// Binder output for one source file. Go stores these on `ast.SourceFile`.
#[derive(Clone, Debug, Default)]
pub struct FileBindData {
    pub bind_diagnostics: Vec<Diagnostic>,
    pub bind_suggestion_diagnostics: Vec<Diagnostic>,
    pub end_flow_node: FlowNodeId,
    pub symbol_count: i32,
    pub classifiable_names: rustc_hash::FxHashSet<String>,
    pub pattern_ambient_modules: Vec<PatternAmbientModule>,
    pub global_exports: SymbolTable,
    /// Go `JSGlobalAugmentations`.
    pub js_global_augmentations: SymbolTable,
    /// Go `SourceFile.CommonJSModuleIndicator` (set by the binder).
    pub common_js_module_indicator: Node,
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

/// A `LinkStore` key. Arena handles are dense small indexes, so their
/// links live in paged slot arrays instead of a hash map.
pub trait LinkKey: Copy + Eq + std::hash::Hash {
    /// True when `dense_index` gives a small arena index.
    const DENSE: bool = false;

    fn dense_index(self) -> usize {
        0
    }
}

macro_rules! dense_link_key {
    ($($name:ident),*) => {$(
        impl LinkKey for $name {
            const DENSE: bool = true;

            fn dense_index(self) -> usize {
                self.index()
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

impl LinkKey for Node {}
impl LinkKey for FlowNodeId {}

/// Slots per page of a dense `LinkStore`. Pages keep sparse stores small.
const LINK_PAGE_BITS: usize = 9;
const LINK_PAGE_SIZE: usize = 1 << LINK_PAGE_BITS;

/// Go `core.LinkStore[K, V]`: lazily created per-key link records.
/// Dense keys map through paged slots (value index + 1, zero is absent) into
/// `values`. Other keys use a hash map.
#[derive(Clone, Debug)]
pub struct LinkStore<K: LinkKey, V: Default> {
    pages: Vec<Option<Box<[u32; LINK_PAGE_SIZE]>>>,
    values: Vec<V>,
    map: FxHashMap<K, V>,
}

impl<K: LinkKey, V: Default> Default for LinkStore<K, V> {
    fn default() -> Self {
        Self {
            pages: Vec::new(),
            values: Vec::new(),
            map: FxHashMap::default(),
        }
    }
}

impl<K: LinkKey, V: Default> LinkStore<K, V> {
    /// The value index for a dense key, if it has a record.
    fn dense_slot(&self, key: K) -> Option<usize> {
        let index = key.dense_index();
        let page = self.pages.get(index >> LINK_PAGE_BITS)?.as_ref()?;
        let slot = page[index & (LINK_PAGE_SIZE - 1)];
        (slot != 0).then(|| slot as usize - 1)
    }

    /// Go `store.Get(key)`: creates the record on first use.
    pub fn get(&mut self, key: K) -> &mut V {
        if !K::DENSE {
            return self.map.entry(key).or_default();
        }
        let index = key.dense_index();
        let page_index = index >> LINK_PAGE_BITS;
        if page_index >= self.pages.len() {
            self.pages.resize_with(page_index + 1, || None);
        }
        let page = self.pages[page_index].get_or_insert_with(|| Box::new([0; LINK_PAGE_SIZE]));
        let slot = &mut page[index & (LINK_PAGE_SIZE - 1)];
        if *slot == 0 {
            self.values.push(V::default());
            *slot = u32::try_from(self.values.len()).expect("link store overflow");
        }
        let value = *slot as usize - 1;
        &mut self.values[value]
    }

    /// Go `store.Has(key)`.
    #[must_use]
    pub fn has(&self, key: K) -> bool {
        if K::DENSE {
            self.dense_slot(key).is_some()
        } else {
            self.map.contains_key(&key)
        }
    }

    /// Go `store.TryGet(key)`.
    #[must_use]
    pub fn try_get(&self, key: K) -> Option<&V> {
        if K::DENSE {
            self.dense_slot(key).map(|value| &self.values[value])
        } else {
            self.map.get(&key)
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
    pub node_bind: std::sync::OnceLock<Vec<NodeBindData>>,
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
