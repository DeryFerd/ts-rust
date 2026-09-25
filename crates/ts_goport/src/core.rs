//! Shared handles and stores for the Go port. Read `PORTING.md` first.
//!
//! Every Go pointer to a shared object becomes a `Copy` handle. Handle value
//! zero is Go `nil`, so Go `x == nil` ports to `x.is_nil()`.

use indexmap::IndexMap;
use std::cell::Cell;

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

/// Go `*ast.Symbol`. Field names follow Go.
#[derive(Clone, Debug, Default)]
pub struct Symbol {
    pub flags: SymbolFlags,
    pub check_flags: CheckFlags,
    pub name: String,
    pub declarations: Vec<Node>,
    pub value_declaration: Node,
    pub members: SymbolTable,
    pub exports: SymbolTable,
    pub parent: SymbolId,
    pub export_symbol: SymbolId,
}

/// Owns all symbols and symbol tables. The binder fills one arena. Each
/// checker starts from a clone, so binder ids stay valid and checker
/// (transient) symbols stay private to that checker.
#[derive(Clone, Debug)]
pub struct SymbolArena {
    pub symbols: Vec<Symbol>,
    pub tables: Vec<IndexMap<String, SymbolId>>,
}

impl Default for SymbolArena {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolArena {
    #[must_use]
    pub fn new() -> Self {
        Self { symbols: vec![Symbol::default()], tables: vec![IndexMap::new()] }
    }

    /// Go `&ast.Symbol{Flags: flags, Name: name}`.
    pub fn new_symbol(&mut self, flags: SymbolFlags, name: impl Into<String>) -> SymbolId {
        let id = SymbolId(u32::try_from(self.symbols.len()).expect("symbol overflow"));
        self.symbols.push(Symbol { flags, name: name.into(), ..Symbol::default() });
        id
    }

    /// Go `make(ast.SymbolTable)`.
    pub fn new_table(&mut self) -> SymbolTable {
        let id = SymbolTable(u32::try_from(self.tables.len()).expect("table overflow"));
        self.tables.push(IndexMap::new());
        id
    }

    #[must_use]
    pub fn sym(&self, symbol: SymbolId) -> &Symbol {
        debug_assert!(symbol.is_some(), "nil symbol dereference");
        &self.symbols[symbol.index()]
    }

    pub fn sym_mut(&mut self, symbol: SymbolId) -> &mut Symbol {
        debug_assert!(symbol.is_some(), "nil symbol dereference");
        &mut self.symbols[symbol.index()]
    }

    /// Go `table[name]`. A nil table reads as empty.
    #[must_use]
    pub fn get(&self, table: SymbolTable, name: &str) -> SymbolId {
        if table.is_nil() {
            return SymbolId::NIL;
        }
        self.tables[table.index()].get(name).copied().unwrap_or_default()
    }

    /// Go `table[name] = symbol`. Panics on a nil table, like Go.
    pub fn set(&mut self, table: SymbolTable, name: impl Into<String>, symbol: SymbolId) {
        assert!(table.is_some(), "assignment to entry in nil map");
        self.tables[table.index()].insert(name.into(), symbol);
    }

    /// Go `delete(table, name)`.
    pub fn delete(&mut self, table: SymbolTable, name: &str) {
        if table.is_some() {
            self.tables[table.index()].shift_remove(name);
        }
    }

    /// Go `len(table)`.
    #[must_use]
    pub fn len(&self, table: SymbolTable) -> usize {
        if table.is_nil() { 0 } else { self.tables[table.index()].len() }
    }

    /// Snapshot of `(name, symbol)` pairs in insertion order. Go map order is
    /// random, so Go code never depends on it; ours is deterministic.
    #[must_use]
    pub fn entries(&self, table: SymbolTable) -> Vec<(String, SymbolId)> {
        if table.is_nil() {
            return Vec::new();
        }
        self.tables[table.index()].iter().map(|(k, v)| (k.clone(), *v)).collect()
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
}

/// Go `...any` diagnostic arguments. Go formats each with `%v`; we use
/// `ToString`. Example: `args![self.type_to_string(t), count]`.
#[macro_export]
macro_rules! args {
    ($($arg:expr),* $(,)?) => { vec![$(::std::string::ToString::to_string(&$arg)),*] };
}

/// Go `core.LinkStore[K, V]`: lazily created per-key link records.
#[derive(Clone, Debug)]
pub struct LinkStore<K: std::hash::Hash + Eq, V: Default> {
    entries: rustc_hash::FxHashMap<K, V>,
}

impl<K: std::hash::Hash + Eq, V: Default> Default for LinkStore<K, V> {
    fn default() -> Self {
        Self { entries: rustc_hash::FxHashMap::default() }
    }
}

impl<K: std::hash::Hash + Eq + Copy, V: Default> LinkStore<K, V> {
    /// Go `store.Get(key)`: creates the record on first use.
    pub fn get(&mut self, key: K) -> &mut V {
        self.entries.entry(key).or_default()
    }

    /// Go `store.Has(key)`.
    #[must_use]
    pub fn has(&self, key: K) -> bool {
        self.entries.contains_key(&key)
    }

    /// Go `store.TryGet(key)`.
    #[must_use]
    pub fn try_get(&self, key: K) -> Option<&V> {
        self.entries.get(&key)
    }
}

thread_local! {
    static UNPORTED_HITS: Cell<u64> = const { Cell::new(0) };
    static UNPORTED_NAMES: std::cell::RefCell<std::collections::BTreeMap<&'static str, u64>> =
        const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
}

/// Records one hit of unported Go code. The runner reports every name.
/// A run with any hit is not a match.
pub fn record_unported(go_name: &'static str) {
    UNPORTED_HITS.with(|hits| hits.set(hits.get() + 1));
    UNPORTED_NAMES.with(|names| *names.borrow_mut().entry(go_name).or_default() += 1);
}

/// All unported names hit so far, with hit counts.
#[must_use]
pub fn unported_report() -> Vec<(&'static str, u64)> {
    UNPORTED_NAMES.with(|names| names.borrow().iter().map(|(k, v)| (*k, *v)).collect())
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
/// installed. The binder fills the `OnceCell` fields once per file.
pub struct GoFile {
    /// The ts_compiler source file (arena, text, file name).
    pub source: &'static ts_compiler::SourceFile,
    /// The `SourceFile` node.
    pub root: Node,
    /// Go `node.Flags` from the parser for each node, indexed by
    /// `NodeId::index()`. It includes the Go parser context flags.
    pub parser_flags: Vec<NodeFlags>,
    /// Go `ast.SourceFile` fields that the parser and program set.
    pub info: crate::program::SourceFileInfo,
    /// Binder data per node, indexed by `NodeId::index()`.
    pub node_bind: std::cell::OnceCell<Vec<NodeBindData>>,
    pub file_bind: std::cell::OnceCell<FileBindData>,
    pub flow_nodes: std::cell::OnceCell<Vec<FlowNode>>,
}

/// Go `Program` as the checker sees it. Installed once per thread with
/// `crate::program::install`, then read with `prog()`.
pub struct GoProgram {
    pub program: &'static ts_compiler::Program,
    /// Files in Go `Program.SourceFiles()` order. `Node::file_index` indexes it.
    pub files: Vec<GoFile>,
    pub options: crate::options::CompilerOptions,
    /// Binder symbols. Each checker clones this.
    pub bound_symbols: std::cell::OnceCell<SymbolArena>,
}

thread_local! {
    static PROGRAM: std::cell::OnceCell<&'static GoProgram> = const { std::cell::OnceCell::new() };
}

/// Installs the program for this thread. Call once.
pub fn set_prog(program: &'static GoProgram) {
    PROGRAM.with(|cell| {
        assert!(cell.set(program).is_ok(), "GoProgram already installed");
    });
}

/// The installed program, or `None` before `set_prog`. The ported parser
/// reads nodes before the program exists.
#[must_use]
pub fn try_prog() -> Option<&'static GoProgram> {
    PROGRAM.with(|cell| cell.get().copied())
}

/// The installed program. Go code reads nodes without a context; this is
/// how node accessors reach the AST.
#[must_use]
pub fn prog() -> &'static GoProgram {
    PROGRAM.with(|cell| *cell.get().expect("GoProgram not installed"))
}
