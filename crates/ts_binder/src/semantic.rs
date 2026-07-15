//! Canonical typescript-go symbol records and store.
//!
//! This exact contract is namespaced away from the legacy binder's current
//! `Symbol` and `SymbolTable`. Binder-created and checker-transient symbols use
//! the same store-owned arena and cannot be mixed across Programs.
//!
//! This layer intentionally stops at canonical storage operations. Binder
//! declaration traversal/merge diagnostics and upstream `cloneSymbol` /
//! `mergeSymbol` behavior remain unsupported until their dedicated port; a
//! table clone here only copies table membership and reuses symbol identities.

use std::{
    collections::{BTreeMap, HashMap},
    num::{NonZeroU32, NonZeroU64},
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign},
    sync::atomic::{AtomicU64, Ordering},
};

use ts_ast::{FileId, NodeArena, NodeArenaId, NodeId, NodeRef};

use crate::{EscapedName, EscapedNameRef, InternalSymbolName, SymbolFlags};

/// Opaque process-local identity of one canonical semantic store.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SemanticStoreId(NonZeroU64);

impl std::fmt::Debug for SemanticStoreId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("SemanticStoreId")
    }
}

static LAST_SEMANTIC_STORE_ID: AtomicU64 = AtomicU64::new(0);
static LAST_GLOBAL_SYMBOL_ID: AtomicU64 = AtomicU64::new(0);

fn next_nonzero(counter: &AtomicU64, exhausted: &str) -> NonZeroU64 {
    let previous = counter
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
            value.checked_add(1)
        })
        .unwrap_or_else(|_| panic!("{exhausted}"));
    NonZeroU64::new(previous + 1).expect("successful allocation is nonzero")
}

fn allocate_store_id() -> SemanticStoreId {
    SemanticStoreId(next_nonzero(
        &LAST_SEMANTIC_STORE_ID,
        "semantic store identity space exhausted",
    ))
}

fn local_id_for_len(len: usize, exhausted: &str) -> NonZeroU32 {
    let zero_based = u32::try_from(len).unwrap_or_else(|_| panic!("{exhausted}"));
    zero_based
        .checked_add(1)
        .and_then(NonZeroU32::new)
        .unwrap_or_else(|| panic!("{exhausted}"))
}

/// Store-branded identity of one canonical symbol.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SemanticSymbolId {
    store: SemanticStoreId,
    local: NonZeroU32,
}

impl SemanticSymbolId {
    /// Returns the one-based store-local allocation identity.
    #[must_use]
    pub const fn get(self) -> u32 {
        self.local.get()
    }

    #[must_use]
    pub const fn index(self) -> usize {
        (self.get() - 1) as usize
    }
}

/// Store-branded identity of one allocated symbol table.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SymbolTableId {
    store: SemanticStoreId,
    local: NonZeroU32,
}

impl SymbolTableId {
    #[must_use]
    pub const fn get(self) -> u32 {
        self.local.get()
    }

    #[must_use]
    pub const fn index(self) -> usize {
        (self.get() - 1) as usize
    }
}

/// Checker-only flags on canonical and transient symbols.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct CheckFlags(u32);

impl CheckFlags {
    pub const NONE: Self = Self(0);
    pub const INSTANTIATED: Self = Self(1 << 0);
    pub const SYNTHETIC_PROPERTY: Self = Self(1 << 1);
    pub const SYNTHETIC_METHOD: Self = Self(1 << 2);
    pub const READONLY: Self = Self(1 << 3);
    pub const READ_PARTIAL: Self = Self(1 << 4);
    pub const WRITE_PARTIAL: Self = Self(1 << 5);
    pub const HAS_NON_UNIFORM_TYPE: Self = Self(1 << 6);
    pub const HAS_LITERAL_TYPE: Self = Self(1 << 7);
    pub const CONTAINS_PUBLIC: Self = Self(1 << 8);
    pub const CONTAINS_PROTECTED: Self = Self(1 << 9);
    pub const CONTAINS_PRIVATE: Self = Self(1 << 10);
    pub const CONTAINS_STATIC: Self = Self(1 << 11);
    pub const LATE: Self = Self(1 << 12);
    pub const REVERSE_MAPPED: Self = Self(1 << 13);
    pub const OPTIONAL_PARAMETER: Self = Self(1 << 14);
    pub const REST_PARAMETER: Self = Self(1 << 15);
    pub const DEFERRED_TYPE: Self = Self(1 << 16);
    pub const HAS_NEVER_TYPE: Self = Self(1 << 17);
    pub const MAPPED: Self = Self(1 << 18);
    pub const STRIP_OPTIONAL: Self = Self(1 << 19);
    pub const UNRESOLVED: Self = Self(1 << 20);
    pub const IS_DISCRIMINANT_COMPUTED: Self = Self(1 << 21);
    pub const IS_DISCRIMINANT: Self = Self(1 << 22);
    pub const INDEX_SYMBOL: Self = Self(1 << 23);
    pub const SYNTHETIC: Self = Self(Self::SYNTHETIC_PROPERTY.0 | Self::SYNTHETIC_METHOD.0);
    pub const NON_UNIFORM_AND_LITERAL: Self =
        Self(Self::HAS_NON_UNIFORM_TYPE.0 | Self::HAS_LITERAL_TYPE.0);
    pub const PARTIAL: Self = Self(Self::READ_PARTIAL.0 | Self::WRITE_PARTIAL.0);

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

impl BitOr for CheckFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for CheckFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl BitAnd for CheckFlags {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}

impl BitAndAssign for CheckFlags {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

/// Snapshot of one Program file's AST identity and allocated node range.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AstScope {
    arena: NodeArenaId,
    file: FileId,
    node_count: usize,
}

impl AstScope {
    #[must_use]
    pub fn new(file: FileId, arena: &NodeArena) -> Self {
        Self {
            arena: arena.id(),
            file,
            node_count: arena.len(),
        }
    }

    #[must_use]
    pub const fn file(self) -> FileId {
        self.file
    }

    #[must_use]
    pub const fn arena(self) -> NodeArenaId {
        self.arena
    }

    #[must_use]
    pub const fn node_count(self) -> usize {
        self.node_count
    }

    #[must_use]
    pub fn node_ref(self, node: NodeId) -> Option<NodeRef> {
        (node.index() < self.node_count).then(|| NodeRef::new(self.arena, self.file, node))
    }

    fn contains(self, node: NodeRef) -> bool {
        node.is_for(self.arena, self.file) && node.node.index() < self.node_count
    }
}

/// Exact canonical symbol payload. The private, lazily assigned global ID is
/// kept as a store-owned side slot so it cannot become part of identity.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(clippy::struct_field_names)] // `ExportSymbol` is the pinned field name.
pub struct Symbol {
    flags: SymbolFlags,
    check_flags: CheckFlags,
    name: EscapedName,
    declarations: Option<Vec<NodeRef>>,
    value_declaration: Option<NodeRef>,
    members: Option<SymbolTableId>,
    exports: Option<SymbolTableId>,
    parent: Option<SemanticSymbolId>,
    export_symbol: Option<SemanticSymbolId>,
}

impl Symbol {
    #[must_use]
    pub const fn flags(&self) -> SymbolFlags {
        self.flags
    }

    #[must_use]
    pub const fn check_flags(&self) -> CheckFlags {
        self.check_flags
    }

    #[must_use]
    pub const fn name(&self) -> EscapedNameRef<'_> {
        self.name.as_ref()
    }

    #[must_use]
    pub fn declarations(&self) -> Option<&[NodeRef]> {
        self.declarations.as_deref()
    }

    #[must_use]
    pub const fn value_declaration(&self) -> Option<NodeRef> {
        self.value_declaration
    }

    #[must_use]
    pub const fn members(&self) -> Option<SymbolTableId> {
        self.members
    }

    #[must_use]
    pub const fn exports(&self) -> Option<SymbolTableId> {
        self.exports
    }

    #[must_use]
    pub const fn parent(&self) -> Option<SemanticSymbolId> {
        self.parent
    }

    #[must_use]
    pub const fn export_symbol(&self) -> Option<SemanticSymbolId> {
        self.export_symbol
    }
}

/// Fully specified input to one validated symbol allocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolData {
    pub flags: SymbolFlags,
    pub check_flags: CheckFlags,
    pub name: EscapedName,
    pub declarations: Option<Vec<NodeRef>>,
    pub value_declaration: Option<NodeRef>,
    pub members: Option<SymbolTableId>,
    pub exports: Option<SymbolTableId>,
    pub parent: Option<SemanticSymbolId>,
    pub export_symbol: Option<SemanticSymbolId>,
}

impl SymbolData {
    #[must_use]
    pub fn new(flags: SymbolFlags, name: EscapedName) -> Self {
        Self {
            flags,
            check_flags: CheckFlags::NONE,
            name,
            declarations: None,
            value_declaration: None,
            members: None,
            exports: None,
            parent: None,
            export_symbol: None,
        }
    }
}

/// Store-owned map from exact escaped names to canonical symbols.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SymbolTable {
    entries: HashMap<EscapedName, SemanticSymbolId>,
}

impl SymbolTable {
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub fn get(&self, name: EscapedNameRef<'_>) -> Option<SemanticSymbolId> {
        self.entries.get(name.as_bytes()).copied()
    }

    #[must_use]
    pub fn get_source(&self, name: &str) -> Option<SemanticSymbolId> {
        self.entries.get(name.as_bytes()).copied()
    }

    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (EscapedNameRef<'_>, SemanticSymbolId)> {
        self.entries
            .iter()
            .map(|(name, symbol)| (name.as_ref(), *symbol))
    }
}

/// Sole owner and validator of one Program's canonical symbols and tables.
#[derive(Debug)]
pub struct SymbolStore {
    id: SemanticStoreId,
    symbols: Vec<Symbol>,
    checker_created_symbols: Vec<bool>,
    global_symbol_ids: Vec<Option<NonZeroU64>>,
    tables: Vec<SymbolTable>,
    ast_scopes: BTreeMap<FileId, AstScope>,
    ast_files: BTreeMap<NodeArenaId, FileId>,
}

impl Default for SymbolStore {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolStore {
    #[must_use]
    pub fn new() -> Self {
        Self {
            id: allocate_store_id(),
            symbols: Vec::new(),
            checker_created_symbols: Vec::new(),
            global_symbol_ids: Vec::new(),
            tables: Vec::new(),
            ast_scopes: BTreeMap::new(),
            ast_files: BTreeMap::new(),
        }
    }

    #[must_use]
    pub const fn id(&self) -> SemanticStoreId {
        self.id
    }

    #[must_use]
    pub fn symbol_len(&self) -> usize {
        self.symbols.len()
    }

    /// Number of checker-transient symbols already allocated in this owner.
    #[must_use]
    pub fn checker_created_symbol_len(&self) -> usize {
        self.checker_created_symbols
            .iter()
            .filter(|created| **created)
            .count()
    }

    #[must_use]
    pub fn symbol_table_len(&self) -> usize {
        self.tables.len()
    }

    #[must_use]
    pub fn symbol(&self, id: SemanticSymbolId) -> Option<&Symbol> {
        (id.store == self.id)
            .then(|| self.symbols.get(id.index()))
            .flatten()
    }

    #[must_use]
    pub fn symbol_table(&self, id: SymbolTableId) -> Option<&SymbolTable> {
        (id.store == self.id)
            .then(|| self.tables.get(id.index()))
            .flatten()
    }

    #[must_use]
    pub fn contains_symbol(&self, id: SemanticSymbolId) -> bool {
        self.symbol(id).is_some()
    }

    #[must_use]
    pub fn contains_symbol_table(&self, id: SymbolTableId) -> bool {
        self.symbol_table(id).is_some()
    }

    /// Registers a safe AST snapshot. Re-registration may grow but not shrink.
    pub fn register_ast_scope(&mut self, scope: AstScope) -> bool {
        if self.ast_scopes.get(&scope.file).is_some_and(|registered| {
            registered.arena != scope.arena || registered.node_count > scope.node_count
        }) || self
            .ast_files
            .get(&scope.arena)
            .is_some_and(|registered| *registered != scope.file)
        {
            return false;
        }
        self.ast_scopes.insert(scope.file, scope);
        self.ast_files.insert(scope.arena, scope.file);
        true
    }

    #[must_use]
    pub fn contains_node_ref(&self, node: NodeRef) -> bool {
        self.ast_scopes
            .get(&node.file)
            .is_some_and(|scope| scope.contains(node))
    }

    /// Allocates a symbol only after validating every embedded reference.
    pub fn alloc_symbol(&mut self, data: SymbolData) -> Option<SemanticSymbolId> {
        let checker_created = data.flags.contains(SymbolFlags::TRANSIENT);
        if (data.check_flags != CheckFlags::NONE && !checker_created)
            || !self.valid_nodes(data.declarations.as_deref())
            || !self.valid_optional_node(data.value_declaration)
            || !self.valid_optional_table(data.members)
            || !self.valid_optional_table(data.exports)
            || !self.valid_optional_symbol(data.parent)
            || !self.valid_optional_symbol(data.export_symbol)
        {
            return None;
        }
        let local = local_id_for_len(self.symbols.len(), "symbol identity space exhausted");
        let id = SemanticSymbolId {
            store: self.id,
            local,
        };
        self.symbols.push(Symbol {
            flags: data.flags,
            check_flags: data.check_flags,
            name: data.name,
            declarations: data.declarations,
            value_declaration: data.value_declaration,
            members: data.members,
            exports: data.exports,
            parent: data.parent,
            export_symbol: data.export_symbol,
        });
        self.checker_created_symbols.push(checker_created);
        self.global_symbol_ids.push(None);
        Some(id)
    }

    /// Allocates a checker-created symbol in the canonical arena.
    ///
    /// Checker transients share identity and relationship validation with
    /// binder symbols, but always carry the upstream `TRANSIENT` bit.
    ///
    /// # Panics
    ///
    /// Panics if the canonical symbol identity space is exhausted.
    #[must_use]
    pub fn alloc_transient_symbol(
        &mut self,
        flags: SymbolFlags,
        name: EscapedName,
        check_flags: CheckFlags,
    ) -> SemanticSymbolId {
        let mut data = SymbolData::new(flags | SymbolFlags::TRANSIENT, name);
        data.check_flags = check_flags;
        self.alloc_symbol(data)
            .expect("reference-free transient symbol allocation is valid")
    }

    /// Allocates an observable empty table. `None` remains the nil-table state.
    #[must_use]
    pub fn alloc_symbol_table(&mut self) -> SymbolTableId {
        let local = local_id_for_len(self.tables.len(), "symbol table identity space exhausted");
        let id = SymbolTableId {
            store: self.id,
            local,
        };
        self.tables.push(SymbolTable::default());
        id
    }

    /// Creates an independent table containing the same symbol references.
    pub fn clone_symbol_table(&mut self, source: SymbolTableId) -> Option<SymbolTableId> {
        let table = self.symbol_table(source)?.clone();
        let id = self.alloc_symbol_table();
        self.tables[id.index()] = table;
        Some(id)
    }

    /// Returns `None` for invalid provenance; otherwise returns the replaced ID.
    pub fn insert_symbol(
        &mut self,
        table: SymbolTableId,
        name: EscapedName,
        symbol: SemanticSymbolId,
    ) -> Option<Option<SemanticSymbolId>> {
        if !self.contains_symbol_table(table) || !self.contains_symbol(symbol) {
            return None;
        }
        Some(self.tables[table.index()].entries.insert(name, symbol))
    }

    pub fn set_symbol_flags(
        &mut self,
        symbol: SemanticSymbolId,
        flags: SymbolFlags,
        check_flags: CheckFlags,
    ) -> bool {
        if !self.contains_symbol(symbol)
            || (check_flags != CheckFlags::NONE && !self.checker_created_symbols[symbol.index()])
        {
            return false;
        }
        let Some(record) = self.symbol_mut(symbol) else {
            return false;
        };
        record.flags = flags;
        record.check_flags = check_flags;
        true
    }

    /// Atomically replaces declaration provenance after validating all nodes.
    pub fn set_symbol_declarations(
        &mut self,
        symbol: SemanticSymbolId,
        declarations: Option<Vec<NodeRef>>,
        value_declaration: Option<NodeRef>,
    ) -> bool {
        if !self.contains_symbol(symbol)
            || !self.valid_nodes(declarations.as_deref())
            || !self.valid_optional_node(value_declaration)
        {
            return false;
        }
        let record = &mut self.symbols[symbol.index()];
        record.declarations = declarations;
        record.value_declaration = value_declaration;
        true
    }

    /// Atomically replaces all symbol/table relationships.
    pub fn set_symbol_relationships(
        &mut self,
        symbol: SemanticSymbolId,
        members: Option<SymbolTableId>,
        exports: Option<SymbolTableId>,
        parent: Option<SemanticSymbolId>,
        export_symbol: Option<SemanticSymbolId>,
    ) -> bool {
        if !self.contains_symbol(symbol)
            || !self.valid_optional_table(members)
            || !self.valid_optional_table(exports)
            || !self.valid_optional_symbol(parent)
            || !self.valid_optional_symbol(export_symbol)
        {
            return false;
        }
        let record = &mut self.symbols[symbol.index()];
        record.members = members;
        record.exports = exports;
        record.parent = parent;
        record.export_symbol = export_symbol;
        true
    }

    #[must_use]
    pub fn private_identifier_name(
        &mut self,
        containing_class: SemanticSymbolId,
        description: &str,
    ) -> Option<EscapedName> {
        if !description.starts_with('#') {
            return None;
        }
        let global = self.ensure_global_symbol_id(containing_class)?;
        Some(EscapedName::private_identifier(global.get(), description))
    }

    /// Lazily assigns and returns the process-global identity used by pinned
    /// symbol sort keys and caches. Store-local handles do not allocate it.
    pub fn global_symbol_id(&mut self, symbol: SemanticSymbolId) -> Option<u64> {
        self.ensure_global_symbol_id(symbol).map(NonZeroU64::get)
    }

    #[must_use]
    pub fn known_symbol_name(symbol_name: &str) -> EscapedName {
        EscapedName::known_symbol(symbol_name)
    }

    #[must_use]
    pub fn unique_symbol_name(&mut self, symbol: SemanticSymbolId) -> Option<EscapedName> {
        let global = self.ensure_global_symbol_id(symbol)?;
        let name = self.symbol(symbol)?.name();
        Some(EscapedName::unique_symbol(name, global.get()))
    }

    #[must_use]
    pub fn internal_name(name: InternalSymbolName) -> EscapedName {
        EscapedName::internal(name)
    }

    fn symbol_mut(&mut self, id: SemanticSymbolId) -> Option<&mut Symbol> {
        (id.store == self.id)
            .then(|| self.symbols.get_mut(id.index()))
            .flatten()
    }

    fn ensure_global_symbol_id(&mut self, symbol: SemanticSymbolId) -> Option<NonZeroU64> {
        if !self.contains_symbol(symbol) {
            return None;
        }
        let slot = &mut self.global_symbol_ids[symbol.index()];
        Some(*slot.get_or_insert_with(|| {
            next_nonzero(
                &LAST_GLOBAL_SYMBOL_ID,
                "global symbol identity space exhausted",
            )
        }))
    }

    fn valid_nodes(&self, nodes: Option<&[NodeRef]>) -> bool {
        nodes.is_none_or(|nodes| nodes.iter().all(|node| self.contains_node_ref(*node)))
    }

    fn valid_optional_node(&self, node: Option<NodeRef>) -> bool {
        node.is_none_or(|node| self.contains_node_ref(node))
    }

    fn valid_optional_symbol(&self, symbol: Option<SemanticSymbolId>) -> bool {
        symbol.is_none_or(|symbol| self.contains_symbol(symbol))
    }

    fn valid_optional_table(&self, table: Option<SymbolTableId>) -> bool {
        table.is_none_or(|table| self.contains_symbol_table(table))
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeRef};
    use ts_parser::parse_source_file;

    use super::{AstScope, CheckFlags, SymbolData, SymbolStore};
    use crate::{EscapedName, InternalSymbolName, SymbolFlags};

    fn source_scope(store: &mut SymbolStore, file: u32, text: &str) -> (AstScope, NodeRef) {
        let parsed = parse_source_file(text);
        let scope = AstScope::new(FileId::new(file), &parsed.arena);
        assert!(store.register_ast_scope(scope));
        (scope, scope.node_ref(parsed.source_file).unwrap())
    }

    fn alloc_source_symbol(store: &mut SymbolStore, name: &str) -> super::SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source(name),
            ))
            .unwrap()
    }

    #[test]
    fn check_flags_match_the_complete_pinned_inventory() {
        let singles = [
            CheckFlags::INSTANTIATED,
            CheckFlags::SYNTHETIC_PROPERTY,
            CheckFlags::SYNTHETIC_METHOD,
            CheckFlags::READONLY,
            CheckFlags::READ_PARTIAL,
            CheckFlags::WRITE_PARTIAL,
            CheckFlags::HAS_NON_UNIFORM_TYPE,
            CheckFlags::HAS_LITERAL_TYPE,
            CheckFlags::CONTAINS_PUBLIC,
            CheckFlags::CONTAINS_PROTECTED,
            CheckFlags::CONTAINS_PRIVATE,
            CheckFlags::CONTAINS_STATIC,
            CheckFlags::LATE,
            CheckFlags::REVERSE_MAPPED,
            CheckFlags::OPTIONAL_PARAMETER,
            CheckFlags::REST_PARAMETER,
            CheckFlags::DEFERRED_TYPE,
            CheckFlags::HAS_NEVER_TYPE,
            CheckFlags::MAPPED,
            CheckFlags::STRIP_OPTIONAL,
            CheckFlags::UNRESOLVED,
            CheckFlags::IS_DISCRIMINANT_COMPUTED,
            CheckFlags::IS_DISCRIMINANT,
            CheckFlags::INDEX_SYMBOL,
        ];
        for (bit, flag) in singles.into_iter().enumerate() {
            assert_eq!(flag.bits(), 1 << bit);
        }
        assert_eq!(CheckFlags::SYNTHETIC.bits(), 0b110);
        assert_eq!(CheckFlags::NON_UNIFORM_AND_LITERAL.bits(), 0b1100_0000);
        assert_eq!(CheckFlags::PARTIAL.bits(), 0b11_0000);
    }

    #[test]
    fn nil_and_allocated_empty_tables_remain_distinct() {
        let mut store = SymbolStore::new();
        let symbol = alloc_source_symbol(&mut store, "value");
        assert_eq!(store.symbol(symbol).unwrap().members(), None);
        let empty = store.alloc_symbol_table();
        assert!(store.symbol_table(empty).unwrap().is_empty());
        assert!(store.set_symbol_relationships(symbol, Some(empty), None, None, None));
        assert_eq!(store.symbol(symbol).unwrap().members(), Some(empty));
        assert!(store.symbol_table(empty).unwrap().is_empty());
    }

    #[test]
    fn private_and_symbol_names_validate_identity_and_never_collide() {
        let mut first = SymbolStore::new();
        let class_a = alloc_source_symbol(&mut first, "A");
        let class_b = alloc_source_symbol(&mut first, "B");
        let same_first = first.private_identifier_name(class_a, "#x").unwrap();
        let same_second = first.private_identifier_name(class_a, "#x").unwrap();
        let different_class = first.private_identifier_name(class_b, "#x").unwrap();
        assert_eq!(same_first, same_second);
        assert_ne!(same_first, different_class);
        assert!(same_first.as_ref().is_private_identifier());
        assert_eq!(first.private_identifier_name(class_a, "x"), None);

        let mut second = SymbolStore::new();
        let foreign = alloc_source_symbol(&mut second, "A");
        assert_eq!(first.private_identifier_name(foreign, "#x"), None);

        let known = SymbolStore::known_symbol_name("iterator");
        let unique_a = first.unique_symbol_name(class_a).unwrap();
        let unique_b = first.unique_symbol_name(class_b).unwrap();
        assert!(known.as_ref().is_late_bound());
        assert!(unique_a.as_ref().is_late_bound());
        assert_ne!(known, unique_a);
        assert_ne!(unique_a, unique_b);
    }

    #[test]
    fn global_symbol_ids_are_lazy_ordered_and_shared_by_dynamic_names() {
        fn private_id(name: &EscapedName) -> u64 {
            let bytes = name.as_bytes();
            let separator = bytes
                .iter()
                .position(|byte| *byte == b'@')
                .expect("private name has an ID separator");
            std::str::from_utf8(&bytes[2..separator])
                .unwrap()
                .parse()
                .unwrap()
        }

        fn unique_id(name: &EscapedName) -> u64 {
            let bytes = name.as_bytes();
            let separator = bytes
                .iter()
                .rposition(|byte| *byte == b'@')
                .expect("unique name has an ID separator");
            std::str::from_utf8(&bytes[separator + 1..])
                .unwrap()
                .parse()
                .unwrap()
        }

        let mut store = SymbolStore::new();
        let allocated_first = alloc_source_symbol(&mut store, "first");
        let allocated_second = alloc_source_symbol(&mut store, "second");

        // Invalid construction must not consume the first symbol's lazy ID.
        assert_eq!(
            store.private_identifier_name(allocated_first, "missing-hash"),
            None
        );
        let second_name = store.unique_symbol_name(allocated_second).unwrap();
        let first_name = store
            .private_identifier_name(allocated_first, "#field")
            .unwrap();
        let second_id = unique_id(&second_name);
        let first_id = private_id(&first_name);
        assert!(second_id < first_id);

        // Both dynamic families use the same once-assigned global symbol ID.
        assert_eq!(
            unique_id(&store.unique_symbol_name(allocated_first).unwrap()),
            first_id
        );
        assert_eq!(store.global_symbol_id(allocated_second), Some(second_id));
    }

    #[test]
    fn checker_transients_share_the_arena_and_force_the_transient_flag() {
        let mut store = SymbolStore::new();
        let bound = alloc_source_symbol(&mut store, "bound");
        let transient = store.alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source("synthetic"),
            CheckFlags::SYNTHETIC_PROPERTY,
        );
        assert_eq!(bound.get(), 1);
        assert_eq!(transient.get(), 2);
        let record = store.symbol(transient).unwrap();
        assert!(record.flags().contains(SymbolFlags::PROPERTY));
        assert!(record.flags().contains(SymbolFlags::TRANSIENT));
        assert_eq!(record.check_flags(), CheckFlags::SYNTHETIC_PROPERTY);
    }

    #[test]
    fn checker_flags_require_transient_allocation_provenance() {
        let mut store = SymbolStore::new();
        let before = store.symbol_len();
        let mut invalid =
            SymbolData::new(SymbolFlags::PROPERTY, EscapedName::source("not transient"));
        invalid.check_flags = CheckFlags::SYNTHETIC_PROPERTY;
        assert_eq!(store.alloc_symbol(invalid), None);
        assert_eq!(store.symbol_len(), before);

        let bound = alloc_source_symbol(&mut store, "bound");
        let bound_before = store.symbol(bound).unwrap().clone();
        assert!(!store.set_symbol_flags(bound, SymbolFlags::PROPERTY, CheckFlags::LATE));
        assert_eq!(store.symbol(bound), Some(&bound_before));

        let transient = store.alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source("late"),
            CheckFlags::LATE,
        );
        assert!(store.set_symbol_flags(transient, SymbolFlags::PROPERTY, CheckFlags::LATE));
        let late = store.symbol(transient).unwrap();
        assert!(!late.flags().contains(SymbolFlags::TRANSIENT));
        assert_eq!(late.check_flags(), CheckFlags::LATE);
    }

    #[test]
    fn source_internal_and_unicode_names_are_distinct_table_entries() {
        let mut store = SymbolStore::new();
        let table = store.alloc_symbol_table();
        let source = alloc_source_symbol(&mut store, "__call");
        let thorn = alloc_source_symbol(&mut store, "þcall");
        let call = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::SIGNATURE,
                EscapedName::internal(InternalSymbolName::Call),
            ))
            .unwrap();
        assert_eq!(
            store.insert_symbol(table, EscapedName::source("__call"), source),
            Some(None)
        );
        assert_eq!(
            store.insert_symbol(table, EscapedName::source("þcall"), thorn),
            Some(None)
        );
        assert_eq!(
            store.insert_symbol(table, EscapedName::internal(InternalSymbolName::Call), call,),
            Some(None)
        );
        let table = store.symbol_table(table).unwrap();
        assert_eq!(table.len(), 3);
        assert_eq!(table.get_source("__call"), Some(source));
        assert_eq!(table.get_source("þcall"), Some(thorn));
        assert_eq!(table.get(InternalSymbolName::Call.as_ref()), Some(call));
    }

    #[test]
    fn declarations_and_all_foreign_relationships_fail_atomically() {
        let mut first = SymbolStore::new();
        let (_, first_node) = source_scope(&mut first, 1, "let first;");
        let first_symbol = alloc_source_symbol(&mut first, "first");
        let first_table = first.alloc_symbol_table();

        let mut second = SymbolStore::new();
        let (_, second_node) = source_scope(&mut second, 2, "let second;");
        let second_symbol = alloc_source_symbol(&mut second, "second");
        let second_table = second.alloc_symbol_table();
        let before_symbols = second.symbol_len();
        let mut invalid = SymbolData::new(SymbolFlags::PROPERTY, EscapedName::source("bad"));
        invalid.declarations = Some(vec![first_node]);
        assert_eq!(second.alloc_symbol(invalid), None);
        assert_eq!(second.symbol_len(), before_symbols);

        assert!(second.set_symbol_declarations(
            second_symbol,
            Some(vec![second_node]),
            Some(second_node),
        ));
        let before = second.symbol(second_symbol).unwrap().clone();
        assert!(!second.set_symbol_declarations(
            second_symbol,
            Some(vec![first_node]),
            Some(second_node),
        ));
        assert_eq!(second.symbol(second_symbol), Some(&before));

        assert!(!second.set_symbol_relationships(
            second_symbol,
            Some(first_table),
            Some(second_table),
            None,
            None,
        ));
        assert_eq!(second.symbol(second_symbol), Some(&before));
        assert!(!second.set_symbol_relationships(
            second_symbol,
            Some(second_table),
            None,
            Some(first_symbol),
            None,
        ));
        assert_eq!(second.symbol(second_symbol), Some(&before));
        assert_eq!(
            second.insert_symbol(second_table, EscapedName::source("foreign"), first_symbol),
            None
        );
        assert!(second.symbol_table(second_table).unwrap().is_empty());
        assert_eq!(second.symbol(first_symbol), None);
        assert_eq!(second.symbol_table(first_table), None);
    }

    #[test]
    fn shallow_table_clone_has_independent_membership() {
        let mut store = SymbolStore::new();
        let symbol = alloc_source_symbol(&mut store, "one");
        let original = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(original, EscapedName::source("one"), symbol),
            Some(None)
        );
        let cloned = store.clone_symbol_table(original).unwrap();
        let two = alloc_source_symbol(&mut store, "two");
        assert_eq!(
            store.insert_symbol(cloned, EscapedName::source("two"), two),
            Some(None)
        );
        assert_eq!(store.symbol_table(original).unwrap().len(), 1);
        assert_eq!(store.symbol_table(cloned).unwrap().len(), 2);
        assert_eq!(
            store.symbol_table(cloned).unwrap().get_source("one"),
            Some(symbol)
        );
    }
}
