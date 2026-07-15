//! Aggregate ownership and provenance validation for canonical semantic data.

use ts_ast::NodeRef;
use ts_binder::{
    AstScope, CheckFlags, EscapedName, SemanticStoreId, SemanticSymbolId, SymbolData, SymbolFlags,
    SymbolStore, SymbolTableId,
    semantic::{Symbol, SymbolTable},
};

use super::{
    bootstrap::IntrinsicBootstrap,
    ids::{
        ConditionalRootId, IndexInfoId, SignatureId, TypeAliasId, TypeId, TypeMapperId,
        TypePredicateId, TypedArena,
    },
    links::{
        AliasSymbolLinks, ArrayLiteralLinks, AssertionLinks, CheckerLinkStores, DeclaredTypeLinks,
        DeferredSymbolLinks, ExportTypeLinks, JsxElementLinks, LateBoundLinks, MappedSymbolLinks,
        MarkedAssignmentSymbolLinks, MembersAndExportsLinks, ModuleSymbolLinks, NodeLinks,
        ReverseMappedSymbolLinks, SignatureLinks, SpreadLinks, SwitchStatementLinks,
        SymbolNodeLinks, SymbolReferenceLinks, TypeAliasLinks, TypeNodeLinks,
        TypeResolutionBoundary, TypeResolutionStack, TypeResolutionTarget,
        TypeResolutionTargetError, TypeSystemPropertyName, ValueSymbolLinks, VarianceLinks,
    },
    signatures::{
        CompositeSignature, IndexInfo, IndexInfoArena, Signature, SignatureArena, SignatureFlags,
        TupleElementInfo, TupleMetadata, TypePredicate, TypePredicateArena, TypePredicateKind,
    },
    type_records::{ConditionalRoot, TypeAlias, TypeData, TypeRecord},
};

/// Sole allocator and owner of one canonical program's semantic graph.
///
/// Every semantic handle is branded with this store's identity. Record writes
/// validate all incoming handles and AST references before mutating storage.
#[derive(Debug)]
pub struct SemanticStore<TypePayload, MapperPayload> {
    symbols: SymbolStore,
    types: TypedArena<TypeId, TypePayload>,
    mappers: TypedArena<TypeMapperId, MapperPayload>,
    signatures: SignatureArena,
    predicates: TypePredicateArena,
    index_infos: IndexInfoArena,
    type_aliases: TypedArena<TypeAliasId, TypeAlias>,
    conditional_roots: TypedArena<ConditionalRootId, ConditionalRoot>,
    links: CheckerLinkStores,
    type_resolutions: TypeResolutionStack,
    pub(super) intrinsic_bootstrap: Option<IntrinsicBootstrap>,
}

impl<TypePayload, MapperPayload> Default for SemanticStore<TypePayload, MapperPayload> {
    fn default() -> Self {
        Self::new()
    }
}

impl<TypePayload, MapperPayload> SemanticStore<TypePayload, MapperPayload> {
    /// Creates an empty store with a fresh process-local identity.
    ///
    /// # Panics
    ///
    /// Panics if the process has exhausted semantic-store identities.
    #[must_use]
    pub fn new() -> Self {
        Self::from_symbol_store(SymbolStore::new())
    }

    /// Adopts the already-bound Program symbol graph before allocating any
    /// checker-owned semantic records.
    ///
    /// The owner is consumed so safe callers cannot later replace it and split
    /// the brand captured by the type, signature, and mapper arenas.
    #[must_use]
    pub fn from_symbol_store(symbols: SymbolStore) -> Self {
        let id = symbols.id();
        Self {
            symbols,
            types: TypedArena::new(id),
            mappers: TypedArena::new(id),
            signatures: SignatureArena::new(id),
            predicates: TypePredicateArena::new(id),
            index_infos: IndexInfoArena::new(id),
            type_aliases: TypedArena::new(id),
            conditional_roots: TypedArena::new(id),
            links: CheckerLinkStores::default(),
            type_resolutions: TypeResolutionStack::new(id),
            intrinsic_bootstrap: None,
        }
    }

    #[must_use]
    pub fn id(&self) -> SemanticStoreId {
        self.symbols.id()
    }

    /// Registers a safe AST snapshot for semantic references.
    ///
    /// Re-registering the same file/arena pair may increase its node bound.
    /// Shrinking that bound, or reusing either identity with a different
    /// counterpart, is rejected before either registration map is modified.
    pub fn register_ast_scope(&mut self, scope: AstScope) -> bool {
        self.symbols.register_ast_scope(scope)
    }

    #[must_use]
    pub fn contains_node_ref(&self, node: NodeRef) -> bool {
        self.symbols.contains_node_ref(node)
    }

    /// Allocates a canonical type payload.
    ///
    /// # Panics
    ///
    /// Panics before mutation if the local `u32` identity space is exhausted.
    #[allow(dead_code)] // Hook for sibling concrete type allocators as they land.
    pub(super) fn alloc_type(&mut self, payload: TypePayload) -> TypeId {
        self.types.alloc_with(|_| payload)
    }

    pub(super) fn alloc_type_with(
        &mut self,
        make_payload: impl FnOnce(TypeId) -> TypePayload,
    ) -> TypeId {
        self.types.alloc_with(make_payload)
    }

    pub(super) fn type_payload_mut(&mut self, id: TypeId) -> Option<&mut TypePayload> {
        self.types.get_mut(id)
    }

    pub(super) fn alloc_type_alias_with(
        &mut self,
        make_payload: impl FnOnce(TypeAliasId) -> TypeAlias,
    ) -> TypeAliasId {
        self.type_aliases.alloc_with(make_payload)
    }

    pub(super) fn type_alias_payload(&self, id: TypeAliasId) -> Option<&TypeAlias> {
        self.type_aliases.get(id)
    }

    pub(super) fn type_alias_payload_mut(&mut self, id: TypeAliasId) -> Option<&mut TypeAlias> {
        self.type_aliases.get_mut(id)
    }

    pub(super) fn type_alias_len_internal(&self) -> usize {
        self.type_aliases.len()
    }

    pub(super) fn alloc_conditional_root_with(
        &mut self,
        make_payload: impl FnOnce(ConditionalRootId) -> ConditionalRoot,
    ) -> ConditionalRootId {
        self.conditional_roots.alloc_with(make_payload)
    }

    pub(super) fn conditional_root_payload(
        &self,
        id: ConditionalRootId,
    ) -> Option<&ConditionalRoot> {
        self.conditional_roots.get(id)
    }

    pub(super) fn conditional_root_payload_mut(
        &mut self,
        id: ConditionalRootId,
    ) -> Option<&mut ConditionalRoot> {
        self.conditional_roots.get_mut(id)
    }

    pub(super) fn conditional_root_len_internal(&self) -> usize {
        self.conditional_roots.len()
    }

    #[must_use]
    pub fn type_payload(&self, id: TypeId) -> Option<&TypePayload> {
        self.types.get(id)
    }

    #[must_use]
    pub fn type_len(&self) -> usize {
        self.types.len()
    }

    #[must_use]
    pub fn types(&self) -> impl ExactSizeIterator<Item = (TypeId, &TypePayload)> {
        self.types.iter()
    }

    /// Allocates a fully validated canonical semantic symbol.
    pub fn alloc_symbol(&mut self, data: SymbolData) -> Option<SemanticSymbolId> {
        self.symbols.alloc_symbol(data)
    }

    #[must_use]
    pub fn symbol(&self, id: SemanticSymbolId) -> Option<&Symbol> {
        self.symbols.symbol(id)
    }

    #[must_use]
    pub fn symbol_len(&self) -> usize {
        self.symbols.symbol_len()
    }

    /// Returns the embedded canonical symbol owner for read-only queries.
    ///
    /// Mutable access to the owner itself is intentionally unavailable because
    /// replacing it would invalidate the aggregate's single-brand invariant.
    #[must_use]
    pub const fn symbol_store(&self) -> &SymbolStore {
        &self.symbols
    }

    /// Lazily assigns the pinned process-global symbol identity.
    pub fn global_symbol_id(&mut self, symbol: SemanticSymbolId) -> Option<u64> {
        self.symbols.global_symbol_id(symbol)
    }

    pub fn private_identifier_name(
        &mut self,
        containing_class: SemanticSymbolId,
        description: &str,
    ) -> Option<EscapedName> {
        self.symbols
            .private_identifier_name(containing_class, description)
    }

    pub fn unique_symbol_name(&mut self, symbol: SemanticSymbolId) -> Option<EscapedName> {
        self.symbols.unique_symbol_name(symbol)
    }

    #[must_use]
    pub fn alloc_transient_symbol(
        &mut self,
        flags: SymbolFlags,
        name: EscapedName,
        check_flags: CheckFlags,
    ) -> SemanticSymbolId {
        self.symbols
            .alloc_transient_symbol(flags, name, check_flags)
    }

    #[must_use]
    pub fn alloc_symbol_table(&mut self) -> SymbolTableId {
        self.symbols.alloc_symbol_table()
    }

    #[must_use]
    pub fn symbol_table(&self, id: SymbolTableId) -> Option<&SymbolTable> {
        self.symbols.symbol_table(id)
    }

    pub fn insert_symbol(
        &mut self,
        table: SymbolTableId,
        name: EscapedName,
        symbol: SemanticSymbolId,
    ) -> Option<Option<SemanticSymbolId>> {
        self.symbols.insert_symbol(table, name, symbol)
    }

    pub fn clone_symbol_table(&mut self, source: SymbolTableId) -> Option<SymbolTableId> {
        self.symbols.clone_symbol_table(source)
    }

    pub fn set_symbol_flags(
        &mut self,
        symbol: SemanticSymbolId,
        flags: SymbolFlags,
        check_flags: CheckFlags,
    ) -> bool {
        self.symbols.set_symbol_flags(symbol, flags, check_flags)
    }

    pub fn set_symbol_declarations(
        &mut self,
        symbol: SemanticSymbolId,
        declarations: Option<Vec<NodeRef>>,
        value_declaration: Option<NodeRef>,
    ) -> bool {
        self.symbols
            .set_symbol_declarations(symbol, declarations, value_declaration)
    }

    pub fn set_symbol_relationships(
        &mut self,
        symbol: SemanticSymbolId,
        members: Option<SymbolTableId>,
        exports: Option<SymbolTableId>,
        parent: Option<SemanticSymbolId>,
        export_symbol: Option<SemanticSymbolId>,
    ) -> bool {
        self.symbols
            .set_symbol_relationships(symbol, members, exports, parent, export_symbol)
    }

    /// Reads already-allocated common node links without allocating on a miss.
    #[must_use]
    pub fn node_links(&self, node: NodeRef) -> Option<&NodeLinks> {
        self.contains_node_ref(node)
            .then(|| self.links.node.try_get(&node))
            .flatten()
    }

    pub fn ensure_node_links(&mut self, node: NodeRef) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.node.get(node);
        true
    }

    pub fn set_node_links(&mut self, node: NodeRef, links: NodeLinks) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.node.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn symbol_node_links(&self, node: NodeRef) -> Option<&SymbolNodeLinks> {
        self.contains_node_ref(node)
            .then(|| self.links.symbol_node.try_get(&node))
            .flatten()
    }

    pub fn ensure_symbol_node_links(&mut self, node: NodeRef) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.symbol_node.get(node);
        true
    }

    pub fn set_symbol_node_links(&mut self, node: NodeRef, links: SymbolNodeLinks) -> bool {
        if !self.contains_node_ref(node) || !self.valid_optional_symbol(links.resolved_symbol) {
            return false;
        }
        self.links.symbol_node.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn type_node_links(&self, node: NodeRef) -> Option<&TypeNodeLinks> {
        self.contains_node_ref(node)
            .then(|| self.links.type_node.try_get(&node))
            .flatten()
    }

    pub fn ensure_type_node_links(&mut self, node: NodeRef) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.type_node.get(node);
        true
    }

    pub fn set_type_node_links(&mut self, node: NodeRef, links: TypeNodeLinks) -> bool {
        if !self.contains_node_ref(node)
            || !self.valid_optional_type(links.resolved_type)
            || !self.valid_optional_types(links.outer_type_parameters.as_deref())
        {
            return false;
        }
        self.links.type_node.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn signature_links(&self, node: NodeRef) -> Option<&SignatureLinks> {
        self.contains_node_ref(node)
            .then(|| self.links.signature.try_get(&node))
            .flatten()
    }

    pub fn ensure_signature_links(&mut self, node: NodeRef) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.signature.get(node);
        true
    }

    pub fn set_signature_links(&mut self, node: NodeRef, links: SignatureLinks) -> bool {
        if !self.contains_node_ref(node)
            || !self.valid_optional_signature(links.resolved_signature.signature())
            || !self.valid_optional_signature(links.effects_signature.signature())
            || !self.valid_optional_signature(links.decorator_signature.signature())
        {
            return false;
        }
        self.links.signature.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn symbol_reference_links(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&SymbolReferenceLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.symbol_reference.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_symbol_reference_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.symbol_reference.get(symbol);
        true
    }

    pub fn set_symbol_reference_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: SymbolReferenceLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.symbol_reference.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn value_symbol_links(&self, symbol: SemanticSymbolId) -> Option<&ValueSymbolLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.value_symbol.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_value_symbol_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.value_symbol.get(symbol);
        true
    }

    pub fn set_value_symbol_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: ValueSymbolLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || !self.valid_optional_type(links.resolved_type)
            || !self.valid_optional_type(links.write_type)
            || !self.valid_optional_symbol(links.target)
            || !self.valid_optional_mapper(links.mapper)
            || !self.valid_optional_type(links.name_type)
            || !self.valid_optional_type(links.containing_type)
        {
            return false;
        }
        self.links.value_symbol.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn alias_symbol_links(&self, symbol: SemanticSymbolId) -> Option<&AliasSymbolLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.alias_symbol.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_alias_symbol_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.alias_symbol.get(symbol);
        true
    }

    pub fn set_alias_symbol_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: AliasSymbolLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || !self.valid_optional_symbol(links.immediate_target)
            || !self.valid_optional_symbol(links.alias_target.symbol())
            || !self.valid_optional_node(links.type_only_declaration)
        {
            return false;
        }
        self.links.alias_symbol.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn type_alias_links(&self, symbol: SemanticSymbolId) -> Option<&TypeAliasLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.type_alias.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_type_alias_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.type_alias.get(symbol);
        true
    }

    pub fn set_type_alias_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: TypeAliasLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || !self.valid_optional_type(links.declared_type)
            || !self.valid_optional_types(links.type_parameters.as_deref())
            || links.instantiations.as_ref().is_some_and(|instantiations| {
                instantiations
                    .values()
                    .any(|type_id| self.types.get(*type_id).is_none())
            })
        {
            return false;
        }
        self.links.type_alias.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn declared_type_links(&self, symbol: SemanticSymbolId) -> Option<&DeclaredTypeLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.declared_type.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_declared_type_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.declared_type.get(symbol);
        true
    }

    pub fn set_declared_type_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: DeclaredTypeLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol) || !self.valid_optional_type(links.declared_type) {
            return false;
        }
        self.links.declared_type.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn assertion_links(&self, node: NodeRef) -> Option<&AssertionLinks> {
        self.contains_node_ref(node)
            .then(|| self.links.assertion.try_get(&node))
            .flatten()
    }

    pub fn ensure_assertion_links(&mut self, node: NodeRef) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.assertion.get(node);
        true
    }

    pub fn set_assertion_links(&mut self, node: NodeRef, links: AssertionLinks) -> bool {
        if !self.contains_node_ref(node) || !self.valid_optional_type(links.expr_type) {
            return false;
        }
        self.links.assertion.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn array_literal_links(&self, node: NodeRef) -> Option<&ArrayLiteralLinks> {
        self.contains_node_ref(node)
            .then(|| self.links.array_literal.try_get(&node))
            .flatten()
    }

    pub fn ensure_array_literal_links(&mut self, node: NodeRef) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.array_literal.get(node);
        true
    }

    pub fn set_array_literal_links(&mut self, node: NodeRef, links: ArrayLiteralLinks) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.array_literal.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn switch_statement_links(&self, node: NodeRef) -> Option<&SwitchStatementLinks> {
        self.contains_node_ref(node)
            .then(|| self.links.switch_statement.try_get(&node))
            .flatten()
    }

    pub fn ensure_switch_statement_links(&mut self, node: NodeRef) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.switch_statement.get(node);
        true
    }

    pub fn set_switch_statement_links(
        &mut self,
        node: NodeRef,
        links: SwitchStatementLinks,
    ) -> bool {
        if !self.contains_node_ref(node)
            || !self.valid_optional_types(links.switch_types.as_deref())
        {
            return false;
        }
        self.links.switch_statement.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn jsx_element_links(&self, node: NodeRef) -> Option<&JsxElementLinks> {
        self.contains_node_ref(node)
            .then(|| self.links.jsx_element.try_get(&node))
            .flatten()
    }

    pub fn ensure_jsx_element_links(&mut self, node: NodeRef) -> bool {
        if !self.contains_node_ref(node) {
            return false;
        }
        self.links.jsx_element.get(node);
        true
    }

    pub fn set_jsx_element_links(&mut self, node: NodeRef, links: JsxElementLinks) -> bool {
        if !self.contains_node_ref(node)
            || !self.valid_optional_type(links.resolved_jsx_element_attributes_type)
            || !self.valid_optional_symbol(links.jsx_namespace)
            || !self.valid_optional_symbol(links.jsx_implicit_import_container)
        {
            return false;
        }
        self.links.jsx_element.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn mapped_symbol_links(&self, symbol: SemanticSymbolId) -> Option<&MappedSymbolLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.mapped_symbol.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_mapped_symbol_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.mapped_symbol.get(symbol);
        true
    }

    pub fn set_mapped_symbol_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: MappedSymbolLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || !self.valid_optional_type(links.key_type)
            || !self.valid_optional_symbol(links.synthetic_origin)
        {
            return false;
        }
        self.links.mapped_symbol.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn deferred_symbol_links(&self, symbol: SemanticSymbolId) -> Option<&DeferredSymbolLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.deferred_symbol.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_deferred_symbol_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.deferred_symbol.get(symbol);
        true
    }

    pub fn set_deferred_symbol_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: DeferredSymbolLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || !self.valid_optional_type(links.parent)
            || !self.valid_optional_types(links.constituents.as_deref())
            || !self.valid_optional_types(links.write_constituents.as_deref())
        {
            return false;
        }
        self.links.deferred_symbol.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn module_symbol_links(&self, symbol: SemanticSymbolId) -> Option<&ModuleSymbolLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.module_symbol.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_module_symbol_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.module_symbol.get(symbol);
        true
    }

    pub fn set_module_symbol_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: ModuleSymbolLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || !self.valid_optional_symbol_table(links.resolved_exports)
            || links.type_only_export_star_map.as_ref().is_some_and(|map| {
                map.values()
                    .flatten()
                    .any(|node| !self.contains_node_ref(*node))
            })
        {
            return false;
        }
        self.links.module_symbol.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn late_bound_links(&self, symbol: SemanticSymbolId) -> Option<&LateBoundLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.late_bound.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_late_bound_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.late_bound.get(symbol);
        true
    }

    pub fn set_late_bound_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: LateBoundLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol) || !self.valid_optional_symbol(links.late_symbol) {
            return false;
        }
        self.links.late_bound.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn export_type_links(&self, symbol: SemanticSymbolId) -> Option<&ExportTypeLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.export_type.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_export_type_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.export_type.get(symbol);
        true
    }

    pub fn set_export_type_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: ExportTypeLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || !self.valid_optional_symbol(links.target)
            || !self.valid_optional_node(links.originating_import)
        {
            return false;
        }
        self.links.export_type.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn members_and_exports_links(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&MembersAndExportsLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.members_and_exports.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_members_and_exports_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.members_and_exports.get(symbol);
        true
    }

    pub fn set_members_and_exports_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: MembersAndExportsLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || links
                .tables
                .iter()
                .flatten()
                .any(|table| !self.symbols.contains_symbol_table(*table))
        {
            return false;
        }
        self.links.members_and_exports.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn spread_links(&self, symbol: SemanticSymbolId) -> Option<&SpreadLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.spread.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_spread_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.spread.get(symbol);
        true
    }

    pub fn set_spread_links(&mut self, symbol: SemanticSymbolId, links: SpreadLinks) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || !self.valid_optional_symbol(links.left_spread)
            || !self.valid_optional_symbol(links.right_spread)
        {
            return false;
        }
        self.links.spread.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn variance_links(&self, symbol: SemanticSymbolId) -> Option<&VarianceLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.variance.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_variance_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.variance.get(symbol);
        true
    }

    pub fn set_variance_links(&mut self, symbol: SemanticSymbolId, links: VarianceLinks) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.variance.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn reverse_mapped_symbol_links(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&ReverseMappedSymbolLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.reverse_mapped_symbol.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_reverse_mapped_symbol_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.reverse_mapped_symbol.get(symbol);
        true
    }

    pub fn set_reverse_mapped_symbol_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: ReverseMappedSymbolLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol)
            || !self.valid_optional_type(links.property_type)
            || !self.valid_optional_type(links.mapped_type)
            || !self.valid_optional_type(links.constraint_type)
        {
            return false;
        }
        self.links.reverse_mapped_symbol.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn marked_assignment_symbol_links(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&MarkedAssignmentSymbolLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.marked_assignment_symbol.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_marked_assignment_symbol_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.marked_assignment_symbol.get(symbol);
        true
    }

    pub fn set_marked_assignment_symbol_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: MarkedAssignmentSymbolLinks,
    ) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links
            .marked_assignment_symbol
            .replace_key(symbol, links);
        true
    }

    /// Pops one query and returns whether its dependency chain remained
    /// cycle-free.
    pub fn pop_type_resolution(&mut self) -> Option<bool> {
        self.type_resolutions.pop()
    }

    #[must_use]
    pub fn type_resolution_len(&self) -> usize {
        self.type_resolutions.len()
    }

    #[must_use]
    pub fn type_resolution_is_empty(&self) -> bool {
        self.type_resolutions.is_empty()
    }

    #[must_use]
    pub const fn type_resolution_start(&self) -> usize {
        self.type_resolutions.resolution_start()
    }

    pub(super) fn checker_link_allocated_lengths(&self) -> [usize; 23] {
        self.links.allocated_lengths()
    }

    pub(super) fn type_resolution_internal_state(&self) -> (usize, usize, usize, u64) {
        (
            self.type_resolutions.len(),
            self.type_resolutions.resolution_start(),
            self.type_resolutions.boundary_len(),
            self.type_resolutions.next_boundary_serial(),
        )
    }

    /// Starts cycle scanning at the current depth and returns an opaque,
    /// single-use LIFO restoration token.
    pub fn reset_type_resolution_start(&mut self) -> TypeResolutionBoundary {
        self.type_resolutions.reset_resolution_start()
    }

    /// Restores the most recent boundary.
    ///
    /// # Errors
    ///
    /// Returns the token without mutation when it is foreign, reused, or
    /// out-of-order, or when entries pushed inside its boundary remain live.
    pub fn restore_type_resolution_start(
        &mut self,
        token: TypeResolutionBoundary,
    ) -> Result<(), TypeResolutionBoundary> {
        self.type_resolutions.restore_resolution_start(token)
    }

    /// Allocates a canonical type-mapper payload.
    ///
    /// # Panics
    ///
    /// Panics before mutation if the local `u32` identity space is exhausted.
    #[allow(dead_code)] // Hook for sibling concrete mapper allocators as they land.
    pub(super) fn alloc_mapper(&mut self, payload: MapperPayload) -> TypeMapperId {
        self.mappers.alloc_with(|_| payload)
    }

    #[must_use]
    pub fn mapper_payload(&self, id: TypeMapperId) -> Option<&MapperPayload> {
        self.mappers.get(id)
    }

    #[must_use]
    pub fn mapper_len(&self) -> usize {
        self.mappers.len()
    }

    /// Implements typescript-go `checker.go::newSignature` after validating
    /// every referenced semantic object and AST node.
    ///
    /// Invalid provenance returns `None` without allocating a signature.
    /// Exhausting the local identity space panics before mutation.
    #[allow(clippy::too_many_arguments)] // Mirrors upstream newSignature exactly.
    pub fn alloc_signature(
        &mut self,
        flags: SignatureFlags,
        declaration: Option<NodeRef>,
        type_parameters: Vec<TypeId>,
        this_parameter: Option<SemanticSymbolId>,
        parameters: Vec<SemanticSymbolId>,
        resolved_return_type: Option<TypeId>,
        resolved_type_predicate: Option<TypePredicateId>,
        min_argument_count: i32,
    ) -> Option<SignatureId> {
        if !self.valid_optional_node(declaration)
            || !self.valid_types(&type_parameters)
            || !self.valid_optional_symbol(this_parameter)
            || !self.valid_symbols(&parameters)
            || !self.valid_optional_type(resolved_return_type)
            || !self.valid_optional_predicate(resolved_type_predicate)
        {
            return None;
        }
        Some(self.signatures.alloc(
            flags,
            declaration,
            type_parameters,
            this_parameter,
            parameters,
            resolved_return_type,
            resolved_type_predicate,
            min_argument_count,
        ))
    }

    #[must_use]
    pub fn signature(&self, id: SignatureId) -> Option<&Signature> {
        self.signatures.get(id)
    }

    #[must_use]
    pub fn signature_len(&self) -> usize {
        self.signatures.len()
    }

    #[must_use]
    pub fn signatures(&self) -> impl ExactSizeIterator<Item = (SignatureId, &Signature)> {
        self.signatures.iter()
    }

    pub fn set_signature_resolved_min_argument_count(
        &mut self,
        id: SignatureId,
        count: i32,
    ) -> bool {
        self.signatures.set_resolved_min_argument_count(id, count)
    }

    pub fn set_signature_resolved_return_type(
        &mut self,
        id: SignatureId,
        type_id: Option<TypeId>,
    ) -> bool {
        if !self.valid_optional_type(type_id) {
            return false;
        }
        self.signatures.set_resolved_return_type(id, type_id)
    }

    pub fn set_signature_resolved_type_predicate(
        &mut self,
        id: SignatureId,
        predicate: Option<TypePredicateId>,
    ) -> bool {
        if !self.valid_optional_predicate(predicate) {
            return false;
        }
        self.signatures.set_resolved_type_predicate(id, predicate)
    }

    pub fn set_signature_isolated_type(
        &mut self,
        id: SignatureId,
        type_id: Option<TypeId>,
    ) -> bool {
        if !self.valid_optional_type(type_id) {
            return false;
        }
        self.signatures.set_isolated_signature_type(id, type_id)
    }

    pub fn set_signature_target_and_mapper(
        &mut self,
        id: SignatureId,
        target: Option<SignatureId>,
        mapper: Option<TypeMapperId>,
    ) -> bool {
        if !self.valid_optional_signature(target) || !self.valid_optional_mapper(mapper) {
            return false;
        }
        self.signatures.set_target_and_mapper(id, target, mapper)
    }

    pub fn set_signature_composite(
        &mut self,
        id: SignatureId,
        composite: Option<CompositeSignature>,
    ) -> bool {
        if composite.as_ref().is_some_and(|composite| {
            composite
                .signatures()
                .iter()
                .any(|signature| self.signatures.get(*signature).is_none())
        }) {
            return false;
        }
        self.signatures.set_composite(id, composite)
    }

    /// Creates validated union or intersection signature provenance.
    #[must_use]
    pub fn create_composite_signature(
        &self,
        is_union: bool,
        signatures: Vec<SignatureId>,
    ) -> Option<CompositeSignature> {
        if signatures
            .iter()
            .any(|signature| self.signatures.get(*signature).is_none())
        {
            return None;
        }
        Some(CompositeSignature::new(is_union, signatures))
    }

    /// Replaces flags after construction, as required when class constructor
    /// signatures gain or lose upstream's `Abstract` flag.
    pub fn set_signature_flags(&mut self, id: SignatureId, flags: SignatureFlags) -> bool {
        self.signatures.set_flags(id, flags)
    }

    /// Replaces contextual or inferred type parameters after validating that
    /// every type belongs to this store.
    pub fn set_signature_type_parameters(
        &mut self,
        id: SignatureId,
        type_parameters: Vec<TypeId>,
    ) -> bool {
        if !self.valid_types(&type_parameters) {
            return false;
        }
        self.signatures.set_type_parameters(id, type_parameters)
    }

    /// Replaces the contextual or union-combined `this` parameter after
    /// validating symbol provenance.
    pub fn set_signature_this_parameter(
        &mut self,
        id: SignatureId,
        this_parameter: Option<SemanticSymbolId>,
    ) -> bool {
        if !self.valid_optional_symbol(this_parameter) {
            return false;
        }
        self.signatures.set_this_parameter(id, this_parameter)
    }

    /// Allocates a type predicate after validating its optional narrowed type.
    pub fn alloc_type_predicate(
        &mut self,
        kind: TypePredicateKind,
        parameter_index: i32,
        parameter_name: impl Into<String>,
        type_id: Option<TypeId>,
    ) -> Option<TypePredicateId> {
        if !self.valid_optional_type(type_id) {
            return None;
        }
        Some(
            self.predicates
                .alloc(kind, parameter_index, parameter_name, type_id),
        )
    }

    #[must_use]
    pub fn type_predicate(&self, id: TypePredicateId) -> Option<&TypePredicate> {
        self.predicates.get(id)
    }

    #[must_use]
    pub fn type_predicate_len(&self) -> usize {
        self.predicates.len()
    }

    /// Implements typescript-go `checker.go::newIndexInfo` after validating
    /// semantic and AST provenance.
    pub fn alloc_index_info(
        &mut self,
        key_type: TypeId,
        value_type: TypeId,
        is_readonly: bool,
        declaration: Option<NodeRef>,
        components: Vec<NodeRef>,
    ) -> Option<IndexInfoId> {
        if self.types.get(key_type).is_none()
            || self.types.get(value_type).is_none()
            || !self.valid_optional_node(declaration)
            || !components
                .iter()
                .all(|component| self.contains_node_ref(*component))
        {
            return None;
        }
        Some(
            self.index_infos
                .alloc(key_type, value_type, is_readonly, declaration, components),
        )
    }

    #[must_use]
    pub fn index_info(&self, id: IndexInfoId) -> Option<&IndexInfo> {
        self.index_infos.get(id)
    }

    #[must_use]
    pub fn index_info_len(&self) -> usize {
        self.index_infos.len()
    }

    pub fn set_index_info_symbol(
        &mut self,
        id: IndexInfoId,
        symbol: Option<SemanticSymbolId>,
    ) -> bool {
        if !self.valid_optional_symbol(symbol) {
            return false;
        }
        self.index_infos.set_index_symbol(id, symbol)
    }

    /// Creates one tuple element descriptor after validating its optional AST
    /// label against this store's registered Program scopes.
    #[must_use]
    pub fn create_tuple_element_info(
        &self,
        flags: super::signatures::ElementFlags,
        labeled_declaration: Option<NodeRef>,
    ) -> Option<TupleElementInfo> {
        if !self.valid_optional_node(labeled_declaration) {
            return None;
        }
        Some(TupleElementInfo::new(flags, labeled_declaration))
    }

    /// Derives tuple metadata after validating every optional label reference.
    #[must_use]
    pub fn create_tuple_metadata(
        &self,
        element_infos: Vec<TupleElementInfo>,
        readonly: bool,
    ) -> Option<TupleMetadata> {
        if element_infos.iter().any(|info| {
            info.labeled_declaration()
                .is_some_and(|node| !self.contains_node_ref(node))
        }) {
            return None;
        }
        Some(TupleMetadata::new(element_infos, readonly))
    }

    fn valid_optional_node(&self, node: Option<NodeRef>) -> bool {
        node.is_none_or(|node| self.contains_node_ref(node))
    }

    fn valid_types(&self, ids: &[TypeId]) -> bool {
        ids.iter().all(|id| self.types.get(*id).is_some())
    }

    fn valid_optional_types(&self, ids: Option<&[TypeId]>) -> bool {
        ids.is_none_or(|ids| self.valid_types(ids))
    }

    fn valid_optional_type(&self, id: Option<TypeId>) -> bool {
        id.is_none_or(|id| self.types.get(id).is_some())
    }

    fn valid_symbols(&self, ids: &[SemanticSymbolId]) -> bool {
        ids.iter().all(|id| self.symbols.contains_symbol(*id))
    }

    fn valid_optional_symbol(&self, id: Option<SemanticSymbolId>) -> bool {
        id.is_none_or(|id| self.symbols.contains_symbol(id))
    }

    fn valid_optional_symbol_table(&self, id: Option<SymbolTableId>) -> bool {
        id.is_none_or(|id| self.symbols.contains_symbol_table(id))
    }

    fn valid_optional_mapper(&self, id: Option<TypeMapperId>) -> bool {
        id.is_none_or(|id| self.mappers.get(id).is_some())
    }

    fn valid_optional_signature(&self, id: Option<SignatureId>) -> bool {
        id.is_none_or(|id| self.signatures.get(id).is_some())
    }

    fn validate_type_resolution_target(
        &self,
        target: TypeResolutionTarget,
        property: TypeSystemPropertyName,
    ) -> Result<(), TypeResolutionTargetError> {
        let belongs_to_store = match target {
            TypeResolutionTarget::Symbol(symbol) => self.symbols.contains_symbol(symbol),
            TypeResolutionTarget::Type(type_id) => self.types.get(type_id).is_some(),
            TypeResolutionTarget::Signature(signature) => self.signatures.get(signature).is_some(),
            TypeResolutionTarget::Node(node) => self.contains_node_ref(node),
        };
        if belongs_to_store && property.accepts(target) {
            Ok(())
        } else {
            Err(TypeResolutionTargetError { target, property })
        }
    }

    fn valid_optional_predicate(&self, id: Option<TypePredicateId>) -> bool {
        id.is_none_or(|id| self.predicates.get(id).is_some())
    }
}

impl<MapperPayload> SemanticStore<TypeRecord, MapperPayload> {
    /// Pushes one validated lazy-property query and probes the current owned
    /// semantic graph while scanning for cycles.
    ///
    /// The stack, sparse links, types, and signatures are borrowed as disjoint
    /// fields. This preserves upstream's live reverse scan without exposing a
    /// mutable link record across recursion or requiring a stale caller-made
    /// snapshot.
    ///
    /// # Errors
    ///
    /// Returns an error when the target is foreign, the property rejects its
    /// target kind, or a type target does not implement that property.
    pub fn push_type_resolution(
        &mut self,
        target: TypeResolutionTarget,
        property: TypeSystemPropertyName,
    ) -> Result<bool, TypeResolutionTargetError> {
        self.validate_canonical_resolution_target(target, property)?;
        let links = &mut self.links;
        let types = &self.types;
        let signatures = &self.signatures;
        self.type_resolutions
            .push(target, property, |target, property| {
                canonical_resolution_has_property(links, types, signatures, target, property)
            })
    }

    /// Finds a cycle start using the current owned semantic graph.
    ///
    /// This may allocate an exact default sparse link record, matching
    /// typescript-go's use of `LinkStore.Get` in `typeResolutionHasProperty`.
    ///
    /// # Errors
    ///
    /// Returns an error when the target is foreign, the property rejects its
    /// target kind, or a type target does not implement that property.
    pub fn find_type_resolution_cycle_start(
        &mut self,
        target: TypeResolutionTarget,
        property: TypeSystemPropertyName,
    ) -> Result<Option<usize>, TypeResolutionTargetError> {
        self.validate_canonical_resolution_target(target, property)?;
        let links = &mut self.links;
        let types = &self.types;
        let signatures = &self.signatures;
        self.type_resolutions
            .find_cycle_start_index(target, property, |target, property| {
                canonical_resolution_has_property(links, types, signatures, target, property)
            })
    }

    fn validate_canonical_resolution_target(
        &self,
        target: TypeResolutionTarget,
        property: TypeSystemPropertyName,
    ) -> Result<(), TypeResolutionTargetError> {
        self.validate_type_resolution_target(target, property)?;
        if let TypeResolutionTarget::Type(type_id) = target {
            let record = self
                .types
                .get(type_id)
                .expect("validated canonical type target exists");
            if canonical_type_resolution_property(record.data(), property).is_none() {
                return Err(TypeResolutionTargetError { target, property });
            }
        }
        Ok(())
    }
}

fn canonical_resolution_has_property(
    links: &mut CheckerLinkStores,
    types: &TypedArena<TypeId, TypeRecord>,
    signatures: &SignatureArena,
    target: TypeResolutionTarget,
    property: TypeSystemPropertyName,
) -> bool {
    match (target, property) {
        (TypeResolutionTarget::Symbol(symbol), TypeSystemPropertyName::Type) => {
            let handle = links.value_symbol.get(symbol);
            links
                .value_symbol
                .value(handle)
                .expect("same-store link handle exists")
                .resolved_type
                .is_some()
        }
        (TypeResolutionTarget::Symbol(symbol), TypeSystemPropertyName::DeclaredType) => {
            let handle = links.type_alias.get(symbol);
            links
                .type_alias
                .value(handle)
                .expect("same-store link handle exists")
                .declared_type
                .is_some()
        }
        (TypeResolutionTarget::Symbol(symbol), TypeSystemPropertyName::WriteType) => {
            let handle = links.value_symbol.get(symbol);
            links
                .value_symbol
                .value(handle)
                .expect("same-store link handle exists")
                .write_type
                .is_some()
        }
        (TypeResolutionTarget::Symbol(symbol), TypeSystemPropertyName::AliasTarget) => {
            let handle = links.alias_symbol.get(symbol);
            links
                .alias_symbol
                .value(handle)
                .expect("same-store link handle exists")
                .alias_target
                .has_property()
        }
        (TypeResolutionTarget::Type(type_id), property) => {
            let record = types
                .get(type_id)
                .expect("validated canonical type target exists");
            canonical_type_resolution_property(record.data(), property)
                .expect("validated type property is supported")
        }
        (
            TypeResolutionTarget::Signature(signature),
            TypeSystemPropertyName::ResolvedReturnType,
        ) => signatures
            .get(signature)
            .expect("validated canonical signature target exists")
            .resolved_return_type()
            .is_some(),
        (TypeResolutionTarget::Node(node), TypeSystemPropertyName::InitializerIsUndefined) => {
            let handle = links.node.get(node);
            links
                .node
                .value(handle)
                .expect("same-store link handle exists")
                .flags
                .contains(super::links::NodeCheckFlags::INITIALIZER_IS_UNDEFINED_COMPUTED)
        }
        _ => unreachable!("target/property pairing was validated before stack mutation"),
    }
}

fn canonical_type_resolution_property(
    data: &TypeData,
    property: TypeSystemPropertyName,
) -> Option<bool> {
    match property {
        TypeSystemPropertyName::ResolvedTypeArguments => match data {
            TypeData::TypeReference(data) => Some(data.resolved_type_arguments.is_some()),
            TypeData::Interface(data) => Some(data.reference.resolved_type_arguments.is_some()),
            TypeData::Tuple(data) => {
                Some(data.interface.reference.resolved_type_arguments.is_some())
            }
            _ => None,
        },
        TypeSystemPropertyName::ResolvedBaseTypes => match data {
            TypeData::Interface(data) => Some(data.base_types_resolved),
            TypeData::Tuple(data) => Some(data.interface.base_types_resolved),
            _ => None,
        },
        TypeSystemPropertyName::ResolvedBaseConstructorType => match data {
            TypeData::Interface(data) => Some(data.resolved_base_constructor_type.is_some()),
            TypeData::Tuple(data) => Some(data.interface.resolved_base_constructor_type.is_some()),
            _ => None,
        },
        TypeSystemPropertyName::ResolvedBaseConstraint => data
            .constrained()
            .map(|data| data.resolved_base_constraint.is_some()),
        TypeSystemPropertyName::Type
        | TypeSystemPropertyName::DeclaredType
        | TypeSystemPropertyName::ResolvedReturnType
        | TypeSystemPropertyName::WriteType
        | TypeSystemPropertyName::InitializerIsUndefined
        | TypeSystemPropertyName::AliasTarget => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ts_ast::{FileId, NodeRef};
    use ts_binder::{EscapedName, SymbolData, SymbolFlags, SymbolStore};
    use ts_parser::parse_source_file;

    use super::{AstScope, SemanticStore};
    use crate::semantic::{
        AliasSymbolLinks, AliasTargetState, ArrayLiteralLinks, AssertionLinks, CacheHashKey,
        DeclaredTypeLinks, DecoratorSignatureState, DeferredSymbolLinks, EffectsSignatureState,
        ExhaustiveState, ExportTypeLinks, JsxElementLinks, JsxFlags, LateBoundLinks,
        MappedSymbolLinks, MarkedAssignmentSymbolLinks, MembersAndExportsLinks, ModuleSymbolLinks,
        NodeLinks, ResolvedSignatureState, ReverseMappedSymbolLinks, SignatureLinks, SpreadLinks,
        SwitchStatementLinks, SymbolNodeLinks, SymbolReferenceLinks, TypeAliasLinks, TypeNodeLinks,
        TypeRecord, TypeResolutionTarget, TypeSystemPropertyName, ValueSymbolLinks, VarianceFlags,
        VarianceLinks,
        signatures::{ElementFlags, SignatureFlags, TypePredicateKind},
        types::{ObjectFlags, TypeFlags},
    };

    type TestStore = SemanticStore<&'static str, &'static str>;
    type CanonicalTestStore = SemanticStore<TypeRecord, &'static str>;

    fn alloc_test_symbol<TypePayload, MapperPayload>(
        store: &mut SemanticStore<TypePayload, MapperPayload>,
        name: &str,
    ) -> crate::semantic::SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source(name),
            ))
            .unwrap()
    }

    fn empty_signature<TypePayload, MapperPayload>(
        store: &mut SemanticStore<TypePayload, MapperPayload>,
    ) -> crate::semantic::SignatureId {
        store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap()
    }

    fn assert_canonical_property_present(
        store: &mut CanonicalTestStore,
        target: TypeResolutionTarget,
        property: TypeSystemPropertyName,
    ) {
        assert_eq!(store.push_type_resolution(target, property), Ok(true));
        assert_eq!(
            store.find_type_resolution_cycle_start(target, property),
            Ok(None),
            "a live cached property must stop the reverse scan before equality"
        );
        assert_eq!(store.pop_type_resolution(), Some(true));
    }

    fn signature_with_references(
        store: &mut TestStore,
        type_parameters: Vec<crate::semantic::TypeId>,
        this_parameter: Option<crate::semantic::SemanticSymbolId>,
        parameters: Vec<crate::semantic::SemanticSymbolId>,
        return_type: Option<crate::semantic::TypeId>,
        predicate: Option<crate::semantic::TypePredicateId>,
    ) -> Option<crate::semantic::SignatureId> {
        store.alloc_signature(
            SignatureFlags::NONE,
            None,
            type_parameters,
            this_parameter,
            parameters,
            return_type,
            predicate,
            0,
        )
    }

    struct SeededStore {
        store: TestStore,
        type_id: crate::semantic::TypeId,
        symbol: crate::semantic::SemanticSymbolId,
        mapper: crate::semantic::TypeMapperId,
        predicate: crate::semantic::TypePredicateId,
        index_info: crate::semantic::IndexInfoId,
        signature: crate::semantic::SignatureId,
    }

    fn seeded_store(payload: &'static str) -> SeededStore {
        let mut store = TestStore::new();
        let type_id = store.alloc_type(payload);
        let symbol = alloc_test_symbol(&mut store, payload);
        let mapper = store.alloc_mapper(payload);
        let predicate = store
            .alloc_type_predicate(TypePredicateKind::Identifier, 0, payload, Some(type_id))
            .unwrap();
        let index_info = store
            .alloc_index_info(type_id, type_id, false, None, Vec::new())
            .unwrap();
        let signature = empty_signature(&mut store);
        SeededStore {
            store,
            type_id,
            symbol,
            mapper,
            predicate,
            index_info,
            signature,
        }
    }

    fn assert_signature_unmodified(store: &TestStore, id: crate::semantic::SignatureId) {
        let signature = store.signature(id).unwrap();
        assert_eq!(signature.flags(), SignatureFlags::NONE);
        assert_eq!(signature.resolved_min_argument_count(), -1);
        assert_eq!(signature.resolved_return_type(), None);
        assert_eq!(signature.resolved_type_predicate(), None);
        assert_eq!(signature.isolated_signature_type(), None);
        assert_eq!(signature.target(), None);
        assert_eq!(signature.mapper(), None);
        assert_eq!(signature.this_parameter(), None);
        assert!(signature.type_parameters().is_empty());
        assert_eq!(signature.composite(), None);
    }

    #[test]
    fn store_identity_is_opaque_unique_and_preserved_by_moves() {
        let store = TestStore::new();
        let identity = store.id();
        assert_eq!(format!("{identity:?}"), "SemanticStoreId");

        let moved = store;
        assert_eq!(moved.id(), identity);
        assert_ne!(TestStore::default().id(), identity);
    }

    #[test]
    fn embedded_symbol_store_is_the_single_brand_and_global_id_owner() {
        let mut store = TestStore::new();
        assert_eq!(store.symbol_store().id(), store.id());
        let symbol = alloc_test_symbol(&mut store, "value");
        let global = store.global_symbol_id(symbol).unwrap();
        assert_eq!(store.global_symbol_id(symbol), Some(global));

        let mut foreign = TestStore::new();
        let foreign_symbol = alloc_test_symbol(&mut foreign, "value");
        assert_eq!(symbol.get(), foreign_symbol.get());
        assert_ne!(symbol, foreign_symbol);
        assert_eq!(store.global_symbol_id(foreign_symbol), None);
    }

    #[test]
    fn prebound_symbol_store_is_consumed_without_splitting_identity() {
        let mut symbols = SymbolStore::new();
        let identity = symbols.id();
        let parsed = parse_source_file("const prebound = 1;");
        let scope = AstScope::new(FileId::new(41), &parsed.arena);
        let declaration = scope.node_ref(parsed.source_file).unwrap();
        assert!(symbols.register_ast_scope(scope));
        let mut symbol_data =
            SymbolData::new(SymbolFlags::PROPERTY, EscapedName::source("prebound"));
        symbol_data.declarations = Some(vec![declaration]);
        symbol_data.value_declaration = Some(declaration);
        let symbol = symbols.alloc_symbol(symbol_data).unwrap();
        let table = symbols.alloc_symbol_table();
        assert_eq!(
            symbols.insert_symbol(table, EscapedName::source("prebound"), symbol),
            Some(None)
        );
        let global_id = symbols.global_symbol_id(symbol).unwrap();

        let mut store = TestStore::from_symbol_store(symbols);
        assert_eq!(store.id(), identity);
        assert_eq!(store.symbol_store().id(), identity);
        assert!(store.contains_node_ref(declaration));
        assert_eq!(
            store.symbol(symbol).unwrap().name().as_utf8(),
            Some("prebound")
        );
        assert_eq!(
            store.symbol_table(table).unwrap().get_source("prebound"),
            Some(symbol)
        );
        assert_eq!(store.global_symbol_id(symbol), Some(global_id));

        let type_id = store.alloc_type("checker type");
        assert_eq!(store.type_payload(type_id), Some(&"checker type"));
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                Some(symbol),
                vec![symbol],
                Some(type_id),
                None,
                1,
            )
            .unwrap();
        assert_eq!(
            store.signature(signature).unwrap().this_parameter(),
            Some(symbol)
        );
    }

    #[test]
    fn foreign_store_id_one_is_rejected_by_allocations_without_mutation() {
        let first = seeded_store("first");
        let mut second = seeded_store("second");

        assert_eq!(
            [
                first.type_id.get(),
                first.symbol.get(),
                first.mapper.get(),
                first.predicate.get(),
                first.index_info.get(),
                first.signature.get(),
            ],
            [1; 6]
        );
        assert_eq!(
            [
                second.type_id.get(),
                second.symbol.get(),
                second.mapper.get(),
                second.predicate.get(),
                second.index_info.get(),
                second.signature.get(),
            ],
            [1; 6]
        );
        assert_ne!(first.type_id, second.type_id);
        assert_ne!(first.signature, second.signature);
        assert_ne!(first.predicate, second.predicate);
        assert_ne!(first.index_info, second.index_info);

        let predicate_count = second.store.type_predicate_len();
        assert_eq!(
            second.store.alloc_type_predicate(
                TypePredicateKind::Identifier,
                0,
                "foreign",
                Some(first.type_id)
            ),
            None
        );
        assert_eq!(second.store.type_predicate_len(), predicate_count);
        let index_count = second.store.index_info_len();
        assert_eq!(
            second
                .store
                .alloc_index_info(first.type_id, second.type_id, false, None, Vec::new()),
            None
        );
        assert_eq!(
            second
                .store
                .alloc_index_info(second.type_id, first.type_id, false, None, Vec::new()),
            None
        );
        assert_eq!(second.store.index_info_len(), index_count);
    }

    #[test]
    fn signature_allocation_rejects_each_foreign_id_one_slot_independently() {
        let first = seeded_store("first");
        let mut second = seeded_store("second");
        let signature_count = second.store.signature_len();

        assert_eq!(
            signature_with_references(
                &mut second.store,
                vec![first.type_id],
                Some(second.symbol),
                vec![second.symbol],
                Some(second.type_id),
                Some(second.predicate),
            ),
            None
        );
        assert_eq!(
            signature_with_references(
                &mut second.store,
                vec![second.type_id],
                Some(first.symbol),
                vec![second.symbol],
                Some(second.type_id),
                Some(second.predicate),
            ),
            None
        );
        assert_eq!(
            signature_with_references(
                &mut second.store,
                vec![second.type_id],
                Some(second.symbol),
                vec![first.symbol],
                Some(second.type_id),
                Some(second.predicate),
            ),
            None
        );
        assert_eq!(
            signature_with_references(
                &mut second.store,
                vec![second.type_id],
                Some(second.symbol),
                vec![second.symbol],
                Some(first.type_id),
                Some(second.predicate),
            ),
            None
        );
        assert_eq!(
            signature_with_references(
                &mut second.store,
                vec![second.type_id],
                Some(second.symbol),
                vec![second.symbol],
                Some(second.type_id),
                Some(first.predicate),
            ),
            None
        );
        assert_eq!(second.store.signature_len(), signature_count);
    }

    #[test]
    fn foreign_store_id_one_is_rejected_by_setters_without_mutation() {
        let first = seeded_store("first");
        let mut second = seeded_store("second");
        let target = empty_signature(&mut second.store);
        let foreign_composite = first
            .store
            .create_composite_signature(true, vec![first.signature]);
        let store = &mut second.store;

        assert!(!store.set_signature_resolved_min_argument_count(first.signature, 2));
        assert!(!store.set_signature_flags(first.signature, SignatureFlags::ABSTRACT));
        assert!(!store.set_signature_target_and_mapper(
            target,
            Some(first.signature),
            Some(second.mapper)
        ));
        assert!(!store.set_signature_target_and_mapper(
            target,
            Some(second.signature),
            Some(first.mapper)
        ));
        assert!(!store.set_signature_resolved_return_type(target, Some(first.type_id)));
        assert!(!store.set_signature_isolated_type(target, Some(first.type_id)));
        assert!(!store.set_signature_resolved_type_predicate(target, Some(first.predicate)));
        assert!(!store.set_signature_this_parameter(target, Some(first.symbol)));
        assert!(!store.set_signature_type_parameters(target, vec![first.type_id]));
        assert!(!store.set_signature_composite(target, foreign_composite));
        assert!(
            store
                .create_composite_signature(true, vec![first.signature])
                .is_none()
        );
        assert_signature_unmodified(store, target);

        assert_eq!(store.type_payload(first.type_id), None);
        assert_eq!(store.symbol(first.symbol), None);
        assert_eq!(store.mapper_payload(first.mapper), None);
        assert_eq!(store.type_predicate(first.predicate), None);
        assert_eq!(store.index_info(first.index_info), None);
        assert!(!store.set_index_info_symbol(second.index_info, Some(first.symbol)));
        assert!(!store.set_index_info_symbol(first.index_info, Some(second.symbol)));
        assert_eq!(
            store.index_info(second.index_info).unwrap().index_symbol(),
            None
        );
    }

    #[test]
    fn arena_branded_node_refs_reject_equal_foreign_file_and_node_ids() {
        let first_parse = parse_source_file("const value = 1;");
        let second_parse = parse_source_file("const value = 1;");
        let file = FileId::new(0);
        let first_scope = AstScope::new(file, &first_parse.arena);
        let second_scope = AstScope::new(file, &second_parse.arena);
        let first_ref = first_scope.node_ref(first_parse.source_file).unwrap();
        let second_ref = second_scope.node_ref(second_parse.source_file).unwrap();

        let mut first_store = TestStore::new();
        assert!(first_store.register_ast_scope(first_scope));
        let foreign_element = first_store
            .create_tuple_element_info(ElementFlags::REQUIRED, Some(first_ref))
            .unwrap();

        assert_eq!(first_ref.file, second_ref.file);
        assert_eq!(first_ref.node, second_ref.node);
        assert_ne!(first_ref.arena, second_ref.arena);

        let mut store = TestStore::new();
        assert!(store.register_ast_scope(second_scope));
        assert!(store.contains_node_ref(second_ref));
        assert!(!store.contains_node_ref(first_ref));
        assert!(!store.register_ast_scope(first_scope));
        assert!(store.contains_node_ref(second_ref));

        let signature_count = store.signature_len();
        assert_eq!(
            store.alloc_signature(
                SignatureFlags::NONE,
                Some(first_ref),
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            ),
            None
        );
        assert_eq!(store.signature_len(), signature_count);
        let key_type = store.alloc_type("key");
        let value_type = store.alloc_type("value");
        let index_count = store.index_info_len();
        assert_eq!(
            store.alloc_index_info(
                key_type,
                value_type,
                false,
                Some(first_ref),
                vec![second_ref]
            ),
            None
        );
        assert_eq!(
            store.alloc_index_info(
                key_type,
                value_type,
                false,
                Some(second_ref),
                vec![first_ref]
            ),
            None
        );
        assert_eq!(store.index_info_len(), index_count);
        assert_eq!(
            store.create_tuple_element_info(ElementFlags::REQUIRED, Some(first_ref)),
            None
        );
        assert_eq!(
            store.create_tuple_metadata(vec![foreign_element], false),
            None
        );
        assert!(
            store
                .create_tuple_element_info(ElementFlags::REQUIRED, Some(second_ref))
                .is_some()
        );
        assert!(
            store
                .alloc_signature(
                    SignatureFlags::NONE,
                    Some(second_ref),
                    Vec::new(),
                    None,
                    Vec::new(),
                    None,
                    None,
                    0,
                )
                .is_some()
        );

        let out_of_bounds = NodeRef::new(
            second_ref.arena,
            second_ref.file,
            ts_ast::NodeId::new(u32::MAX),
        );
        assert!(!store.contains_node_ref(out_of_bounds));
    }

    #[test]
    fn ast_scope_refresh_cannot_shrink_past_a_stored_node_reference() {
        let mut parsed = parse_source_file("const value = 1;");
        let file = FileId::new(3);
        let original_scope = AstScope::new(file, &parsed.arena);
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(original_scope));

        let copied_node = parsed.arena.get(parsed.source_file).unwrap().clone();
        let later_node = parsed.arena.alloc(copied_node);
        let grown_scope = AstScope::new(file, &parsed.arena);
        assert!(grown_scope.node_count() > original_scope.node_count());
        assert!(store.register_ast_scope(grown_scope));

        let later_ref = grown_scope.node_ref(later_node).unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(later_ref),
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();

        assert!(!store.register_ast_scope(original_scope));
        assert!(store.contains_node_ref(later_ref));
        assert_eq!(
            store.signature(signature).unwrap().declaration(),
            Some(later_ref)
        );
    }

    #[test]
    fn upstream_record_defaults_mutations_and_tuple_derivation_stay_exact() {
        let parsed = parse_source_file("function f(value: string): string { return value; }");
        let scope = AstScope::new(FileId::new(4), &parsed.arena);
        let declaration = scope.node_ref(parsed.source_file).unwrap();
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(scope));

        let type_parameter = store.alloc_type("T");
        let return_type = store.alloc_type("string");
        let isolated_type = store.alloc_type("isolated");
        let replacement_type_parameter = store.alloc_type("U");
        let this_parameter = alloc_test_symbol(&mut store, "this");
        let parameter = alloc_test_symbol(&mut store, "value");
        let replacement_this = alloc_test_symbol(&mut store, "replacement this");
        let mapper = store.alloc_mapper("instantiate T");
        let predicate = store
            .alloc_type_predicate(TypePredicateKind::Identifier, 0, "value", Some(return_type))
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::HAS_REST_PARAMETER | SignatureFlags::HAS_LITERAL_TYPES,
                Some(declaration),
                vec![type_parameter],
                Some(this_parameter),
                vec![parameter],
                Some(return_type),
                Some(predicate),
                1,
            )
            .unwrap();

        assert_eq!(type_parameter.get(), 1);
        assert_eq!(this_parameter.get(), 1);
        assert_eq!(mapper.get(), 1);
        assert_eq!(predicate.get(), 1);
        assert_eq!(signature.get(), 1);
        let value = store.signature(signature).unwrap();
        assert_eq!(value.id(), signature);
        assert_eq!(value.resolved_min_argument_count(), -1);
        assert_eq!(value.target(), None);
        assert_eq!(value.mapper(), None);
        assert_eq!(value.isolated_signature_type(), None);
        assert_eq!(value.composite(), None);

        assert!(store.set_signature_resolved_min_argument_count(signature, 2));
        assert!(store.set_signature_resolved_return_type(signature, None));
        assert!(store.set_signature_resolved_type_predicate(signature, None));
        assert!(store.set_signature_isolated_type(signature, Some(isolated_type)));
        assert!(store.set_signature_target_and_mapper(signature, None, Some(mapper)));
        assert!(store.set_signature_flags(signature, SignatureFlags::ABSTRACT));
        assert!(store.set_signature_type_parameters(signature, vec![replacement_type_parameter]));
        assert!(store.set_signature_this_parameter(signature, Some(replacement_this)));
        let value = store.signature(signature).unwrap();
        assert_eq!(value.resolved_min_argument_count(), 2);
        assert_eq!(value.resolved_return_type(), None);
        assert_eq!(value.resolved_type_predicate(), None);
        assert_eq!(value.isolated_signature_type(), Some(isolated_type));
        assert_eq!(value.mapper(), Some(mapper));
        assert_eq!(value.flags(), SignatureFlags::ABSTRACT);
        assert_eq!(value.type_parameters(), [replacement_type_parameter]);
        assert_eq!(value.this_parameter(), Some(replacement_this));

        let infos = vec![
            store
                .create_tuple_element_info(ElementFlags::REQUIRED, Some(declaration))
                .unwrap(),
            store
                .create_tuple_element_info(ElementFlags::OPTIONAL, None)
                .unwrap(),
            store
                .create_tuple_element_info(ElementFlags::VARIADIC, None)
                .unwrap(),
        ];
        let tuple = store.create_tuple_metadata(infos.clone(), true).unwrap();
        assert_eq!(tuple.element_infos(), infos);
        assert_eq!(tuple.min_length(), 2);
        assert_eq!(tuple.fixed_length(), 2);
        assert_eq!(
            tuple.combined_flags(),
            ElementFlags::REQUIRED | ElementFlags::OPTIONAL | ElementFlags::VARIADIC
        );
        assert!(tuple.is_readonly());

        let absent = store
            .alloc_type_predicate(TypePredicateKind::AssertsIdentifier, 3, "condition", None)
            .unwrap();
        assert_eq!(store.type_predicate(absent).unwrap().type_id(), None);

        let index = store
            .alloc_index_info(
                return_type,
                isolated_type,
                true,
                Some(declaration),
                vec![declaration],
            )
            .unwrap();
        assert_eq!(index.get(), 1);
        assert_eq!(store.index_info(index).unwrap().index_symbol(), None);
        assert!(store.set_index_info_symbol(index, Some(parameter)));
        assert_eq!(
            store.index_info(index).unwrap().index_symbol(),
            Some(parameter)
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Exercises all sparse stores and exact default states.
    fn sparse_semantic_links_preserve_absent_and_allocated_default_records() {
        let parsed = parse_source_file("type T = string;");
        let scope = AstScope::new(FileId::new(21), &parsed.arena);
        let node = scope.node_ref(parsed.source_file).unwrap();
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(scope));
        let symbol = alloc_test_symbol(&mut store, "T");

        assert_eq!(store.node_links(node), None);
        assert_eq!(store.symbol_node_links(node), None);
        assert_eq!(store.type_node_links(node), None);
        assert_eq!(store.assertion_links(node), None);
        assert_eq!(store.array_literal_links(node), None);
        assert_eq!(store.switch_statement_links(node), None);
        assert_eq!(store.jsx_element_links(node), None);
        assert_eq!(store.signature_links(node), None);
        assert_eq!(store.symbol_reference_links(symbol), None);
        assert_eq!(store.value_symbol_links(symbol), None);
        assert_eq!(store.mapped_symbol_links(symbol), None);
        assert_eq!(store.deferred_symbol_links(symbol), None);
        assert_eq!(store.alias_symbol_links(symbol), None);
        assert_eq!(store.module_symbol_links(symbol), None);
        assert_eq!(store.late_bound_links(symbol), None);
        assert_eq!(store.export_type_links(symbol), None);
        assert_eq!(store.members_and_exports_links(symbol), None);
        assert_eq!(store.type_alias_links(symbol), None);
        assert_eq!(store.declared_type_links(symbol), None);
        assert_eq!(store.spread_links(symbol), None);
        assert_eq!(store.variance_links(symbol), None);
        assert_eq!(store.reverse_mapped_symbol_links(symbol), None);
        assert_eq!(store.marked_assignment_symbol_links(symbol), None);

        assert!(store.ensure_node_links(node));
        assert!(store.ensure_symbol_node_links(node));
        assert!(store.ensure_type_node_links(node));
        assert!(store.ensure_assertion_links(node));
        assert!(store.ensure_array_literal_links(node));
        assert!(store.ensure_switch_statement_links(node));
        assert!(store.ensure_jsx_element_links(node));
        assert!(store.ensure_signature_links(node));
        assert!(store.ensure_symbol_reference_links(symbol));
        assert!(store.ensure_value_symbol_links(symbol));
        assert!(store.ensure_mapped_symbol_links(symbol));
        assert!(store.ensure_deferred_symbol_links(symbol));
        assert!(store.ensure_alias_symbol_links(symbol));
        assert!(store.ensure_module_symbol_links(symbol));
        assert!(store.ensure_late_bound_links(symbol));
        assert!(store.ensure_export_type_links(symbol));
        assert!(store.ensure_members_and_exports_links(symbol));
        assert!(store.ensure_type_alias_links(symbol));
        assert!(store.ensure_declared_type_links(symbol));
        assert!(store.ensure_spread_links(symbol));
        assert!(store.ensure_variance_links(symbol));
        assert!(store.ensure_reverse_mapped_symbol_links(symbol));
        assert!(store.ensure_marked_assignment_symbol_links(symbol));

        assert_eq!(store.node_links(node), Some(&NodeLinks::default()));
        assert_eq!(
            store.symbol_node_links(node),
            Some(&SymbolNodeLinks::default())
        );
        assert_eq!(store.type_node_links(node), Some(&TypeNodeLinks::default()));
        assert_eq!(
            store.assertion_links(node),
            Some(&AssertionLinks::default())
        );
        assert_eq!(
            store.array_literal_links(node),
            Some(&ArrayLiteralLinks::default())
        );
        assert_eq!(
            store.switch_statement_links(node),
            Some(&SwitchStatementLinks::default())
        );
        assert_eq!(
            store.jsx_element_links(node),
            Some(&JsxElementLinks::default())
        );
        assert_eq!(
            store.signature_links(node),
            Some(&SignatureLinks::default())
        );
        assert_eq!(
            store.symbol_reference_links(symbol),
            Some(&SymbolReferenceLinks::default())
        );
        assert_eq!(
            store.value_symbol_links(symbol),
            Some(&ValueSymbolLinks::default())
        );
        assert_eq!(
            store.mapped_symbol_links(symbol),
            Some(&MappedSymbolLinks::default())
        );
        assert_eq!(
            store.deferred_symbol_links(symbol),
            Some(&DeferredSymbolLinks::default())
        );
        assert_eq!(
            store.alias_symbol_links(symbol),
            Some(&AliasSymbolLinks::default())
        );
        assert_eq!(
            store.module_symbol_links(symbol),
            Some(&ModuleSymbolLinks::default())
        );
        assert_eq!(
            store.late_bound_links(symbol),
            Some(&LateBoundLinks::default())
        );
        assert_eq!(
            store.export_type_links(symbol),
            Some(&ExportTypeLinks::default())
        );
        assert_eq!(
            store.members_and_exports_links(symbol),
            Some(&MembersAndExportsLinks::default())
        );
        assert_eq!(
            store.type_alias_links(symbol),
            Some(&TypeAliasLinks::default())
        );
        assert_eq!(
            store.declared_type_links(symbol),
            Some(&DeclaredTypeLinks::default())
        );
        assert_eq!(store.spread_links(symbol), Some(&SpreadLinks::default()));
        assert_eq!(
            store.variance_links(symbol),
            Some(&VarianceLinks::default())
        );
        assert_eq!(
            store.reverse_mapped_symbol_links(symbol),
            Some(&ReverseMappedSymbolLinks::default())
        );
        assert_eq!(
            store.marked_assignment_symbol_links(symbol),
            Some(&MarkedAssignmentSymbolLinks::default())
        );

        let allocated_empty = TypeAliasLinks {
            type_parameters: Some(Vec::new()),
            instantiations: Some(HashMap::new()),
            ..TypeAliasLinks::default()
        };
        assert!(store.set_type_alias_links(symbol, allocated_empty.clone()));
        assert_eq!(store.type_alias_links(symbol), Some(&allocated_empty));
        assert_ne!(
            store.type_alias_links(symbol),
            Some(&TypeAliasLinks::default())
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Exercises every field in the dependency-closed link slice.
    fn semantic_link_commits_accept_owned_ids_and_exact_field_states() {
        let parsed = parse_source_file("const value = 1;");
        let scope = AstScope::new(FileId::new(22), &parsed.arena);
        let node = scope.node_ref(parsed.source_file).unwrap();
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(scope));
        let symbol = alloc_test_symbol(&mut store, "value");
        let target = alloc_test_symbol(&mut store, "target");
        // Upstream's unknown/error/unresolved type sentinels are still real
        // type pointers. Their Rust equivalents remain concrete TypeIds in
        // every type-valued cache rather than becoming generic enum states.
        let type_id = store.alloc_type("concrete unresolved/error type sentinel");
        let mapper = store.alloc_mapper("identity");
        let signature = empty_signature(&mut store);
        let table = store.alloc_symbol_table();

        let symbol_node = SymbolNodeLinks {
            resolved_symbol: Some(target),
        };
        assert!(store.set_symbol_node_links(node, symbol_node.clone()));
        assert_eq!(store.symbol_node_links(node), Some(&symbol_node));

        let type_node = TypeNodeLinks {
            resolved_type: Some(type_id),
            outer_type_parameters: Some(vec![type_id]),
        };
        assert!(store.set_type_node_links(node, type_node.clone()));
        assert_eq!(store.type_node_links(node), Some(&type_node));

        let signature_links = SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolving,
            effects_signature: EffectsSignatureState::NoEffects,
            decorator_signature: DecoratorSignatureState::Resolved(signature),
        };
        assert!(store.set_signature_links(node, signature_links.clone()));
        assert_eq!(store.signature_links(node), Some(&signature_links));
        let completed_signature_links = SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            effects_signature: EffectsSignatureState::Resolved(signature),
            decorator_signature: DecoratorSignatureState::NotApplicable,
        };
        assert!(store.set_signature_links(node, completed_signature_links.clone()));
        assert_eq!(
            store.signature_links(node),
            Some(&completed_signature_links)
        );

        let value_links = ValueSymbolLinks {
            resolved_type: Some(type_id),
            write_type: Some(type_id),
            target: Some(target),
            mapper: Some(mapper),
            name_type: Some(type_id),
            containing_type: Some(type_id),
            function_or_constructor_checked: true,
        };
        assert!(store.set_value_symbol_links(symbol, value_links.clone()));
        assert_eq!(store.value_symbol_links(symbol), Some(&value_links));

        let alias_links = AliasSymbolLinks {
            immediate_target: Some(target),
            alias_target: AliasTargetState::Unknown,
            referenced: true,
            type_only_declaration: Some(node),
        };
        assert!(store.set_alias_symbol_links(symbol, alias_links.clone()));
        assert_eq!(store.alias_symbol_links(symbol), Some(&alias_links));

        let type_alias_links = TypeAliasLinks {
            declared_type: Some(type_id),
            type_parameters: Some(vec![type_id]),
            instantiations: Some(HashMap::from([(CacheHashKey::from_halves(1, 2), type_id)])),
            is_constructor_declared_property: true,
        };
        assert!(store.set_type_alias_links(symbol, type_alias_links.clone()));
        assert_eq!(store.type_alias_links(symbol), Some(&type_alias_links));

        let declared_links = DeclaredTypeLinks {
            declared_type: Some(type_id),
            interface_checked: true,
            index_signatures_checked: true,
            type_parameters_checked: true,
            enum_checked: true,
        };
        assert!(store.set_declared_type_links(symbol, declared_links.clone()));
        assert_eq!(store.declared_type_links(symbol), Some(&declared_links));

        let assertion = AssertionLinks {
            expr_type: Some(type_id),
        };
        assert!(store.set_assertion_links(node, assertion.clone()));
        assert_eq!(store.assertion_links(node), Some(&assertion));

        let array_literal = ArrayLiteralLinks {
            indices_computed: true,
            first_spread_index: -1,
            last_spread_index: -1,
        };
        assert!(store.set_array_literal_links(node, array_literal.clone()));
        assert_eq!(store.array_literal_links(node), Some(&array_literal));

        let switch_statement = SwitchStatementLinks {
            exhaustive_state: ExhaustiveState::True,
            switch_types_computed: true,
            witnesses_computed: true,
            switch_types: Some(vec![type_id]),
            witnesses: Some(Vec::new()),
        };
        assert!(store.set_switch_statement_links(node, switch_statement.clone()));
        assert_eq!(store.switch_statement_links(node), Some(&switch_statement));

        let jsx_element = JsxElementLinks {
            jsx_flags: JsxFlags::INTRINSIC_ELEMENT,
            resolved_jsx_element_attributes_type: Some(type_id),
            jsx_namespace: Some(target),
            jsx_implicit_import_container: Some(target),
        };
        assert!(store.set_jsx_element_links(node, jsx_element.clone()));
        assert_eq!(store.jsx_element_links(node), Some(&jsx_element));

        let mapped_links = MappedSymbolLinks {
            key_type: Some(type_id),
            synthetic_origin: Some(target),
        };
        assert!(store.set_mapped_symbol_links(symbol, mapped_links.clone()));
        assert_eq!(store.mapped_symbol_links(symbol), Some(&mapped_links));

        let deferred = DeferredSymbolLinks {
            parent: Some(type_id),
            constituents: Some(vec![type_id]),
            write_constituents: Some(Vec::new()),
        };
        assert!(store.set_deferred_symbol_links(symbol, deferred.clone()));
        assert_eq!(store.deferred_symbol_links(symbol), Some(&deferred));

        let module = ModuleSymbolLinks {
            resolved_exports: Some(table),
            type_only_export_star_map: Some(HashMap::from([
                (EscapedName::source("named"), Some(node)),
                (EscapedName::source("cached-negative"), None),
            ])),
            exports_checked: true,
        };
        assert!(store.set_module_symbol_links(symbol, module.clone()));
        assert_eq!(store.module_symbol_links(symbol), Some(&module));

        let late_bound = LateBoundLinks {
            late_symbol: Some(target),
        };
        assert!(store.set_late_bound_links(symbol, late_bound.clone()));
        assert_eq!(store.late_bound_links(symbol), Some(&late_bound));

        let export_type = ExportTypeLinks {
            target: Some(target),
            originating_import: Some(node),
        };
        assert!(store.set_export_type_links(symbol, export_type.clone()));
        assert_eq!(store.export_type_links(symbol), Some(&export_type));

        let members_and_exports = MembersAndExportsLinks {
            tables: [Some(table), None],
        };
        assert!(store.set_members_and_exports_links(symbol, members_and_exports.clone()));
        assert_eq!(
            store.members_and_exports_links(symbol),
            Some(&members_and_exports)
        );

        let spread = SpreadLinks {
            left_spread: Some(target),
            right_spread: Some(target),
        };
        assert!(store.set_spread_links(symbol, spread.clone()));
        assert_eq!(store.spread_links(symbol), Some(&spread));

        let variance = VarianceLinks {
            variances: Some(vec![VarianceFlags::COVARIANT | VarianceFlags::UNRELIABLE]),
        };
        assert!(store.set_variance_links(symbol, variance.clone()));
        assert_eq!(store.variance_links(symbol), Some(&variance));

        let reverse_mapped = ReverseMappedSymbolLinks {
            property_type: Some(type_id),
            mapped_type: Some(type_id),
            constraint_type: Some(type_id),
        };
        assert!(store.set_reverse_mapped_symbol_links(symbol, reverse_mapped.clone()));
        assert_eq!(
            store.reverse_mapped_symbol_links(symbol),
            Some(&reverse_mapped)
        );

        let assignment = MarkedAssignmentSymbolLinks {
            last_assignment_pos: -1,
            has_definite_assignment: true,
        };
        assert!(store.set_marked_assignment_symbol_links(symbol, assignment.clone()));
        assert_eq!(
            store.marked_assignment_symbol_links(symbol),
            Some(&assignment)
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Exhaustive per-slot foreign provenance matrix.
    fn semantic_link_keys_and_payloads_reject_every_foreign_id_kind_atomically() {
        let first_parse = parse_source_file("const value = 1;");
        let second_parse = parse_source_file("const value = 1;");
        let first_scope = AstScope::new(FileId::new(23), &first_parse.arena);
        let second_scope = AstScope::new(FileId::new(23), &second_parse.arena);
        let first_node = first_scope.node_ref(first_parse.source_file).unwrap();
        let second_node = second_scope.node_ref(second_parse.source_file).unwrap();

        let mut first = TestStore::new();
        assert!(first.register_ast_scope(first_scope));
        let foreign_symbol = alloc_test_symbol(&mut first, "foreign");
        let foreign_type = first.alloc_type("foreign type");
        let foreign_mapper = first.alloc_mapper("foreign mapper");
        let foreign_signature = empty_signature(&mut first);
        let foreign_table = first.alloc_symbol_table();

        let mut store = TestStore::new();
        assert!(store.register_ast_scope(second_scope));
        let symbol = alloc_test_symbol(&mut store, "local");
        let local_type = store.alloc_type("local type");
        let local_table = store.alloc_symbol_table();

        assert!(!store.ensure_node_links(first_node));
        assert!(!store.ensure_symbol_node_links(first_node));
        assert!(!store.ensure_type_node_links(first_node));
        assert!(!store.ensure_assertion_links(first_node));
        assert!(!store.ensure_array_literal_links(first_node));
        assert!(!store.ensure_switch_statement_links(first_node));
        assert!(!store.ensure_jsx_element_links(first_node));
        assert!(!store.ensure_signature_links(first_node));
        assert_eq!(store.node_links(second_node), None);
        assert_eq!(store.symbol_node_links(second_node), None);
        assert_eq!(store.type_node_links(second_node), None);
        assert_eq!(store.assertion_links(second_node), None);
        assert_eq!(store.array_literal_links(second_node), None);
        assert_eq!(store.switch_statement_links(second_node), None);
        assert_eq!(store.jsx_element_links(second_node), None);
        assert_eq!(store.signature_links(second_node), None);

        assert!(!store.ensure_symbol_reference_links(foreign_symbol));
        assert!(!store.ensure_value_symbol_links(foreign_symbol));
        assert!(!store.ensure_mapped_symbol_links(foreign_symbol));
        assert!(!store.ensure_deferred_symbol_links(foreign_symbol));
        assert!(!store.ensure_alias_symbol_links(foreign_symbol));
        assert!(!store.ensure_module_symbol_links(foreign_symbol));
        assert!(!store.ensure_late_bound_links(foreign_symbol));
        assert!(!store.ensure_export_type_links(foreign_symbol));
        assert!(!store.ensure_members_and_exports_links(foreign_symbol));
        assert!(!store.ensure_type_alias_links(foreign_symbol));
        assert!(!store.ensure_declared_type_links(foreign_symbol));
        assert!(!store.ensure_spread_links(foreign_symbol));
        assert!(!store.ensure_variance_links(foreign_symbol));
        assert!(!store.ensure_reverse_mapped_symbol_links(foreign_symbol));
        assert!(!store.ensure_marked_assignment_symbol_links(foreign_symbol));

        assert!(!store.set_symbol_node_links(
            second_node,
            SymbolNodeLinks {
                resolved_symbol: Some(foreign_symbol),
            },
        ));
        assert_eq!(store.symbol_node_links(second_node), None);

        for invalid in [
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(foreign_signature),
                ..SignatureLinks::default()
            },
            SignatureLinks {
                effects_signature: EffectsSignatureState::Resolved(foreign_signature),
                ..SignatureLinks::default()
            },
            SignatureLinks {
                decorator_signature: DecoratorSignatureState::Resolved(foreign_signature),
                ..SignatureLinks::default()
            },
        ] {
            assert!(!store.set_signature_links(second_node, invalid));
            assert_eq!(store.signature_links(second_node), None);
        }

        assert!(!store.set_type_node_links(
            second_node,
            TypeNodeLinks {
                resolved_type: Some(foreign_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(!store.set_type_node_links(
            second_node,
            TypeNodeLinks {
                outer_type_parameters: Some(vec![foreign_type]),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(store.type_node_links(second_node), None);

        assert!(!store.set_assertion_links(
            second_node,
            AssertionLinks {
                expr_type: Some(foreign_type),
            },
        ));
        assert_eq!(store.assertion_links(second_node), None);

        assert!(!store.set_switch_statement_links(
            second_node,
            SwitchStatementLinks {
                switch_types: Some(vec![foreign_type]),
                ..SwitchStatementLinks::default()
            },
        ));
        assert_eq!(store.switch_statement_links(second_node), None);

        for invalid in [
            JsxElementLinks {
                resolved_jsx_element_attributes_type: Some(foreign_type),
                ..JsxElementLinks::default()
            },
            JsxElementLinks {
                jsx_namespace: Some(foreign_symbol),
                ..JsxElementLinks::default()
            },
            JsxElementLinks {
                jsx_implicit_import_container: Some(foreign_symbol),
                ..JsxElementLinks::default()
            },
        ] {
            assert!(!store.set_jsx_element_links(second_node, invalid));
            assert_eq!(store.jsx_element_links(second_node), None);
        }

        let invalid_values = [
            ValueSymbolLinks {
                resolved_type: Some(foreign_type),
                ..ValueSymbolLinks::default()
            },
            ValueSymbolLinks {
                write_type: Some(foreign_type),
                ..ValueSymbolLinks::default()
            },
            ValueSymbolLinks {
                target: Some(foreign_symbol),
                ..ValueSymbolLinks::default()
            },
            ValueSymbolLinks {
                mapper: Some(foreign_mapper),
                ..ValueSymbolLinks::default()
            },
            ValueSymbolLinks {
                name_type: Some(foreign_type),
                ..ValueSymbolLinks::default()
            },
            ValueSymbolLinks {
                containing_type: Some(foreign_type),
                ..ValueSymbolLinks::default()
            },
        ];
        for invalid in invalid_values {
            assert!(!store.set_value_symbol_links(symbol, invalid));
            assert_eq!(store.value_symbol_links(symbol), None);
        }

        for invalid in [
            MappedSymbolLinks {
                key_type: Some(foreign_type),
                ..MappedSymbolLinks::default()
            },
            MappedSymbolLinks {
                synthetic_origin: Some(foreign_symbol),
                ..MappedSymbolLinks::default()
            },
        ] {
            assert!(!store.set_mapped_symbol_links(symbol, invalid));
            assert_eq!(store.mapped_symbol_links(symbol), None);
        }

        for invalid in [
            DeferredSymbolLinks {
                parent: Some(foreign_type),
                ..DeferredSymbolLinks::default()
            },
            DeferredSymbolLinks {
                constituents: Some(vec![foreign_type]),
                ..DeferredSymbolLinks::default()
            },
            DeferredSymbolLinks {
                write_constituents: Some(vec![foreign_type]),
                ..DeferredSymbolLinks::default()
            },
        ] {
            assert!(!store.set_deferred_symbol_links(symbol, invalid));
            assert_eq!(store.deferred_symbol_links(symbol), None);
        }

        assert!(!store.set_alias_symbol_links(
            symbol,
            AliasSymbolLinks {
                immediate_target: Some(foreign_symbol),
                ..AliasSymbolLinks::default()
            },
        ));
        assert!(!store.set_alias_symbol_links(
            symbol,
            AliasSymbolLinks {
                alias_target: AliasTargetState::Resolved(foreign_symbol),
                ..AliasSymbolLinks::default()
            },
        ));
        assert!(!store.set_alias_symbol_links(
            symbol,
            AliasSymbolLinks {
                type_only_declaration: Some(first_node),
                ..AliasSymbolLinks::default()
            },
        ));
        assert_eq!(store.alias_symbol_links(symbol), None);

        for invalid in [
            ModuleSymbolLinks {
                resolved_exports: Some(foreign_table),
                ..ModuleSymbolLinks::default()
            },
            ModuleSymbolLinks {
                type_only_export_star_map: Some(HashMap::from([(
                    EscapedName::source("foreign"),
                    Some(first_node),
                )])),
                ..ModuleSymbolLinks::default()
            },
        ] {
            assert!(!store.set_module_symbol_links(symbol, invalid));
            assert_eq!(store.module_symbol_links(symbol), None);
        }

        assert!(!store.set_late_bound_links(
            symbol,
            LateBoundLinks {
                late_symbol: Some(foreign_symbol),
            },
        ));
        assert_eq!(store.late_bound_links(symbol), None);

        for invalid in [
            ExportTypeLinks {
                target: Some(foreign_symbol),
                ..ExportTypeLinks::default()
            },
            ExportTypeLinks {
                originating_import: Some(first_node),
                ..ExportTypeLinks::default()
            },
        ] {
            assert!(!store.set_export_type_links(symbol, invalid));
            assert_eq!(store.export_type_links(symbol), None);
        }

        for invalid in [
            MembersAndExportsLinks {
                tables: [Some(foreign_table), None],
            },
            MembersAndExportsLinks {
                tables: [None, Some(foreign_table)],
            },
        ] {
            assert!(!store.set_members_and_exports_links(symbol, invalid));
            assert_eq!(store.members_and_exports_links(symbol), None);
        }

        let invalid_aliases = [
            TypeAliasLinks {
                declared_type: Some(foreign_type),
                ..TypeAliasLinks::default()
            },
            TypeAliasLinks {
                type_parameters: Some(vec![foreign_type]),
                ..TypeAliasLinks::default()
            },
            TypeAliasLinks {
                instantiations: Some(HashMap::from([(
                    CacheHashKey::from_halves(3, 4),
                    foreign_type,
                )])),
                ..TypeAliasLinks::default()
            },
        ];
        for invalid in invalid_aliases {
            assert!(!store.set_type_alias_links(symbol, invalid));
            assert_eq!(store.type_alias_links(symbol), None);
        }

        assert!(!store.set_declared_type_links(
            symbol,
            DeclaredTypeLinks {
                declared_type: Some(foreign_type),
                ..DeclaredTypeLinks::default()
            },
        ));
        assert_eq!(store.declared_type_links(symbol), None);

        for invalid in [
            SpreadLinks {
                left_spread: Some(foreign_symbol),
                ..SpreadLinks::default()
            },
            SpreadLinks {
                right_spread: Some(foreign_symbol),
                ..SpreadLinks::default()
            },
        ] {
            assert!(!store.set_spread_links(symbol, invalid));
            assert_eq!(store.spread_links(symbol), None);
        }

        for invalid in [
            ReverseMappedSymbolLinks {
                property_type: Some(foreign_type),
                ..ReverseMappedSymbolLinks::default()
            },
            ReverseMappedSymbolLinks {
                mapped_type: Some(foreign_type),
                ..ReverseMappedSymbolLinks::default()
            },
            ReverseMappedSymbolLinks {
                constraint_type: Some(foreign_type),
                ..ReverseMappedSymbolLinks::default()
            },
        ] {
            assert!(!store.set_reverse_mapped_symbol_links(symbol, invalid));
            assert_eq!(store.reverse_mapped_symbol_links(symbol), None);
        }

        let module_baseline = ModuleSymbolLinks {
            resolved_exports: Some(local_table),
            type_only_export_star_map: Some(HashMap::from([(
                EscapedName::source("local"),
                Some(second_node),
            )])),
            exports_checked: true,
        };
        assert!(store.set_module_symbol_links(symbol, module_baseline.clone()));
        assert!(!store.set_module_symbol_links(
            symbol,
            ModuleSymbolLinks {
                resolved_exports: Some(foreign_table),
                ..ModuleSymbolLinks::default()
            },
        ));
        assert_eq!(store.module_symbol_links(symbol), Some(&module_baseline));

        let baseline = ValueSymbolLinks {
            resolved_type: Some(local_type),
            ..ValueSymbolLinks::default()
        };
        assert!(store.set_value_symbol_links(symbol, baseline.clone()));
        assert!(!store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(foreign_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(store.value_symbol_links(symbol), Some(&baseline));
    }

    #[test]
    fn semantic_store_owns_and_validates_the_type_resolution_stack() {
        let parsed = parse_source_file("const first = 1; const second = 2;");
        let scope = AstScope::new(FileId::new(24), &parsed.arena);
        let node = scope.node_ref(parsed.source_file).unwrap();
        let mut store = CanonicalTestStore::new();
        assert!(store.register_ast_scope(scope));
        let first = alloc_test_symbol(&mut store, "first");
        let second = alloc_test_symbol(&mut store, "second");
        let type_id = store.alloc_type_parameter(None).unwrap();
        let intrinsic = store
            .alloc_intrinsic_type(TypeFlags::NUMBER, "number")
            .unwrap();
        let signature = empty_signature(&mut store);

        let first_target = TypeResolutionTarget::Symbol(first);
        let second_target = TypeResolutionTarget::Symbol(second);
        assert_eq!(
            store.push_type_resolution(first_target, TypeSystemPropertyName::Type),
            Ok(true)
        );
        assert_eq!(
            store.push_type_resolution(second_target, TypeSystemPropertyName::Type),
            Ok(true)
        );
        assert_eq!(
            store.push_type_resolution(first_target, TypeSystemPropertyName::Type),
            Ok(false)
        );
        assert_eq!(store.type_resolution_len(), 2);
        assert_eq!(store.pop_type_resolution(), Some(false));
        assert_eq!(store.pop_type_resolution(), Some(false));
        assert!(store.type_resolution_is_empty());

        for (target, property) in [
            (
                TypeResolutionTarget::Type(type_id),
                TypeSystemPropertyName::ResolvedBaseConstraint,
            ),
            (
                TypeResolutionTarget::Signature(signature),
                TypeSystemPropertyName::ResolvedReturnType,
            ),
            (
                TypeResolutionTarget::Node(node),
                TypeSystemPropertyName::InitializerIsUndefined,
            ),
        ] {
            assert_eq!(store.push_type_resolution(target, property), Ok(true));
            assert_eq!(store.pop_type_resolution(), Some(true));
        }

        assert!(
            store
                .push_type_resolution(
                    TypeResolutionTarget::Symbol(first),
                    TypeSystemPropertyName::ResolvedReturnType,
                )
                .is_err()
        );
        assert!(
            store
                .push_type_resolution(
                    TypeResolutionTarget::Type(intrinsic),
                    TypeSystemPropertyName::ResolvedBaseConstraint,
                )
                .is_err()
        );
        assert!(store.type_resolution_is_empty());
    }

    #[test]
    fn type_resolution_cycle_scan_observes_live_owned_link_state() {
        let mut store = CanonicalTestStore::new();
        let first = alloc_test_symbol(&mut store, "first");
        let second = alloc_test_symbol(&mut store, "second");
        let resolved_type = store.alloc_type_parameter(None).unwrap();
        let first_target = TypeResolutionTarget::Symbol(first);
        let second_target = TypeResolutionTarget::Symbol(second);

        assert_eq!(
            store.push_type_resolution(first_target, TypeSystemPropertyName::Type),
            Ok(true)
        );
        assert_eq!(
            store.push_type_resolution(second_target, TypeSystemPropertyName::Type),
            Ok(true)
        );
        assert_eq!(
            store.value_symbol_links(first),
            Some(&ValueSymbolLinks::default()),
            "the live probe must preserve upstream LinkStore.Get allocation"
        );

        // This cache write occurs after both stack entries were pushed. The
        // next reverse scan must observe it live and stop before treating the
        // older `first` entry as a cycle.
        assert!(store.set_value_symbol_links(
            second,
            ValueSymbolLinks {
                resolved_type: Some(resolved_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            store.push_type_resolution(first_target, TypeSystemPropertyName::Type),
            Ok(true)
        );
        assert_eq!(store.type_resolution_len(), 3);
        assert_eq!(store.pop_type_resolution(), Some(true));
        assert_eq!(store.pop_type_resolution(), Some(true));
        assert_eq!(store.pop_type_resolution(), Some(true));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Exhaustive pinned ten-property storage matrix.
    fn live_property_probe_covers_every_pinned_property_storage_location() {
        let parsed = parse_source_file("const value = 1;");
        let scope = AstScope::new(FileId::new(26), &parsed.arena);
        let node = scope.node_ref(parsed.source_file).unwrap();
        let mut store = CanonicalTestStore::new();
        assert!(store.register_ast_scope(scope));

        let cached_type = store.alloc_type_parameter(None).unwrap();
        let value_symbol = alloc_test_symbol(&mut store, "value");
        assert!(store.set_value_symbol_links(
            value_symbol,
            ValueSymbolLinks {
                resolved_type: Some(cached_type),
                write_type: Some(cached_type),
                ..ValueSymbolLinks::default()
            },
        ));

        let alias_symbol = alloc_test_symbol(&mut store, "alias");
        assert!(store.set_alias_symbol_links(
            alias_symbol,
            AliasSymbolLinks {
                alias_target: AliasTargetState::Unknown,
                ..AliasSymbolLinks::default()
            },
        ));

        let type_alias_symbol = alloc_test_symbol(&mut store, "TypeAlias");
        assert!(store.set_type_alias_links(
            type_alias_symbol,
            TypeAliasLinks {
                declared_type: Some(cached_type),
                ..TypeAliasLinks::default()
            },
        ));

        assert!(store.set_node_links(
            node,
            NodeLinks {
                flags: crate::semantic::NodeCheckFlags::INITIALIZER_IS_UNDEFINED_COMPUTED,
                ..NodeLinks::default()
            },
        ));

        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(cached_type),
                None,
                0,
            )
            .unwrap();

        let reference = store
            .alloc_type_reference(ObjectFlags::REFERENCE, None)
            .unwrap();
        assert!(store.set_type_reference_resolution(reference, None, Some(Vec::new())));
        let interface = store
            .alloc_interface_type(ObjectFlags::INTERFACE, None)
            .unwrap();
        assert!(store.set_interface_base_resolution(
            interface,
            true,
            Some(cached_type),
            Some(Vec::new()),
        ));
        assert!(store.set_resolved_base_constraint(cached_type, Some(cached_type)));

        for (target, property) in [
            (
                TypeResolutionTarget::Symbol(value_symbol),
                TypeSystemPropertyName::Type,
            ),
            (
                TypeResolutionTarget::Symbol(value_symbol),
                TypeSystemPropertyName::WriteType,
            ),
            (
                TypeResolutionTarget::Symbol(type_alias_symbol),
                TypeSystemPropertyName::DeclaredType,
            ),
            (
                TypeResolutionTarget::Symbol(alias_symbol),
                TypeSystemPropertyName::AliasTarget,
            ),
            (
                TypeResolutionTarget::Type(reference),
                TypeSystemPropertyName::ResolvedTypeArguments,
            ),
            (
                TypeResolutionTarget::Type(interface),
                TypeSystemPropertyName::ResolvedBaseTypes,
            ),
            (
                TypeResolutionTarget::Type(interface),
                TypeSystemPropertyName::ResolvedBaseConstructorType,
            ),
            (
                TypeResolutionTarget::Type(cached_type),
                TypeSystemPropertyName::ResolvedBaseConstraint,
            ),
            (
                TypeResolutionTarget::Signature(signature),
                TypeSystemPropertyName::ResolvedReturnType,
            ),
            (
                TypeResolutionTarget::Node(node),
                TypeSystemPropertyName::InitializerIsUndefined,
            ),
        ] {
            assert_canonical_property_present(&mut store, target, property);
        }
    }

    #[test]
    fn type_resolution_stack_rejects_equal_local_foreign_targets_without_mutation() {
        let first_parse = parse_source_file("const value = 1;");
        let second_parse = parse_source_file("const value = 1;");
        let first_scope = AstScope::new(FileId::new(25), &first_parse.arena);
        let second_scope = AstScope::new(FileId::new(25), &second_parse.arena);
        let first_node = first_scope.node_ref(first_parse.source_file).unwrap();
        let second_node = second_scope.node_ref(second_parse.source_file).unwrap();

        let mut first = CanonicalTestStore::new();
        assert!(first.register_ast_scope(first_scope));
        let foreign_symbol = alloc_test_symbol(&mut first, "value");
        let foreign_type = first.alloc_type_parameter(None).unwrap();
        let foreign_signature = empty_signature(&mut first);

        let mut store = CanonicalTestStore::new();
        assert!(store.register_ast_scope(second_scope));
        let local_symbol = alloc_test_symbol(&mut store, "value");
        let local_type = store.alloc_type_parameter(None).unwrap();
        let local_signature = empty_signature(&mut store);

        assert_eq!(foreign_symbol.get(), local_symbol.get());
        assert_eq!(foreign_type.get(), local_type.get());
        assert_eq!(foreign_signature.get(), local_signature.get());
        assert_eq!(first_node.file, second_node.file);
        assert_eq!(first_node.node, second_node.node);
        assert_ne!(first_node.arena, second_node.arena);

        let foreign_targets = [
            (
                TypeResolutionTarget::Symbol(foreign_symbol),
                TypeSystemPropertyName::Type,
            ),
            (
                TypeResolutionTarget::Type(foreign_type),
                TypeSystemPropertyName::ResolvedBaseConstraint,
            ),
            (
                TypeResolutionTarget::Signature(foreign_signature),
                TypeSystemPropertyName::ResolvedReturnType,
            ),
            (
                TypeResolutionTarget::Node(first_node),
                TypeSystemPropertyName::InitializerIsUndefined,
            ),
        ];
        for (target, property) in foreign_targets {
            assert!(store.push_type_resolution(target, property).is_err());
            assert!(
                store
                    .find_type_resolution_cycle_start(target, property)
                    .is_err()
            );
            assert!(store.type_resolution_is_empty());
        }

        for (target, property) in [
            (
                TypeResolutionTarget::Symbol(local_symbol),
                TypeSystemPropertyName::AliasTarget,
            ),
            (
                TypeResolutionTarget::Type(local_type),
                TypeSystemPropertyName::ResolvedBaseConstraint,
            ),
            (
                TypeResolutionTarget::Signature(local_signature),
                TypeSystemPropertyName::ResolvedReturnType,
            ),
            (
                TypeResolutionTarget::Node(second_node),
                TypeSystemPropertyName::InitializerIsUndefined,
            ),
        ] {
            assert_eq!(store.push_type_resolution(target, property), Ok(true));
            assert_eq!(store.pop_type_resolution(), Some(true));
        }
    }

    #[test]
    fn type_resolution_boundaries_are_store_branded_single_use_and_lifo() {
        let mut first = CanonicalTestStore::new();
        let first_symbol = alloc_test_symbol(&mut first, "first");
        let second_symbol = alloc_test_symbol(&mut first, "second");
        let third_symbol = alloc_test_symbol(&mut first, "third");
        assert_eq!(
            first.push_type_resolution(
                TypeResolutionTarget::Symbol(first_symbol),
                TypeSystemPropertyName::Type,
            ),
            Ok(true)
        );
        let outer = first.reset_type_resolution_start();
        assert_eq!(first.type_resolution_start(), 1);
        assert_eq!(first.pop_type_resolution(), None);
        assert_eq!(
            first.push_type_resolution(
                TypeResolutionTarget::Symbol(second_symbol),
                TypeSystemPropertyName::Type,
            ),
            Ok(true)
        );
        let inner = first.reset_type_resolution_start();
        assert_eq!(first.type_resolution_start(), 2);
        assert_eq!(first.pop_type_resolution(), None);
        assert_eq!(
            first.push_type_resolution(
                TypeResolutionTarget::Symbol(third_symbol),
                TypeSystemPropertyName::Type,
            ),
            Ok(true)
        );

        let outer = first
            .restore_type_resolution_start(outer)
            .expect_err("outer token cannot restore before inner token");
        assert_eq!(first.type_resolution_start(), 2);
        let inner = first
            .restore_type_resolution_start(inner)
            .expect_err("inner token cannot restore while its entry is live");
        assert_eq!(first.type_resolution_start(), 2);
        assert_eq!(first.pop_type_resolution(), Some(true));
        assert!(first.restore_type_resolution_start(inner).is_ok());
        assert_eq!(first.type_resolution_start(), 1);
        let outer = first
            .restore_type_resolution_start(outer)
            .expect_err("outer token cannot restore while its entry is live");
        assert_eq!(first.type_resolution_start(), 1);
        assert_eq!(first.pop_type_resolution(), Some(true));
        assert!(first.restore_type_resolution_start(outer).is_ok());
        assert_eq!(first.type_resolution_start(), 0);

        assert_eq!(first.pop_type_resolution(), Some(true));
        assert!(first.type_resolution_is_empty());

        // Fresh stores both allocate boundary serial 1. Branding, rather than
        // an incidental serial mismatch, must reject the crossed token.
        let mut left = CanonicalTestStore::new();
        let mut right = CanonicalTestStore::new();
        let left_token = left.reset_type_resolution_start();
        let right_token = right.reset_type_resolution_start();
        let left_token = right
            .restore_type_resolution_start(left_token)
            .expect_err("another semantic store must reject an equal-serial token");
        assert!(right.restore_type_resolution_start(right_token).is_ok());
        assert!(left.restore_type_resolution_start(left_token).is_ok());
    }
}
