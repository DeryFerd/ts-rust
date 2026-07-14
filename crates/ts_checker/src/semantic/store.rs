//! Aggregate ownership and provenance validation for canonical semantic data.

use std::collections::BTreeMap;

use ts_ast::{FileId, NodeArena, NodeArenaId, NodeId, NodeRef};

use super::{
    ids::{
        IndexInfoId, SemanticStoreId, SemanticSymbolId, SignatureId, TypeId, TypeMapperId,
        TypePredicateId, TypedArena, allocate_semantic_store_id,
    },
    signatures::{
        CompositeSignature, IndexInfo, IndexInfoArena, Signature, SignatureArena, SignatureFlags,
        TupleElementInfo, TupleMetadata, TypePredicate, TypePredicateArena, TypePredicateKind,
    },
};

/// Snapshot of one Program file's AST identity and allocated node range.
///
/// The constructor captures the arena identity and current node count from an
/// actual [`NodeArena`]. It cannot promise persistence across Program rebuilds
/// or arena replacement, and nodes allocated after this snapshot require a
/// refreshed registration.
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
    pub const fn file(&self) -> FileId {
        self.file
    }

    #[must_use]
    pub const fn arena(&self) -> NodeArenaId {
        self.arena
    }

    #[must_use]
    pub const fn node_count(&self) -> usize {
        self.node_count
    }

    /// Creates a branded reference only for a node present in this snapshot.
    #[must_use]
    pub fn node_ref(&self, node: NodeId) -> Option<NodeRef> {
        (node.index() < self.node_count).then(|| NodeRef::new(self.arena, self.file, node))
    }

    fn contains(&self, node: NodeRef) -> bool {
        node.is_for(self.arena, self.file) && node.node.index() < self.node_count
    }
}

/// Sole allocator and owner of one canonical program's semantic graph.
///
/// Every semantic handle is branded with this store's identity. Record writes
/// validate all incoming handles and AST references before mutating storage.
#[derive(Debug)]
pub struct SemanticStore<TypePayload, SymbolPayload, MapperPayload> {
    id: SemanticStoreId,
    types: TypedArena<TypeId, TypePayload>,
    symbols: TypedArena<SemanticSymbolId, SymbolPayload>,
    mappers: TypedArena<TypeMapperId, MapperPayload>,
    signatures: SignatureArena,
    predicates: TypePredicateArena,
    index_infos: IndexInfoArena,
    ast_scopes: BTreeMap<FileId, AstScope>,
    ast_files: BTreeMap<NodeArenaId, FileId>,
}

impl<TypePayload, SymbolPayload, MapperPayload> Default
    for SemanticStore<TypePayload, SymbolPayload, MapperPayload>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<TypePayload, SymbolPayload, MapperPayload>
    SemanticStore<TypePayload, SymbolPayload, MapperPayload>
{
    /// Creates an empty store with a fresh process-local identity.
    ///
    /// # Panics
    ///
    /// Panics if the process has exhausted semantic-store identities.
    #[must_use]
    pub fn new() -> Self {
        let id = allocate_semantic_store_id();
        Self {
            id,
            types: TypedArena::new(id),
            symbols: TypedArena::new(id),
            mappers: TypedArena::new(id),
            signatures: SignatureArena::new(id),
            predicates: TypePredicateArena::new(id),
            index_infos: IndexInfoArena::new(id),
            ast_scopes: BTreeMap::new(),
            ast_files: BTreeMap::new(),
        }
    }

    #[must_use]
    pub const fn id(&self) -> SemanticStoreId {
        self.id
    }

    /// Registers a safe AST snapshot for semantic references.
    ///
    /// Re-registering the same file/arena pair refreshes its node bound.
    /// Reusing either identity with a different counterpart is rejected before
    /// either registration map is modified.
    pub fn register_ast_scope(&mut self, scope: AstScope) -> bool {
        if self
            .ast_scopes
            .get(&scope.file)
            .is_some_and(|registered| registered.arena != scope.arena)
            || self
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

    /// Allocates a canonical type payload.
    ///
    /// # Panics
    ///
    /// Panics before mutation if the local `u32` identity space is exhausted.
    pub fn alloc_type(&mut self, payload: TypePayload) -> TypeId {
        self.types.alloc(payload)
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

    /// Allocates a canonical semantic symbol payload.
    ///
    /// # Panics
    ///
    /// Panics before mutation if the local `u32` identity space is exhausted.
    pub fn alloc_symbol(&mut self, payload: SymbolPayload) -> SemanticSymbolId {
        self.symbols.alloc(payload)
    }

    #[must_use]
    pub fn symbol_payload(&self, id: SemanticSymbolId) -> Option<&SymbolPayload> {
        self.symbols.get(id)
    }

    #[must_use]
    pub fn symbol_len(&self) -> usize {
        self.symbols.len()
    }

    /// Allocates a canonical type-mapper payload.
    ///
    /// # Panics
    ///
    /// Panics before mutation if the local `u32` identity space is exhausted.
    pub fn alloc_mapper(&mut self, payload: MapperPayload) -> TypeMapperId {
        self.mappers.alloc(payload)
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

    fn valid_optional_type(&self, id: Option<TypeId>) -> bool {
        id.is_none_or(|id| self.types.get(id).is_some())
    }

    fn valid_symbols(&self, ids: &[SemanticSymbolId]) -> bool {
        ids.iter().all(|id| self.symbols.get(*id).is_some())
    }

    fn valid_optional_symbol(&self, id: Option<SemanticSymbolId>) -> bool {
        id.is_none_or(|id| self.symbols.get(id).is_some())
    }

    fn valid_optional_mapper(&self, id: Option<TypeMapperId>) -> bool {
        id.is_none_or(|id| self.mappers.get(id).is_some())
    }

    fn valid_optional_signature(&self, id: Option<SignatureId>) -> bool {
        id.is_none_or(|id| self.signatures.get(id).is_some())
    }

    fn valid_optional_predicate(&self, id: Option<TypePredicateId>) -> bool {
        id.is_none_or(|id| self.predicates.get(id).is_some())
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeRef};
    use ts_parser::parse_source_file;

    use super::{AstScope, SemanticStore};
    use crate::semantic::signatures::{ElementFlags, SignatureFlags, TypePredicateKind};

    type TestStore = SemanticStore<&'static str, &'static str, &'static str>;

    fn empty_signature(store: &mut TestStore) -> crate::semantic::SignatureId {
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
        let symbol = store.alloc_symbol(payload);
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

        let signature_count = second.store.signature_len();
        assert_eq!(
            second.store.alloc_signature(
                SignatureFlags::NONE,
                None,
                vec![first.type_id],
                Some(first.symbol),
                vec![second.symbol],
                Some(second.type_id),
                None,
                0,
            ),
            None
        );
        assert_eq!(second.store.signature_len(), signature_count);

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
        assert_eq!(second.store.index_info_len(), index_count);
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
        assert!(!store.set_signature_resolved_return_type(target, Some(first.type_id)));
        assert!(!store.set_signature_isolated_type(target, Some(first.type_id)));
        assert!(!store.set_signature_resolved_type_predicate(target, Some(first.predicate)));
        assert!(!store.set_signature_this_parameter(target, Some(first.symbol)));
        assert!(!store.set_signature_type_parameters(target, vec![first.type_id]));
        assert!(!store.set_signature_composite(target, foreign_composite));
        assert_signature_unmodified(store, target);

        assert_eq!(store.type_payload(first.type_id), None);
        assert_eq!(store.symbol_payload(first.symbol), None);
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
        assert_eq!(store.index_info_len(), index_count);
        assert_eq!(
            store.create_tuple_element_info(ElementFlags::REQUIRED, Some(first_ref)),
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
        let this_parameter = store.alloc_symbol("this");
        let parameter = store.alloc_symbol("value");
        let replacement_this = store.alloc_symbol("replacement this");
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
}
