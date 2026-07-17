//! Aggregate ownership and provenance validation for canonical semantic data.

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    num::NonZeroU32,
};

use ts_ast::{FileId, NodeArena, NodeArenaId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    AstScope, CheckFlags, EscapedName, SemanticStoreId, SemanticSymbolId, SymbolData, SymbolFlags,
    SymbolStore, SymbolTableId,
    semantic::{PreparedSymbolTable, Symbol, SymbolTable},
};
use ts_parser::{IsolatedEntityName, parse_isolated_entity_name};

use super::{
    array_types::CanonicalArrayTargets,
    bootstrap::IntrinsicBootstrap,
    derived_types::DerivedTypeCaches,
    ids::{
        ConditionalRootId, IndexInfoId, SignatureId, TypeAliasId, TypeId, TypeMapperId,
        TypePredicateId, TypedArena,
    },
    links::{
        AliasSymbolLinks, AliasTargetState, ArrayLiteralLinks, AssertionLinks, CheckerLinkStores,
        ContainingSymbolLinks, DeclaredTypeLinks, DecoratorSignatureState, DeferredSymbolLinks,
        EffectsSignatureState, EntityNameNode, EntityNameRef, EnumMemberLinks, ExportTypeLinks,
        ExtendedContainersState, JsxElementLinks, LateBoundLinks, MappedSymbolLinks,
        MarkedAssignmentSymbolLinks, MembersAndExportsLinks, ModuleSymbolLinks, NodeLinks,
        OptionalSymbolSequence, ResolvedSignatureState, ReverseMappedSymbolLinks, SignatureLinks,
        SourceFileLinks, SourceFileRef, SpreadLinks, SwitchStatementLinks, SymbolNodeLinks,
        SymbolReferenceLinks, TypeAliasLinks, TypeNodeLinks, TypeResolutionBoundary,
        TypeResolutionCheckpoint, TypeResolutionStack, TypeResolutionTarget,
        TypeResolutionTargetError, TypeSystemPropertyName, ValueSymbolLinks, VarianceLinks,
    },
    relation::{RelationCaches, RelationComparisonResult, RelationKind, RelationStateSnapshot},
    signatures::{
        CompositeSignature, IndexInfo, IndexInfoArena, Signature, SignatureArena, SignatureFlags,
        TupleElementInfo, TupleMetadata, TypePredicate, TypePredicateArena, TypePredicateKind,
    },
    source_callables::SourceCallableTypeParameterSyntaxProof,
    type_records::{CacheHashKey, ConditionalRoot, TypeAlias, TypeData, TypeRecord, type_list_key},
};

#[derive(Debug)]
enum PreparedEntityName {
    Identifier(String),
    QualifiedName { left: Box<Self>, right: String },
}

impl PreparedEntityName {
    fn node_count(&self) -> usize {
        match self {
            Self::Identifier(_) => 1,
            Self::QualifiedName { left, .. } => left.node_count() + 2,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceNodeFacts {
    kind: SyntaxKind,
    parent: Option<NodeId>,
    exported: bool,
    signature_links_eligible: bool,
}

#[derive(Debug)]
struct CachedSignatureEntry {
    type_arguments: Box<[TypeId]>,
    instantiated: SignatureId,
}

/// Exact lookup state for pinned checker `cachedSignatures`. The hash remains
/// the upstream key, while the retained ordered arguments make a rare hash
/// collision observable and fail-closed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CachedSignatureLookup {
    Missing,
    Hit(SignatureId),
    HashCollision(SignatureId),
    Invalid,
}

/// Source syntax family that owns one exact callable value object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableFamily {
    FunctionDeclaration,
    ArrowFunction,
}

/// Whether a source callable's return is owned by exact annotation syntax or
/// is inferred from its checked body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableReturnProvenance {
    Annotated,
    Inferred,
}

impl SourceCallableFamily {
    pub(super) const fn syntax_kind(self) -> SyntaxKind {
        match self {
            Self::FunctionDeclaration => SyntaxKind::FunctionDeclaration,
            Self::ArrowFunction => SyntaxKind::ArrowFunction,
        }
    }
}

/// Immutable owner tuple distinguishing source values from `FunctionType` nodes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableProvenance {
    pub(super) family: SourceCallableFamily,
    pub(super) declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) owner_parent: Option<SemanticSymbolId>,
    pub(super) export_local: Option<SemanticSymbolId>,
    pub(super) signature: SignatureId,
    pub(super) return_provenance: SourceCallableReturnProvenance,
    /// Exact global-array targets installed while this callable was planned.
    /// Store-only validation uses this retained capability for inferred
    /// structured returns without consulting ambient checker state.
    pub(super) array_targets: Option<CanonicalArrayTargets>,
    /// Exact declared identity named by a naked generic return annotation.
    /// Fixed keyword returns and non-generic/contextual callables retain None.
    pub(super) generic_return_type_parameter: Option<TypeId>,
    /// The annotation that contextually typed an inferred source arrow.
    ///
    /// Annotated source callables retain `None` and instead own an exact
    /// return-annotation edge. Contextual arrows retain both this target and
    /// `contextual_variable` so warm validation can distinguish the target
    /// identity from the arrow expression's independently inferred callable.
    pub(super) contextual_target: Option<TypeId>,
    pub(super) contextual_variable: Option<SemanticSymbolId>,
}

/// Immutable syntax-plan edge for the admitted direct-interface heritage slice.
///
/// `resolved_base_types` remains the pinned semantic cache, while this separate
/// provenance lets store-only consumers prove that the cached edge still names
/// the exact base selected by source planning.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DirectInterfaceHeritageProvenance {
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) base_symbol: SemanticSymbolId,
    pub(super) base_type: TypeId,
}

/// One declaration-order row for an exact source generic signature.
///
/// Both the binder symbol and canonical type identity are retained on purpose:
/// warm validation must prove that an ordered signature edge still belongs to
/// the exact `TypeParameterDeclaration`, not merely to an equal-looking node
/// or a type parameter at the same vector position.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableTypeParameterProvenance {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) type_parameter: TypeId,
    pub(super) constraint: Option<NodeRef>,
    pub(super) default_type: Option<NodeRef>,
}

/// Fully resolved payload staged before publishing source generic metadata.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ResolvedSourceCallableTypeParameter {
    pub(super) provenance: SourceCallableTypeParameterProvenance,
    /// The declared constraint, or the canonical `no_constraint_type`.
    pub(super) constraint: TypeId,
    /// The declared default, or the canonical `no_constraint_type`.
    pub(super) default_type: TypeId,
}

/// Dependency-closed inputs for publishing one source generic callable.
///
/// The opaque syntax proof is produced only by source planning. The store
/// revalidates every semantic edge against it before allocating the callable
/// object or signature, then commits the complete shell without fallible
/// publication steps.
#[derive(Debug)]
pub(super) struct PreparedSourceGenericCallablePublication<'a> {
    pub(super) syntax: &'a SourceCallableTypeParameterSyntaxProof,
    pub(super) family: SourceCallableFamily,
    pub(super) declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) owner_parent: Option<SemanticSymbolId>,
    pub(super) export_local: Option<SemanticSymbolId>,
    pub(super) type_parameters: Vec<ResolvedSourceCallableTypeParameter>,
    pub(super) parameters: Vec<SemanticSymbolId>,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) return_annotation: NodeRef,
    pub(super) return_null_literal_identity: bool,
    pub(super) generic_return_type_parameter: Option<TypeId>,
    pub(super) array_targets: Option<CanonicalArrayTargets>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceTypeParameterResolutionState {
    Cold,
    Warm,
}

/// Branded identities owned by the one canonical mutable empty tuple graph.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CanonicalEmptyTupleProvenance {
    pub(super) type_: TypeId,
    pub(super) this_type: TypeId,
    pub(super) declared_members: SymbolTableId,
    pub(super) length_symbol: SemanticSymbolId,
}

/// Exact target-cache key used by pinned `getTupleTargetType`.
///
/// Element types deliberately do not participate. Labels retain their arena-
/// branded declaration identity, matching upstream's `writeNode` key segment.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) struct CanonicalTupleTargetKey {
    pub(super) element_infos: Vec<TupleElementInfo>,
    pub(super) readonly: bool,
}

/// Branded identities owned by one synthesized tuple target graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CanonicalTupleTargetProvenance {
    pub(super) target: TypeId,
    pub(super) type_parameters: Vec<TypeId>,
    pub(super) this_type: TypeId,
    pub(super) declared_members: SymbolTableId,
    pub(super) element_symbols: Vec<SemanticSymbolId>,
    pub(super) length_symbol: SemanticSymbolId,
    pub(super) length_type: TypeId,
    pub(super) length_constituents: Vec<TypeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceNodeParent {
    Root,
    Parent(NodeRef),
}

/// A merged-symbol redirect rejected before the redirect map changes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(dead_code)] // Mutated only by the sibling merge substrate.
pub(super) enum MergedSymbolRecordError {
    InvalidTarget(SemanticSymbolId),
    InvalidSource(SemanticSymbolId),
    SelfRedirect(SemanticSymbolId),
    RedirectCycle {
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    },
}

impl std::fmt::Display for MergedSymbolRecordError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidTarget(target) => {
                write!(
                    formatter,
                    "merged-symbol target {target:?} is not store-owned"
                )
            }
            Self::InvalidSource(source) => {
                write!(
                    formatter,
                    "merged-symbol source {source:?} is not store-owned"
                )
            }
            Self::SelfRedirect(symbol) => {
                write!(
                    formatter,
                    "merged symbol {symbol:?} cannot redirect to itself"
                )
            }
            Self::RedirectCycle { source, target } => write!(
                formatter,
                "merged-symbol redirect from {source:?} to {target:?} would create a cycle"
            ),
        }
    }
}

impl std::error::Error for MergedSymbolRecordError {}

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
    entity_names: Vec<EntityNameNode>,
    source_files: BTreeMap<FileId, SourceFileRef>,
    source_files_by_arena: BTreeMap<NodeArenaId, SourceFileRef>,
    source_node_facts: BTreeMap<NodeArenaId, Vec<Option<SourceNodeFacts>>>,
    type_alias_declared_type_owners: HashMap<TypeId, HashSet<SemanticSymbolId>>,
    merged_symbols: HashMap<SemanticSymbolId, SemanticSymbolId>,
    links: CheckerLinkStores,
    declared_types_in_progress: HashSet<SemanticSymbolId>,
    function_type_provenance: HashSet<TypeId>,
    declared_call_set_provenance: HashSet<TypeId>,
    declared_call_set_types_by_signature: HashMap<SignatureId, TypeId>,
    direct_interface_heritage_provenance: HashMap<TypeId, DirectInterfaceHeritageProvenance>,
    source_callable_provenance: HashMap<TypeId, SourceCallableProvenance>,
    source_callable_types_by_declaration: HashMap<NodeRef, TypeId>,
    source_callable_types_by_owner: HashMap<SemanticSymbolId, TypeId>,
    source_callable_types_by_signature: HashMap<SignatureId, TypeId>,
    source_callable_type_parameters:
        HashMap<SignatureId, Box<[SourceCallableTypeParameterProvenance]>>,
    /// Pinned checker `cachedSignatures`, keyed by generic target and the
    /// ordered type-argument hash.
    cached_signatures: HashMap<(SignatureId, CacheHashKey), CachedSignatureEntry>,
    function_signature_return_annotations: HashMap<SignatureId, (NodeRef, bool)>,
    callable_signature_parameter_types: HashMap<SignatureId, Vec<TypeId>>,
    circular_return_signatures: HashMap<SignatureId, TypeId>,
    canonical_tuple_targets: HashMap<CanonicalTupleTargetKey, CanonicalTupleTargetProvenance>,
    canonical_empty_tuple: Option<CanonicalEmptyTupleProvenance>,
    type_resolutions: TypeResolutionStack,
    relations: RelationCaches,
    pub(super) derived_types: DerivedTypeCaches,
    pub(super) intrinsic_bootstrap: Option<IntrinsicBootstrap>,
    claimed_strict_builtin_iterator_return: Option<bool>,
    claimed_strict_function_types: Option<bool>,
    pub(super) union_cache_needs_validation: bool,
    #[cfg(test)]
    pub(super) union_cache_validation_scans: usize,
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
            entity_names: Vec::new(),
            source_files: BTreeMap::new(),
            source_files_by_arena: BTreeMap::new(),
            source_node_facts: BTreeMap::new(),
            type_alias_declared_type_owners: HashMap::new(),
            merged_symbols: HashMap::new(),
            links: CheckerLinkStores::default(),
            declared_types_in_progress: HashSet::new(),
            function_type_provenance: HashSet::new(),
            declared_call_set_provenance: HashSet::new(),
            declared_call_set_types_by_signature: HashMap::new(),
            direct_interface_heritage_provenance: HashMap::new(),
            source_callable_provenance: HashMap::new(),
            source_callable_types_by_declaration: HashMap::new(),
            source_callable_types_by_owner: HashMap::new(),
            source_callable_types_by_signature: HashMap::new(),
            source_callable_type_parameters: HashMap::new(),
            cached_signatures: HashMap::new(),
            function_signature_return_annotations: HashMap::new(),
            callable_signature_parameter_types: HashMap::new(),
            circular_return_signatures: HashMap::new(),
            canonical_tuple_targets: HashMap::new(),
            canonical_empty_tuple: None,
            type_resolutions: TypeResolutionStack::new(id),
            relations: RelationCaches::default(),
            derived_types: DerivedTypeCaches::default(),
            intrinsic_bootstrap: None,
            claimed_strict_builtin_iterator_return: None,
            claimed_strict_function_types: None,
            union_cache_needs_validation: false,
            #[cfg(test)]
            union_cache_validation_scans: 0,
        }
    }

    #[must_use]
    pub fn id(&self) -> SemanticStoreId {
        self.symbols.id()
    }

    /// Claims the checker-global iterator-return mode for this store's query
    /// session. The first claim configures the session; later claims must
    /// match and never rewrite the established mode.
    pub(super) fn claim_strict_builtin_iterator_return(
        &mut self,
        requested: bool,
    ) -> Result<(), bool> {
        match self.claimed_strict_builtin_iterator_return {
            Some(established) if established != requested => Err(established),
            Some(_) => Ok(()),
            None => {
                self.claimed_strict_builtin_iterator_return = Some(requested);
                Ok(())
            }
        }
    }

    #[cfg(test)]
    pub(super) const fn claimed_strict_builtin_iterator_return(&self) -> Option<bool> {
        self.claimed_strict_builtin_iterator_return
    }

    /// Claims the checker-global function-parameter variance mode for this
    /// store's relation caches. Relation keys intentionally omit compiler
    /// options, so every option-aware relation query in one store must agree
    /// with the first claim.
    pub(super) fn claim_strict_function_types(&mut self, requested: bool) -> Result<(), bool> {
        match self.claimed_strict_function_types {
            Some(established) if established != requested => Err(established),
            Some(_) => Ok(()),
            None => {
                self.claimed_strict_function_types = Some(requested);
                Ok(())
            }
        }
    }

    /// Returns the immutable function-variance claim without establishing it.
    /// Legacy relation sessions use this to avoid reading option-aware cache
    /// entries that their API did not explicitly admit.
    pub(super) const fn claimed_strict_function_types(&self) -> Option<bool> {
        self.claimed_strict_function_types
    }

    /// Registers a safe AST snapshot for semantic references.
    ///
    /// Re-registering the same file/arena pair may increase its node bound.
    /// Shrinking that bound, or reusing either identity with a different
    /// counterpart, is rejected before either registration map is modified.
    pub fn register_ast_scope(&mut self, scope: AstScope) -> bool {
        self.symbols.register_ast_scope(scope)
    }

    /// Registers and returns the validated identity of one source-file root.
    ///
    /// The root must be the arena's exact `SourceFile` payload with no parent.
    /// File and arena cross-wiring is rejected before either provenance map or
    /// the embedded symbol owner's AST registry is mutated.
    pub fn register_source_file(
        &mut self,
        arena: &NodeArena,
        source_file: NodeId,
        file: FileId,
    ) -> Option<SourceFileRef> {
        let root = arena.get(source_file)?;
        if root.kind != SyntaxKind::SourceFile
            || !matches!(root.data, NodeData::SourceFile(_))
            || root.parent.is_some()
        {
            return None;
        }

        let source = SourceFileRef::new(self.id(), NodeRef::new(arena.id(), file, source_file));
        let node_facts = Self::validated_source_node_facts(arena, source_file)?;
        if self
            .source_files
            .get(&file)
            .is_some_and(|registered| *registered != source)
            || self
                .source_files_by_arena
                .get(&arena.id())
                .is_some_and(|registered| *registered != source)
            || self
                .source_node_facts
                .get(&arena.id())
                .is_some_and(|registered| {
                    node_facts.len() < registered.len()
                        || node_facts[..registered.len()] != registered[..]
                })
        {
            return None;
        }

        if !self.symbols.register_ast_scope(AstScope::new(file, arena)) {
            return None;
        }
        self.source_files.insert(file, source);
        self.source_files_by_arena.insert(arena.id(), source);
        self.source_node_facts.insert(arena.id(), node_facts);
        Some(source)
    }

    /// Parses and copies one exact standalone `Identifier | QualifiedName`
    /// tree into the checker-owned synthetic entity-name arena.
    ///
    /// Parsing uses the pinned JavaScript-context isolated grammar and rejects
    /// trailing tokens or diagnostics before any semantic allocation.
    ///
    /// # Panics
    ///
    /// Panics if the checker-owned entity-name identity space is exhausted.
    pub fn register_entity_name_text(&mut self, text: &str) -> Option<EntityNameRef> {
        let parsed = parse_isolated_entity_name(text)?;
        self.register_parsed_entity_name(&parsed)
    }

    /// Copies one sealed parser result after preflighting its full closure.
    pub fn register_parsed_entity_name(
        &mut self,
        parsed: &IsolatedEntityName,
    ) -> Option<EntityNameRef> {
        self.register_entity_name(parsed.arena(), parsed.root())
    }

    fn register_entity_name(&mut self, arena: &NodeArena, root: NodeId) -> Option<EntityNameRef> {
        let mut visited = HashSet::new();
        let prepared = Self::prepare_entity_name(arena, root, None, &mut visited)?;
        self.entity_names
            .len()
            .checked_add(prepared.node_count())
            .and_then(|len| u32::try_from(len).ok())
            .expect("entity-name identity space exhausted before allocation");
        Some(self.allocate_prepared_entity_name(prepared))
    }

    #[must_use]
    pub fn entity_name(&self, entity_name: EntityNameRef) -> Option<&EntityNameNode> {
        (entity_name.owner() == self.id())
            .then(|| self.entity_names.get(entity_name.index()))
            .flatten()
    }

    #[must_use]
    pub fn entity_name_len(&self) -> usize {
        self.entity_names.len()
    }

    #[must_use]
    pub fn contains_source_file(&self, source_file: SourceFileRef) -> bool {
        source_file.owner() == self.id()
            && self
                .source_files
                .get(&source_file.file())
                .is_some_and(|registered| *registered == source_file)
            && self.contains_node_ref(source_file.node_ref())
    }

    #[must_use]
    pub fn contains_node_ref(&self, node: NodeRef) -> bool {
        self.symbols.contains_node_ref(node)
    }

    fn prepare_entity_name(
        arena: &NodeArena,
        node: NodeId,
        expected_parent: Option<NodeId>,
        visited: &mut HashSet<NodeId>,
    ) -> Option<PreparedEntityName> {
        if !visited.insert(node) {
            return None;
        }
        let node_data = arena.get(node)?;
        if node_data.parent != expected_parent
            || node_data.flags != ts_ast::NodeFlags::JAVASCRIPT_FILE
        {
            return None;
        }
        match (&node_data.kind, &node_data.data) {
            (SyntaxKind::Identifier, NodeData::Identifier(identifier))
                if identifier.flow_node.is_none() && !identifier.text.is_empty() =>
            {
                Some(PreparedEntityName::Identifier(identifier.text.clone()))
            }
            (SyntaxKind::QualifiedName, NodeData::QualifiedName(qualified))
                if qualified.flow_node.is_none() && qualified.facts == 0 =>
            {
                let left = Self::prepare_entity_name(arena, qualified.left, Some(node), visited)?;
                let right = Self::prepare_entity_name(arena, qualified.right, Some(node), visited)?;
                let PreparedEntityName::Identifier(right) = right else {
                    return None;
                };
                Some(PreparedEntityName::QualifiedName {
                    left: Box::new(left),
                    right,
                })
            }
            _ => None,
        }
    }

    fn allocate_prepared_entity_name(&mut self, prepared: PreparedEntityName) -> EntityNameRef {
        let node = match prepared {
            PreparedEntityName::Identifier(text) => EntityNameNode::Identifier { text },
            PreparedEntityName::QualifiedName { left, right } => {
                let left = self.allocate_prepared_entity_name(*left);
                let right =
                    self.allocate_entity_name_node(EntityNameNode::Identifier { text: right });
                EntityNameNode::QualifiedName { left, right }
            }
        };
        self.allocate_entity_name_node(node)
    }

    fn allocate_entity_name_node(&mut self, node: EntityNameNode) -> EntityNameRef {
        let one_based = u32::try_from(self.entity_names.len())
            .ok()
            .and_then(|index| index.checked_add(1))
            .and_then(NonZeroU32::new)
            .expect("preflighted entity-name identity exists");
        let entity_name = EntityNameRef::new(self.id(), one_based);
        self.entity_names.push(node);
        entity_name
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
    pub(super) fn canonical_tuple_target(
        &self,
        key: &CanonicalTupleTargetKey,
    ) -> Option<&CanonicalTupleTargetProvenance> {
        self.canonical_tuple_targets.get(key)
    }

    #[must_use]
    pub(super) fn canonical_tuple_target_for_type(
        &self,
        target: TypeId,
    ) -> Option<(&CanonicalTupleTargetKey, &CanonicalTupleTargetProvenance)> {
        self.canonical_tuple_targets
            .iter()
            .find(|(_, provenance)| provenance.target == target)
    }

    #[must_use]
    #[cfg(test)]
    pub(super) fn canonical_tuple_target_len(&self) -> usize {
        self.canonical_tuple_targets.len()
    }

    pub(super) fn try_reserve_canonical_tuple_targets(&mut self, additional: usize) -> bool {
        self.canonical_tuple_targets.try_reserve(additional).is_ok()
    }

    /// Publishes a completed tuple graph without replacing an existing shape
    /// or assigning one target identity to multiple shape keys.
    pub(super) fn publish_canonical_tuple_target(
        &mut self,
        key: CanonicalTupleTargetKey,
        provenance: CanonicalTupleTargetProvenance,
    ) -> bool {
        if self.canonical_tuple_targets.contains_key(&key)
            || self
                .canonical_tuple_targets
                .values()
                .any(|cached| cached.target == provenance.target)
            || self.types.get(provenance.target).is_none()
            || self.types.get(provenance.this_type).is_none()
            || provenance
                .type_parameters
                .iter()
                .any(|type_| self.types.get(*type_).is_none())
            || self
                .symbols
                .symbol_table(provenance.declared_members)
                .is_none()
            || provenance
                .element_symbols
                .iter()
                .any(|symbol| !self.symbols.contains_symbol(*symbol))
            || !self.symbols.contains_symbol(provenance.length_symbol)
            || self.types.get(provenance.length_type).is_none()
            || provenance
                .length_constituents
                .iter()
                .any(|type_| self.types.get(*type_).is_none())
        {
            return false;
        }
        self.canonical_tuple_targets.insert(key, provenance);
        true
    }

    #[cfg(test)]
    pub(super) fn replace_canonical_tuple_target_for_test(
        &mut self,
        key: &CanonicalTupleTargetKey,
        target: TypeId,
    ) -> Option<TypeId> {
        let provenance = self.canonical_tuple_targets.get_mut(key)?;
        Some(std::mem::replace(&mut provenance.target, target))
    }

    /// Returns the checker-owned mutable empty-tuple target, when created.
    ///
    /// Publication is deliberately one-shot and occurs only after the tuple's
    /// complete recursive graph has been initialized.
    #[must_use]
    pub(super) const fn canonical_empty_tuple_type_cache(&self) -> Option<TypeId> {
        match self.canonical_empty_tuple {
            Some(provenance) => Some(provenance.type_),
            None => None,
        }
    }

    pub(super) const fn canonical_empty_tuple_provenance(
        &self,
    ) -> Option<CanonicalEmptyTupleProvenance> {
        self.canonical_empty_tuple
    }

    pub(super) fn publish_canonical_empty_tuple_type(
        &mut self,
        provenance: CanonicalEmptyTupleProvenance,
    ) -> bool {
        if self.intrinsic_bootstrap.is_none()
            || self.types.get(provenance.type_).is_none()
            || self.types.get(provenance.this_type).is_none()
            || self
                .symbols
                .symbol_table(provenance.declared_members)
                .is_none()
            || !self.symbols.contains_symbol(provenance.length_symbol)
            || self.canonical_empty_tuple.is_some()
        {
            return false;
        }
        self.canonical_empty_tuple = Some(provenance);
        true
    }

    #[cfg(test)]
    pub(super) fn replace_canonical_empty_tuple_type_for_test(
        &mut self,
        type_: Option<TypeId>,
    ) -> Option<TypeId> {
        let previous = self.canonical_empty_tuple_type_cache();
        self.canonical_empty_tuple = match (self.canonical_empty_tuple, type_) {
            (_, None) => None,
            (Some(mut provenance), Some(type_)) => {
                provenance.type_ = type_;
                Some(provenance)
            }
            (None, Some(_)) => return previous,
        };
        previous
    }

    pub(super) fn try_reserve_types(&mut self, additional: usize) -> bool {
        self.types.try_reserve(additional)
    }

    pub(super) fn try_reserve_type_aliases(&mut self, additional: usize) -> bool {
        self.type_aliases.try_reserve(additional)
    }

    pub(super) fn try_reserve_function_type_provenance(&mut self, additional: usize) -> bool {
        self.function_type_provenance
            .try_reserve(additional)
            .is_ok()
    }

    pub(super) fn set_function_type_provenance(&mut self, type_: TypeId) -> bool {
        if self.types.get(type_).is_none() || self.function_type_provenance.contains(&type_) {
            return false;
        }
        self.function_type_provenance.insert(type_)
    }

    pub(super) fn type_has_function_type_provenance(&self, type_: TypeId) -> bool {
        self.function_type_provenance.contains(&type_)
    }

    pub(super) fn try_reserve_declared_call_set_provenance(
        &mut self,
        additional_types: usize,
        additional_signatures: usize,
    ) -> bool {
        self.declared_call_set_provenance
            .try_reserve(additional_types)
            .is_ok()
            && self
                .declared_call_set_types_by_signature
                .try_reserve(additional_signatures)
                .is_ok()
    }

    pub(super) fn set_declared_call_set_provenance(
        &mut self,
        type_: TypeId,
        signatures: &[SignatureId],
    ) -> bool {
        let mut unique = HashSet::with_capacity(signatures.len());
        if self.types.get(type_).is_none()
            || signatures.is_empty()
            || self.declared_call_set_provenance.contains(&type_)
            || signatures.iter().any(|signature| {
                !unique.insert(*signature)
                    || self
                        .declared_call_set_types_by_signature
                        .contains_key(signature)
                    || self.signature(*signature).is_none_or(|record| {
                        record.declaration().is_none_or(|declaration| {
                            self.source_node_kind(declaration) != Some(SyntaxKind::CallSignature)
                        })
                    })
            })
        {
            return false;
        }
        assert!(self.declared_call_set_provenance.insert(type_));
        for signature in signatures {
            assert!(
                self.declared_call_set_types_by_signature
                    .insert(*signature, type_)
                    .is_none()
            );
        }
        true
    }

    pub(super) fn type_has_declared_call_set_provenance(&self, type_: TypeId) -> bool {
        self.declared_call_set_provenance.contains(&type_)
    }

    pub(super) fn declared_call_set_type_for_signature(
        &self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        self.declared_call_set_types_by_signature
            .get(&signature)
            .copied()
    }

    pub(super) fn try_reserve_source_callable_provenance(&mut self, additional: usize) -> bool {
        self.source_callable_provenance
            .try_reserve(additional)
            .is_ok()
            && self
                .source_callable_types_by_declaration
                .try_reserve(additional)
                .is_ok()
            && self
                .source_callable_types_by_owner
                .try_reserve(additional)
                .is_ok()
            && self
                .source_callable_types_by_signature
                .try_reserve(additional)
                .is_ok()
            && self
                .source_callable_type_parameters
                .try_reserve(additional)
                .is_ok()
    }

    pub(super) fn source_callable_type_parameters(
        &self,
        signature: SignatureId,
    ) -> Option<&[SourceCallableTypeParameterProvenance]> {
        self.source_callable_type_parameters
            .get(&signature)
            .map(Box::as_ref)
    }

    #[cfg(test)]
    pub(super) fn replace_source_callable_type_parameters_for_test(
        &mut self,
        signature: SignatureId,
        replacement: Option<Box<[SourceCallableTypeParameterProvenance]>>,
    ) -> Option<Box<[SourceCallableTypeParameterProvenance]>> {
        match replacement {
            Some(replacement) => self
                .source_callable_type_parameters
                .insert(signature, replacement),
            None => self.source_callable_type_parameters.remove(&signature),
        }
    }

    pub(super) fn set_source_callable_provenance(
        &mut self,
        type_: TypeId,
        provenance: SourceCallableProvenance,
    ) -> bool {
        let contextual_pair = match (provenance.contextual_target, provenance.contextual_variable) {
            (None, None) => true,
            (Some(target), Some(variable)) => {
                provenance.family == SourceCallableFamily::ArrowFunction
                    && provenance.return_provenance == SourceCallableReturnProvenance::Inferred
                    && target != type_
                    && self.types.get(target).is_some()
                    && self.symbols.contains_symbol(variable)
                    && variable != provenance.owner_symbol
            }
            _ => false,
        };
        let exact_type_parameters =
            self.signatures
                .get(provenance.signature)
                .is_some_and(|signature| {
                    signature.type_parameters().is_empty()
                        && !self
                            .source_callable_type_parameters
                            .contains_key(&provenance.signature)
                });
        let array_targets_valid = provenance.array_targets.is_none_or(|targets| {
            self.types.get(targets.array_type()).is_some()
                && self.types.get(targets.readonly_array_type()).is_some()
        });
        if self.types.get(type_).is_none()
            || self.source_callable_provenance.contains_key(&type_)
            || !contextual_pair
            || !exact_type_parameters
            || !array_targets_valid
            || self.source_node_kind(provenance.declaration)
                != Some(provenance.family.syntax_kind())
            || !self.symbols.contains_symbol(provenance.owner_symbol)
            || provenance
                .owner_parent
                .is_some_and(|parent| !self.symbols.contains_symbol(parent))
            || provenance
                .export_local
                .is_some_and(|local| !self.symbols.contains_symbol(local))
            || provenance.export_local == Some(provenance.owner_symbol)
            || provenance.return_provenance == SourceCallableReturnProvenance::Inferred
                && provenance.generic_return_type_parameter.is_some()
            || self.signatures.get(provenance.signature).is_none()
            || self
                .source_callable_types_by_declaration
                .contains_key(&provenance.declaration)
            || self
                .source_callable_types_by_owner
                .contains_key(&provenance.owner_symbol)
            || self
                .source_callable_types_by_signature
                .contains_key(&provenance.signature)
        {
            return false;
        }
        let by_type = self.source_callable_provenance.insert(type_, provenance);
        let by_declaration = self
            .source_callable_types_by_declaration
            .insert(provenance.declaration, type_);
        let by_owner = self
            .source_callable_types_by_owner
            .insert(provenance.owner_symbol, type_);
        let by_signature = self
            .source_callable_types_by_signature
            .insert(provenance.signature, type_);
        assert!(
            by_type.is_none()
                && by_declaration.is_none()
                && by_owner.is_none()
                && by_signature.is_none(),
            "source callable reverse maps were prevalidated absent"
        );
        true
    }

    pub(super) fn source_callable_provenance(
        &self,
        type_: TypeId,
    ) -> Option<SourceCallableProvenance> {
        self.source_callable_provenance.get(&type_).copied()
    }

    #[cfg(test)]
    pub(super) fn replace_source_callable_provenance_for_test(
        &mut self,
        type_: TypeId,
        replacement: Option<SourceCallableProvenance>,
    ) -> Option<SourceCallableProvenance> {
        match replacement {
            Some(replacement) => self.source_callable_provenance.insert(type_, replacement),
            None => self.source_callable_provenance.remove(&type_),
        }
    }

    #[cfg(test)]
    pub(super) fn replace_source_callable_type_for_declaration_for_test(
        &mut self,
        declaration: NodeRef,
        replacement: Option<TypeId>,
    ) -> Option<TypeId> {
        match replacement {
            Some(replacement) => self
                .source_callable_types_by_declaration
                .insert(declaration, replacement),
            None => self
                .source_callable_types_by_declaration
                .remove(&declaration),
        }
    }

    pub(super) fn source_callable_type_for_owner(&self, owner: SemanticSymbolId) -> Option<TypeId> {
        self.source_callable_types_by_owner.get(&owner).copied()
    }

    pub(super) fn source_callable_type_for_signature(
        &self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        self.source_callable_types_by_signature
            .get(&signature)
            .copied()
    }

    pub(super) fn source_callable_type_for_declaration(
        &self,
        declaration: NodeRef,
    ) -> Option<TypeId> {
        self.source_callable_types_by_declaration
            .get(&declaration)
            .copied()
    }

    pub(super) fn source_callable_provenance_lengths(&self) -> [usize; 5] {
        [
            self.source_callable_provenance.len(),
            self.source_callable_types_by_declaration.len(),
            self.source_callable_types_by_owner.len(),
            self.source_callable_types_by_signature.len(),
            self.source_callable_type_parameters.len(),
        ]
    }

    fn has_callable_provenance(&self) -> bool {
        !self.function_type_provenance.is_empty()
            || !self.declared_call_set_provenance.is_empty()
            || !self.source_callable_provenance.is_empty()
            || self.signatures.iter().any(|(_, signature)| {
                signature.declaration().is_some_and(|node| {
                    self.source_node_kind(node) == Some(SyntaxKind::CallSignature)
                })
            })
    }

    pub(super) fn mark_union_cache_validation_dirty(&mut self) {
        if self.intrinsic_bootstrap.is_some() {
            self.union_cache_needs_validation = true;
        }
    }

    fn node_is_function_type(&self, node: NodeRef) -> bool {
        self.source_node_kind(node) == Some(SyntaxKind::FunctionType)
    }

    fn node_is_source_callable_declaration(&self, node: NodeRef) -> bool {
        self.source_callable_type_for_declaration(node)
            .and_then(|type_| self.source_callable_provenance(type_))
            .is_some_and(|provenance| {
                provenance.declaration == node
                    && self.source_node_kind(node) == Some(provenance.family.syntax_kind())
            })
    }

    fn node_has_callable_ancestor(&self, mut node: NodeRef) -> bool {
        let mut visited = HashSet::new();
        loop {
            if !visited.insert(node) {
                return false;
            }
            if self.node_is_function_type(node)
                || self.node_is_source_callable_declaration(node)
                || self.source_node_kind(node) == Some(SyntaxKind::CallSignature)
            {
                return true;
            }
            let Some(SourceNodeParent::Parent(parent)) = self.source_node_parent(node) else {
                return false;
            };
            node = parent;
        }
    }

    fn symbol_is_callable_parameter(&self, symbol: SemanticSymbolId) -> bool {
        let Some([declaration]) = self.symbol(symbol).and_then(Symbol::declarations) else {
            return false;
        };
        self.source_node_kind(*declaration) == Some(SyntaxKind::Parameter)
            && matches!(
                self.source_node_parent(*declaration),
                Some(SourceNodeParent::Parent(parent))
                    if self.node_is_function_type(parent)
                        || self.node_is_source_callable_declaration(parent)
                        || self.source_node_kind(parent) == Some(SyntaxKind::CallSignature)
            )
    }

    fn symbol_is_source_callable_owner(&self, symbol: SemanticSymbolId) -> bool {
        self.source_callable_types_by_owner.contains_key(&symbol)
    }

    fn signature_is_callable(&self, signature: SignatureId) -> bool {
        self.signature(signature)
            .and_then(Signature::declaration)
            .is_some_and(|declaration| {
                self.node_is_function_type(declaration)
                    || self.source_node_kind(declaration) == Some(SyntaxKind::CallSignature)
                    || self
                        .source_callable_type_for_signature(signature)
                        .and_then(|type_| self.source_callable_provenance(type_))
                        .is_some_and(|provenance| provenance.declaration == declaration)
            })
    }

    fn signature_owns_callable_type(&self, signature: SignatureId) -> bool {
        let Some(declaration) = self.signature(signature).and_then(Signature::declaration) else {
            return false;
        };
        if self.signature_links(declaration).is_none_or(|links| {
            links.resolved_signature != ResolvedSignatureState::Resolved(signature)
        }) {
            return false;
        }
        let type_ = if self.node_is_function_type(declaration) {
            self.type_node_links(declaration)
                .and_then(|links| links.resolved_type)
                .filter(|type_| self.type_has_function_type_provenance(*type_))
        } else if self.source_node_kind(declaration) == Some(SyntaxKind::CallSignature) {
            self.declared_call_set_types_by_signature
                .get(&signature)
                .copied()
                .filter(|type_| self.type_has_declared_call_set_provenance(*type_))
        } else {
            self.source_callable_type_for_signature(signature)
                .filter(|type_| {
                    self.source_callable_provenance(*type_)
                        .is_some_and(|provenance| {
                            provenance.declaration == declaration
                                && provenance.signature == signature
                        })
                })
        };
        type_.is_some()
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

    pub(super) fn try_reserve_checker_symbol_allocations(
        &mut self,
        additional_symbols: usize,
        additional_tables: usize,
    ) -> bool {
        self.symbols
            .try_reserve_checker_allocations(additional_symbols, additional_tables)
    }

    /// Returns a symbol after exactly one merged-symbol redirect lookup.
    ///
    /// `None` means the input is not owned by this store. Redirect targets are
    /// validated when recorded, so a valid input always returns a valid symbol.
    #[must_use]
    pub fn get_merged_symbol(&self, symbol: SemanticSymbolId) -> Option<SemanticSymbolId> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.merged_symbols.get(&symbol).copied().unwrap_or(symbol))
    }

    /// Number of exact source-to-merged redirects recorded by the checker.
    #[must_use]
    pub fn merged_symbol_len(&self) -> usize {
        self.merged_symbols.len()
    }

    /// Records one exact source-to-target merged-symbol redirect.
    ///
    /// Existing source redirects follow upstream map-overwrite semantics.
    /// Cycles and invalid provenance are rejected before the map changes.
    #[allow(dead_code)] // Called by the production merge substrate.
    pub(super) fn record_merged_symbol(
        &mut self,
        target: SemanticSymbolId,
        source: SemanticSymbolId,
    ) -> Result<Option<SemanticSymbolId>, MergedSymbolRecordError> {
        if !self.symbols.contains_symbol(target) {
            return Err(MergedSymbolRecordError::InvalidTarget(target));
        }
        if !self.symbols.contains_symbol(source) {
            return Err(MergedSymbolRecordError::InvalidSource(source));
        }
        if target == source {
            return Err(MergedSymbolRecordError::SelfRedirect(source));
        }

        let mut cursor = target;
        let mut visited = HashSet::new();
        loop {
            if cursor == source {
                return Err(MergedSymbolRecordError::RedirectCycle { source, target });
            }
            if !visited.insert(cursor) {
                return Err(MergedSymbolRecordError::RedirectCycle { source, target });
            }
            let Some(next) = self.merged_symbols.get(&cursor).copied() else {
                break;
            };
            cursor = next;
        }

        let previous = self.merged_symbols.insert(source, target);
        if self.has_callable_provenance() {
            self.mark_union_cache_validation_dirty();
        }
        Ok(previous)
    }

    /// Returns a symbol's raw parent after exactly one merged redirect.
    #[must_use]
    pub fn get_parent_of_symbol(&self, symbol: SemanticSymbolId) -> Option<SemanticSymbolId> {
        let parent = self.symbols.symbol(symbol)?.parent()?;
        self.get_merged_symbol(parent)
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
    pub(super) fn alloc_prepared_symbol_table(
        &mut self,
        prepared: PreparedSymbolTable,
    ) -> SymbolTableId {
        self.symbols.alloc_prepared_symbol_table(prepared)
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
        let previous = self.symbols.insert_symbol(table, name, symbol)?;
        if self.has_callable_provenance() {
            self.mark_union_cache_validation_dirty();
        }
        Some(previous)
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
        if !self.symbols.set_symbol_flags(symbol, flags, check_flags) {
            return false;
        }
        if self.has_callable_provenance() {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub fn set_symbol_declarations(
        &mut self,
        symbol: SemanticSymbolId,
        declarations: Option<Vec<NodeRef>>,
        value_declaration: Option<NodeRef>,
    ) -> bool {
        if !self
            .symbols
            .set_symbol_declarations(symbol, declarations, value_declaration)
        {
            return false;
        }
        if self.has_callable_provenance() {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub fn set_symbol_relationships(
        &mut self,
        symbol: SemanticSymbolId,
        members: Option<SymbolTableId>,
        exports: Option<SymbolTableId>,
        parent: Option<SemanticSymbolId>,
        export_symbol: Option<SemanticSymbolId>,
    ) -> bool {
        if !self
            .symbols
            .set_symbol_relationships(symbol, members, exports, parent, export_symbol)
        {
            return false;
        }
        if self.has_callable_provenance() {
            self.mark_union_cache_validation_dirty();
        }
        true
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
        if !self.contains_node_ref(node) || !links.flags.has_only_defined_bits() {
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
        let dirty = self.node_has_callable_ancestor(node)
            && self
                .type_node_links(node)
                .is_some_and(|current| current != &TypeNodeLinks::default() && current != &links);
        self.links.type_node.replace_key(node, links);
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub(super) fn try_reserve_type_node_links(&mut self, additional: usize) -> bool {
        self.links.type_node.try_reserve(additional)
    }

    #[must_use]
    pub fn enum_member_links(&self, node: NodeRef) -> Option<&EnumMemberLinks> {
        self.node_has_kind(node, |kind| kind == SyntaxKind::EnumMember)
            .then(|| self.links.enum_member.try_get(&node))
            .flatten()
    }

    pub fn ensure_enum_member_links(&mut self, node: NodeRef) -> bool {
        if !self.node_has_kind(node, |kind| kind == SyntaxKind::EnumMember) {
            return false;
        }
        self.links.enum_member.get(node);
        true
    }

    pub fn set_enum_member_links(&mut self, node: NodeRef, links: EnumMemberLinks) -> bool {
        if !self.node_has_kind(node, |kind| kind == SyntaxKind::EnumMember) {
            return false;
        }
        self.links.enum_member.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn signature_links(&self, node: NodeRef) -> Option<&SignatureLinks> {
        self.node_is_signature_links_eligible(node)
            .then(|| self.links.signature.try_get(&node))
            .flatten()
    }

    pub fn ensure_signature_links(&mut self, node: NodeRef) -> bool {
        if !self.node_is_signature_links_eligible(node) {
            return false;
        }
        self.links.signature.get(node);
        true
    }

    pub fn set_signature_links(&mut self, node: NodeRef, mut links: SignatureLinks) -> bool {
        if let Some(bootstrap) = &self.intrinsic_bootstrap {
            if links.resolved_signature
                == ResolvedSignatureState::Resolved(bootstrap.resolving_signature)
            {
                links.resolved_signature = ResolvedSignatureState::Resolving;
            }
            if links.effects_signature
                == EffectsSignatureState::Resolved(bootstrap.unknown_signature)
            {
                links.effects_signature = EffectsSignatureState::NoEffects;
            }
            if links.decorator_signature
                == DecoratorSignatureState::Resolved(bootstrap.any_signature)
            {
                links.decorator_signature = DecoratorSignatureState::NotApplicable;
            }
        }
        if !self.node_is_signature_links_eligible(node)
            || !self.valid_optional_signature(links.resolved_signature.signature())
            || !self.valid_optional_signature(links.effects_signature.signature())
            || !self.valid_optional_signature(links.decorator_signature.signature())
        {
            return false;
        }
        let dirty = (self.node_is_function_type(node)
            || self.node_is_source_callable_declaration(node))
            || self.source_node_kind(node) == Some(SyntaxKind::CallSignature);
        let dirty = dirty
            && self
                .signature_links(node)
                .is_some_and(|current| current != &SignatureLinks::default() && current != &links);
        self.links.signature.replace_key(node, links);
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
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
        let dirty = (self.symbol_is_callable_parameter(symbol)
            || self.symbol_is_source_callable_owner(symbol))
            && self.value_symbol_links(symbol).is_some_and(|current| {
                current != &ValueSymbolLinks::default() && current != &links
            });
        self.links.value_symbol.replace_key(symbol, links);
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
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
        mut links: AliasSymbolLinks,
    ) -> bool {
        if let Some(bootstrap) = &self.intrinsic_bootstrap
            && links.alias_target == AliasTargetState::Resolved(bootstrap.unknown_symbol)
        {
            links.alias_target = AliasTargetState::Unknown;
        }
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
        let dirty = self.type_alias_links(symbol).is_some_and(|current| {
            current != &TypeAliasLinks::default()
                && current != &links
                && [current.declared_type, links.declared_type]
                    .into_iter()
                    .flatten()
                    .any(|type_| self.function_type_provenance.contains(&type_))
        });
        let previous = self
            .links
            .type_alias
            .try_get(&symbol)
            .and_then(|links| links.declared_type);
        let declared_type = links.declared_type;
        self.links.type_alias.replace_key(symbol, links);
        if previous != declared_type {
            if let Some(previous) = previous {
                let remove_entry = self
                    .type_alias_declared_type_owners
                    .get_mut(&previous)
                    .is_some_and(|owners| {
                        owners.remove(&symbol);
                        owners.is_empty()
                    });
                if remove_entry {
                    self.type_alias_declared_type_owners.remove(&previous);
                }
            }
            if let Some(declared_type) = declared_type {
                self.type_alias_declared_type_owners
                    .entry(declared_type)
                    .or_default()
                    .insert(symbol);
            }
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    /// Returns every cached type-alias symbol whose declared-type link points
    /// at `type_`. This reverse edge is maintained atomically with
    /// [`Self::set_type_alias_links`] and is used to prove symmetric alias
    /// provenance for declared type-literal identities.
    #[must_use]
    pub(super) fn type_alias_declared_type_owners(
        &self,
        type_: TypeId,
    ) -> Option<&HashSet<SemanticSymbolId>> {
        self.type_alias_declared_type_owners.get(&type_)
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

    /// Marks the narrow interval in which a recursive class shell is visible
    /// through its declared-type link but is not initialized yet.
    ///
    /// The marker is checker-private and cannot exist before intrinsic
    /// bootstrap, so it does not add a hidden pre-bootstrap pristine state.
    pub(super) fn begin_declared_type_initialization(&mut self, symbol: SemanticSymbolId) -> bool {
        self.intrinsic_bootstrap.is_some()
            && self.symbols.contains_symbol(symbol)
            && self.declared_types_in_progress.insert(symbol)
    }

    #[must_use]
    pub(super) fn declared_type_initialization_in_progress(
        &self,
        symbol: SemanticSymbolId,
    ) -> bool {
        self.symbols.contains_symbol(symbol) && self.declared_types_in_progress.contains(&symbol)
    }

    pub(super) fn finish_declared_type_initialization(&mut self, symbol: SemanticSymbolId) -> bool {
        self.symbols.contains_symbol(symbol) && self.declared_types_in_progress.remove(&symbol)
    }

    #[must_use]
    pub fn assertion_links(&self, node: NodeRef) -> Option<&AssertionLinks> {
        self.node_has_kind(node, |kind| {
            matches!(
                kind,
                SyntaxKind::TypeAssertionExpression | SyntaxKind::AsExpression
            )
        })
        .then(|| self.links.assertion.try_get(&node))
        .flatten()
    }

    pub fn ensure_assertion_links(&mut self, node: NodeRef) -> bool {
        if !self.node_has_kind(node, |kind| {
            matches!(
                kind,
                SyntaxKind::TypeAssertionExpression | SyntaxKind::AsExpression
            )
        }) {
            return false;
        }
        self.links.assertion.get(node);
        true
    }

    pub fn set_assertion_links(&mut self, node: NodeRef, links: AssertionLinks) -> bool {
        if !self.node_has_kind(node, |kind| {
            matches!(
                kind,
                SyntaxKind::TypeAssertionExpression | SyntaxKind::AsExpression
            )
        }) || !self.valid_optional_type(links.expr_type)
        {
            return false;
        }
        self.links.assertion.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn array_literal_links(&self, node: NodeRef) -> Option<&ArrayLiteralLinks> {
        self.node_has_kind(node, |kind| kind == SyntaxKind::ArrayLiteralExpression)
            .then(|| self.links.array_literal.try_get(&node))
            .flatten()
    }

    pub fn ensure_array_literal_links(&mut self, node: NodeRef) -> bool {
        if !self.node_has_kind(node, |kind| kind == SyntaxKind::ArrayLiteralExpression) {
            return false;
        }
        self.links.array_literal.get(node);
        true
    }

    pub fn set_array_literal_links(&mut self, node: NodeRef, links: ArrayLiteralLinks) -> bool {
        if !self.node_has_kind(node, |kind| kind == SyntaxKind::ArrayLiteralExpression) {
            return false;
        }
        self.links.array_literal.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn switch_statement_links(&self, node: NodeRef) -> Option<&SwitchStatementLinks> {
        self.node_has_kind(node, |kind| kind == SyntaxKind::SwitchStatement)
            .then(|| self.links.switch_statement.try_get(&node))
            .flatten()
    }

    pub fn ensure_switch_statement_links(&mut self, node: NodeRef) -> bool {
        if !self.node_has_kind(node, |kind| kind == SyntaxKind::SwitchStatement) {
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
        if !self.node_has_kind(node, |kind| kind == SyntaxKind::SwitchStatement)
            || !self.valid_optional_types(links.switch_types.as_deref())
        {
            return false;
        }
        self.links.switch_statement.replace_key(node, links);
        true
    }

    #[must_use]
    pub fn jsx_element_links(&self, node: NodeRef) -> Option<&JsxElementLinks> {
        self.node_is_source_reachable(node)
            .then(|| self.links.jsx_element.try_get(&node))
            .flatten()
    }

    pub fn ensure_jsx_element_links(&mut self, node: NodeRef) -> bool {
        if !self.node_is_source_reachable(node) {
            return false;
        }
        self.links.jsx_element.get(node);
        true
    }

    pub fn set_jsx_element_links(&mut self, node: NodeRef, links: JsxElementLinks) -> bool {
        if !self.node_is_source_reachable(node)
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

    #[must_use]
    pub fn containing_symbol_links(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&ContainingSymbolLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.containing_symbol.try_get(&symbol))
            .flatten()
    }

    pub fn ensure_containing_symbol_links(&mut self, symbol: SemanticSymbolId) -> bool {
        if !self.symbols.contains_symbol(symbol) {
            return false;
        }
        self.links.containing_symbol.get(symbol);
        true
    }

    pub fn set_containing_symbol_links(
        &mut self,
        symbol: SemanticSymbolId,
        links: ContainingSymbolLinks,
    ) -> bool {
        let valid_extended = match &links.extended_containers {
            ExtendedContainersState::Uncomputed
            | ExtendedContainersState::Computed(OptionalSymbolSequence::Nil) => true,
            ExtendedContainersState::Computed(OptionalSymbolSequence::Allocated(symbols)) => {
                self.valid_symbols(symbols)
            }
        };
        let valid_by_file = links
            .extended_containers_by_file
            .as_ref()
            .is_none_or(|by_file| {
                by_file.iter().all(|(source_file, symbols)| {
                    self.contains_source_file(*source_file)
                        && self.valid_optional_symbol_sequence(symbols)
                })
            });
        let valid_accessible = links.accessible_chain_cache.as_ref().is_none_or(|cache| {
            cache.iter().all(|(key, symbols)| {
                self.valid_optional_node(key.location)
                    && self.valid_optional_symbol_sequence(symbols)
            })
        });
        if !self.symbols.contains_symbol(symbol)
            || !valid_extended
            || !valid_by_file
            || !valid_accessible
        {
            return false;
        }
        self.links.containing_symbol.replace_key(symbol, links);
        true
    }

    #[must_use]
    pub fn source_file_links(&self, source_file: SourceFileRef) -> Option<&SourceFileLinks> {
        self.contains_source_file(source_file)
            .then(|| self.links.source_file.try_get(&source_file))
            .flatten()
    }

    pub fn ensure_source_file_links(&mut self, source_file: SourceFileRef) -> bool {
        if !self.contains_source_file(source_file) {
            return false;
        }
        self.links.source_file.get(source_file);
        true
    }

    pub fn set_source_file_links(
        &mut self,
        source_file: SourceFileRef,
        links: SourceFileLinks,
    ) -> bool {
        let valid_deferred_nodes = links
            .deferred_nodes
            .iter()
            .all(|node| self.valid_source_node(source_file, *node));
        let valid_identifier_nodes = links.identifier_check_nodes.as_deref().is_none_or(|nodes| {
            nodes
                .iter()
                .all(|node| self.valid_source_node(source_file, *node))
        });
        let valid_jsx_factory = links
            .local_jsx_factory
            .is_none_or(|entity| self.entity_name(entity).is_some());
        let valid_jsx_fragment_factory = links
            .local_jsx_fragment_factory
            .is_none_or(|entity| self.entity_name(entity).is_some());
        if !self.contains_source_file(source_file)
            || !self.valid_optional_symbol(links.external_helpers_module)
            || !links
                .requested_external_emit_helpers
                .has_only_defined_bits()
            || !valid_deferred_nodes
            || !valid_identifier_nodes
            || !valid_jsx_factory
            || !valid_jsx_fragment_factory
            || !self.valid_optional_type(links.jsx_fragment_type)
        {
            return false;
        }
        self.links.source_file.replace_key(source_file, links);
        true
    }

    /// Reads one exact relation-cache result without allocating the lazy map.
    ///
    /// Relation-key construction is intentionally outside this substrate. The
    /// caller must supply the canonical key produced by the eventual exact
    /// `getRelationKey` port.
    #[must_use]
    pub fn relation_cache_get(
        &self,
        relation: RelationKind,
        key: CacheHashKey,
    ) -> RelationComparisonResult {
        self.relations.get(relation, key)
    }

    /// Ports `Relation.set`, allocating the selected result map on its first
    /// write and replacing any result already stored under `key`.
    pub fn relation_cache_set(
        &mut self,
        relation: RelationKind,
        key: CacheHashKey,
        result: RelationComparisonResult,
    ) {
        self.relations.set(relation, key, result);
    }

    #[must_use]
    pub fn relation_cache_size(&self, relation: RelationKind) -> usize {
        self.relations.size(relation)
    }

    /// Distinguishes upstream's nil result map from an allocated map.
    #[must_use]
    pub fn relation_cache_is_allocated(&self, relation: RelationKind) -> bool {
        self.relations.is_allocated(relation)
    }

    /// Exact initial work budget used by `checkTypeRelatedToEx` for this cache.
    #[must_use]
    pub fn relation_comparison_budget(&self, relation: RelationKind) -> isize {
        self.relations.comparison_budget(relation)
    }

    #[must_use]
    pub fn relation_state_snapshot(&self) -> RelationStateSnapshot {
        self.relations.snapshot()
    }

    /// Reads the directional enum relation cache.
    ///
    /// A valid cache miss is `Some(RelationComparisonResult::NONE)`. `None`
    /// rejects either foreign symbol before assigning either symbol's lazy
    /// process-global ID or mutating cache state.
    pub fn enum_relation_cache_get(
        &mut self,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    ) -> Option<RelationComparisonResult> {
        let (source_id, target_id) = self.enum_relation_symbol_ids(source, target)?;
        Some(self.relations.enum_get(source_id, target_id))
    }

    /// Writes the directional enum relation cache after validating both keys.
    ///
    /// Returns `false` without assigning global symbol IDs or changing cache
    /// state when either handle is foreign.
    pub fn enum_relation_cache_set(
        &mut self,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
        result: RelationComparisonResult,
    ) -> bool {
        let Some((source_id, target_id)) = self.enum_relation_symbol_ids(source, target) else {
            return false;
        };
        self.relations.enum_set(source_id, target_id, result);
        true
    }

    #[must_use]
    pub fn enum_relation_cache_size(&self) -> usize {
        self.relations.enum_size()
    }

    fn enum_relation_symbol_ids(
        &mut self,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    ) -> Option<(u64, u64)> {
        if !self.symbols.contains_symbol(source) || !self.symbols.contains_symbol(target) {
            return None;
        }
        let source_id = self
            .symbols
            .global_symbol_id(source)
            .expect("validated source symbol must receive a global ID");
        let target_id = self
            .symbols
            .global_symbol_id(target)
            .expect("validated target symbol must receive a global ID");
        Some((source_id, target_id))
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

    pub(super) fn checker_link_allocated_lengths(&self) -> [usize; 26] {
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

    /// Starts one internal transaction around a fallible resolution callback.
    pub(super) fn checkpoint_type_resolution(&mut self) -> TypeResolutionCheckpoint {
        self.type_resolutions.checkpoint()
    }

    /// Commits a balanced callback suffix while preserving genuine cycle
    /// result-bit changes.
    pub(super) fn commit_type_resolution_checkpoint(
        &mut self,
        token: TypeResolutionCheckpoint,
    ) -> Result<(), TypeResolutionCheckpoint> {
        self.type_resolutions.commit_checkpoint(token)
    }

    /// Removes a fallible callback suffix and restores the pre-existing stack.
    pub(super) fn rollback_type_resolution_checkpoint(
        &mut self,
        token: TypeResolutionCheckpoint,
    ) -> Result<(), TypeResolutionCheckpoint> {
        self.type_resolutions.rollback_checkpoint(token)
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

    /// Reserves mapper identities before an infallible publication suffix.
    pub(super) fn try_reserve_mappers(&mut self, additional: usize) -> bool {
        self.mappers.try_reserve(additional)
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

    pub(super) fn try_reserve_signatures(&mut self, additional: usize) -> bool {
        self.signatures.try_reserve(additional)
    }

    /// Reserves upstream `cachedSignatures` entries without publishing one.
    pub(super) fn try_reserve_cached_signatures(&mut self, additional: usize) -> bool {
        self.cached_signatures.try_reserve(additional).is_ok()
    }

    /// Reads one exact upstream `cachedSignatures` entry.
    #[must_use]
    pub(super) fn cached_signature(
        &self,
        target: SignatureId,
        type_arguments: CacheHashKey,
        exact_type_arguments: &[TypeId],
    ) -> CachedSignatureLookup {
        if self.signature(target).is_none()
            || !self.valid_types(exact_type_arguments)
            || type_list_key(exact_type_arguments) != type_arguments
        {
            return CachedSignatureLookup::Invalid;
        }
        let Some(entry) = self.cached_signatures.get(&(target, type_arguments)) else {
            return CachedSignatureLookup::Missing;
        };
        if self.signature(entry.instantiated).is_none() {
            CachedSignatureLookup::Invalid
        } else if entry.type_arguments.as_ref() == exact_type_arguments {
            CachedSignatureLookup::Hit(entry.instantiated)
        } else {
            CachedSignatureLookup::HashCollision(entry.instantiated)
        }
    }

    /// Publishes one prevalidated instantiated signature. The instantiated
    /// signature must already point at `target`; callers commit this cache
    /// entry last so every visible entry is dependency-closed.
    pub(super) fn set_cached_signature(
        &mut self,
        target: SignatureId,
        type_arguments: CacheHashKey,
        exact_type_arguments: Box<[TypeId]>,
        instantiated: SignatureId,
    ) -> bool {
        if self.signature(target).is_none()
            || !self.valid_types(&exact_type_arguments)
            || type_list_key(&exact_type_arguments) != type_arguments
            || !self.signature(instantiated).is_some_and(|signature| {
                signature.target() == Some(target) && signature.mapper().is_some()
            })
            || self
                .cached_signatures
                .contains_key(&(target, type_arguments))
        {
            return false;
        }
        self.cached_signatures.insert(
            (target, type_arguments),
            CachedSignatureEntry {
                type_arguments: exact_type_arguments,
                instantiated,
            },
        );
        true
    }

    #[must_use]
    pub(super) fn cached_signature_len(&self) -> usize {
        self.cached_signatures.len()
    }

    /// Reports whether an owned signature is published by any authoritative
    /// `cachedSignatures` entry. Recovery signatures must remain call-local,
    /// so their validators need a reverse membership check rather than a
    /// lookup for one already-known type-argument vector.
    #[must_use]
    pub(super) fn cached_signatures_contain(&self, signature: SignatureId) -> Option<bool> {
        self.signature(signature)?;
        Some(
            self.cached_signatures
                .values()
                .any(|entry| entry.instantiated == signature),
        )
    }

    /// Reserves a transient parameter's value-link slot before publishing its
    /// symbol, mapper, and instantiated signature.
    pub(super) fn try_reserve_value_symbol_links(&mut self, additional: usize) -> bool {
        self.links.value_symbol.try_reserve(additional)
    }

    pub(super) fn try_reserve_function_signature_return_annotations(
        &mut self,
        additional: usize,
    ) -> bool {
        self.function_signature_return_annotations
            .try_reserve(additional)
            .is_ok()
    }

    pub(super) fn set_function_signature_return_annotation(
        &mut self,
        id: SignatureId,
        annotation: NodeRef,
        null_literal_identity: bool,
    ) -> bool {
        let Some(declaration) = self.signature(id).and_then(Signature::declaration) else {
            return false;
        };
        let valid_callable = self.node_is_function_type(declaration)
            || self.source_node_kind(declaration) == Some(SyntaxKind::CallSignature)
            || self
                .source_callable_type_for_signature(id)
                .and_then(|type_| self.source_callable_provenance(type_))
                .is_some_and(|provenance| provenance.declaration == declaration);
        if !valid_callable || self.function_signature_return_annotations.contains_key(&id) {
            return false;
        }
        let mut current = annotation;
        loop {
            let Some(SourceNodeParent::Parent(parent)) = self.source_node_parent(current) else {
                return false;
            };
            if parent == declaration {
                break;
            }
            if self.source_node_kind(parent) != Some(SyntaxKind::ParenthesizedType) {
                return false;
            }
            current = parent;
        }
        let previous = self
            .function_signature_return_annotations
            .insert(id, (annotation, null_literal_identity));
        assert!(
            previous.is_none(),
            "the return annotation was checked absent"
        );
        true
    }

    pub(super) fn function_signature_return_annotation(
        &self,
        id: SignatureId,
    ) -> Option<(NodeRef, bool)> {
        self.function_signature_return_annotations.get(&id).copied()
    }

    pub(super) fn try_reserve_callable_signature_parameter_types(
        &mut self,
        additional: usize,
    ) -> bool {
        self.callable_signature_parameter_types
            .try_reserve(additional)
            .is_ok()
    }

    /// Publishes immutable semantic parameter identities for exact callables.
    /// The whole batch is validated before any entry is inserted.
    pub(super) fn set_callable_signature_parameter_types_batch(
        &mut self,
        parameter_types: Vec<(SignatureId, Vec<TypeId>)>,
    ) -> bool {
        let mut signatures = HashSet::with_capacity(parameter_types.len());
        if parameter_types.iter().any(|(signature, types)| {
            !signatures.insert(*signature)
                || self
                    .callable_signature_parameter_types
                    .contains_key(signature)
                || !self.signature_owns_callable_type(*signature)
                || self
                    .signature(*signature)
                    .is_none_or(|record| record.parameters().len() != types.len())
                || !self.valid_optional_types(Some(types))
        }) {
            return false;
        }
        for (signature, types) in parameter_types {
            let previous = self
                .callable_signature_parameter_types
                .insert(signature, types);
            assert!(
                previous.is_none(),
                "callable parameter provenance was prevalidated absent"
            );
        }
        true
    }

    pub(super) fn callable_signature_parameter_types(
        &self,
        signature: SignatureId,
    ) -> Option<&[TypeId]> {
        self.callable_signature_parameter_types
            .get(&signature)
            .map(Vec::as_slice)
    }

    pub(super) fn callable_signature_parameter_types_len(&self) -> usize {
        self.callable_signature_parameter_types.len()
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
        let dirty = self.signature_is_callable(id);
        if !self.signatures.set_resolved_min_argument_count(id, count) {
            return false;
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub fn set_signature_resolved_return_type(
        &mut self,
        id: SignatureId,
        type_id: Option<TypeId>,
    ) -> bool {
        if !self.valid_optional_type(type_id) {
            return false;
        }
        let dirty = self.signature_is_callable(id);
        if !self.signatures.set_resolved_return_type(id, type_id) {
            return false;
        }
        let cleared_circular_provenance = self.circular_return_signatures.remove(&id).is_some();
        if dirty || cleared_circular_provenance {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub(super) fn try_reserve_circular_return_signatures(&mut self, additional: usize) -> bool {
        self.circular_return_signatures
            .try_reserve(additional)
            .is_ok()
    }

    pub(super) fn signature_has_circular_return_type(&self, id: SignatureId) -> bool {
        self.circular_return_signatures.contains_key(&id)
    }

    pub(super) fn circular_return_annotation_type(&self, id: SignatureId) -> Option<TypeId> {
        self.circular_return_signatures.get(&id).copied()
    }

    pub(super) fn set_function_signature_circular_return_type(
        &mut self,
        id: SignatureId,
        type_id: TypeId,
        annotation_type: TypeId,
    ) -> bool {
        let valid = self.signature_is_callable(id)
            && self.function_signature_return_annotations.contains_key(&id)
            && self.types.get(annotation_type).is_some()
            && self
                .intrinsic_bootstrap
                .as_ref()
                .is_some_and(|bootstrap| type_id == bootstrap.any_type)
            && self
                .signature(id)
                .is_some_and(|signature| signature.resolved_return_type().is_none())
            && !self.circular_return_signatures.contains_key(&id);
        if !valid {
            return false;
        }
        let previous = self.circular_return_signatures.insert(id, annotation_type);
        assert!(
            previous.is_none(),
            "the circular-return marker was checked absent"
        );
        let published = self.signatures.set_resolved_return_type(id, Some(type_id));
        assert!(published, "the local function signature was prevalidated");
        self.mark_union_cache_validation_dirty();
        true
    }

    pub fn set_signature_resolved_type_predicate(
        &mut self,
        id: SignatureId,
        predicate: Option<TypePredicateId>,
    ) -> bool {
        if !self.valid_optional_predicate(predicate) {
            return false;
        }
        let dirty = self.signature_is_callable(id);
        if !self.signatures.set_resolved_type_predicate(id, predicate) {
            return false;
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub fn set_signature_isolated_type(
        &mut self,
        id: SignatureId,
        type_id: Option<TypeId>,
    ) -> bool {
        if !self.valid_optional_type(type_id) {
            return false;
        }
        let dirty = self.signature_is_callable(id);
        if !self.signatures.set_isolated_signature_type(id, type_id) {
            return false;
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
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
        let dirty = self.signature_is_callable(id);
        if !self.signatures.set_target_and_mapper(id, target, mapper) {
            return false;
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
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
        let dirty = self.signature_is_callable(id);
        if !self.signatures.set_composite(id, composite) {
            return false;
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
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
        let dirty = self.signature_is_callable(id);
        if !self.signatures.set_flags(id, flags) {
            return false;
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
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
        let dirty = self.signature_is_callable(id);
        if !self.signatures.set_type_parameters(id, type_parameters) {
            return false;
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
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
        let dirty = self.signature_is_callable(id);
        if !self.signatures.set_this_parameter(id, this_parameter) {
            return false;
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
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

    pub(super) fn try_reserve_index_infos(&mut self, additional: usize) -> bool {
        self.index_infos.try_reserve(additional)
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

    fn node_has_kind(&self, node: NodeRef, predicate: impl FnOnce(SyntaxKind) -> bool) -> bool {
        self.source_node_kind(node).is_some_and(predicate)
    }

    fn node_is_source_reachable(&self, node: NodeRef) -> bool {
        self.source_node_fact(node).is_some()
    }

    fn node_is_signature_links_eligible(&self, node: NodeRef) -> bool {
        self.source_node_fact(node)
            .is_some_and(|facts| facts.signature_links_eligible)
    }

    /// Returns the registered syntax kind for a source-reachable node.
    #[must_use]
    pub(super) fn source_node_kind(&self, node: NodeRef) -> Option<SyntaxKind> {
        self.source_node_fact(node).map(|facts| facts.kind)
    }

    /// Returns the registered parent of a source-reachable node. The outer
    /// outer `Option` distinguishes an unknown node from a registered root.
    #[must_use]
    pub(super) fn source_node_parent(&self, node: NodeRef) -> Option<SourceNodeParent> {
        self.source_node_fact(node).map(|facts| {
            facts.parent.map_or(SourceNodeParent::Root, |parent| {
                SourceNodeParent::Parent(NodeRef::new(node.arena, node.file, parent))
            })
        })
    }

    #[must_use]
    pub(super) fn source_node_is_exported(&self, node: NodeRef) -> Option<bool> {
        self.source_node_fact(node).map(|facts| facts.exported)
    }

    fn source_node_fact(&self, node: NodeRef) -> Option<SourceNodeFacts> {
        if !self.contains_node_ref(node) {
            return None;
        }
        self.source_node_facts
            .get(&node.arena)
            .and_then(|facts| facts.get(node.node.index()))
            .copied()
            .flatten()
    }

    fn validated_source_node_facts(
        arena: &NodeArena,
        source_file: NodeId,
    ) -> Option<Vec<Option<SourceNodeFacts>>> {
        let mut facts = vec![None; arena.len()];
        let mut pending = vec![(source_file, None)];
        while let Some((node_id, expected_parent)) = pending.pop() {
            let slot = facts.get_mut(node_id.index())?;
            if slot.is_some() {
                return None;
            }
            let node = arena.get(node_id)?;
            if node.parent != expected_parent || !node.data.matches_syntax_kind(node.kind) {
                return None;
            }
            *slot = Some(SourceNodeFacts {
                kind: node.kind,
                parent: node.parent,
                exported: match &node.data {
                    NodeData::TypeAliasDeclaration(declaration) => {
                        declaration.modifiers.as_ref().is_some_and(|modifiers| {
                            modifiers.list.nodes.iter().any(|modifier| {
                                arena.get(*modifier).is_some_and(|modifier| {
                                    modifier.kind == SyntaxKind::ExportKeyword
                                })
                            })
                        })
                    }
                    NodeData::InterfaceDeclaration(declaration) => {
                        declaration.modifiers.as_ref().is_some_and(|modifiers| {
                            modifiers.list.nodes.iter().any(|modifier| {
                                arena.get(*modifier).is_some_and(|modifier| {
                                    modifier.kind == SyntaxKind::ExportKeyword
                                })
                            })
                        })
                    }
                    _ => false,
                },
                signature_links_eligible: Self::is_signature_links_eligible(arena, node),
            });
            node.for_each_child(|child| pending.push((child, Some(node_id))));
        }
        Some(facts)
    }

    fn is_signature_links_eligible(arena: &NodeArena, node: &ts_ast::Node) -> bool {
        if let NodeData::BinaryExpression(binary) = &node.data {
            return arena
                .get(binary.operator_token)
                .is_some_and(|operator| operator.kind == SyntaxKind::InstanceOfKeyword);
        }
        matches!(
            node.kind,
            SyntaxKind::MethodSignature
                | SyntaxKind::MethodDeclaration
                | SyntaxKind::Constructor
                | SyntaxKind::GetAccessor
                | SyntaxKind::SetAccessor
                | SyntaxKind::CallSignature
                | SyntaxKind::ConstructSignature
                | SyntaxKind::IndexSignature
                | SyntaxKind::FunctionType
                | SyntaxKind::ConstructorType
                | SyntaxKind::FunctionExpression
                | SyntaxKind::ArrowFunction
                | SyntaxKind::FunctionDeclaration
                | SyntaxKind::JsDocSignature
                | SyntaxKind::JsxOpeningElement
                | SyntaxKind::JsxSelfClosingElement
                | SyntaxKind::JsxOpeningFragment
                | SyntaxKind::CallExpression
                | SyntaxKind::NewExpression
                | SyntaxKind::TaggedTemplateExpression
                | SyntaxKind::Decorator
                | SyntaxKind::ClassDeclaration
                | SyntaxKind::ClassExpression
                | SyntaxKind::Parameter
                | SyntaxKind::PropertyDeclaration
        )
    }

    fn valid_source_node(&self, source_file: SourceFileRef, node: NodeRef) -> bool {
        let source = source_file.node_ref();
        self.contains_source_file(source_file)
            && self.contains_node_ref(node)
            && node.is_for(source.arena, source.file)
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

    fn valid_optional_symbol_sequence(&self, sequence: &OptionalSymbolSequence) -> bool {
        sequence
            .as_slice()
            .is_none_or(|ids| self.valid_symbols(ids))
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
    pub(super) fn try_reserve_direct_interface_heritage_provenance(
        &mut self,
        additional: usize,
    ) -> bool {
        self.direct_interface_heritage_provenance
            .try_reserve(additional)
            .is_ok()
    }

    pub(super) fn direct_interface_heritage_provenance(
        &self,
        type_: TypeId,
    ) -> Option<DirectInterfaceHeritageProvenance> {
        self.direct_interface_heritage_provenance
            .get(&type_)
            .copied()
    }

    /// Publishes one source-planned direct-base edge exactly once.
    ///
    /// Callers reserve the map slot before beginning their semantic transaction.
    /// Both declared-type links are authoritative by the time heritage members
    /// resolve, so accepting only those identities prevents a coherent but
    /// source-wrong `resolved_base_types` cache from reaching structural relation.
    pub(super) fn publish_direct_interface_heritage_provenance(
        &mut self,
        type_: TypeId,
        provenance: DirectInterfaceHeritageProvenance,
    ) -> bool {
        let owner_is_exact = self.type_payload(type_).is_some_and(|record| {
            matches!(record.data(), TypeData::Interface(_))
                && record.symbol() == Some(provenance.owner_symbol)
        }) && self.get_merged_symbol(provenance.owner_symbol)
            == Some(provenance.owner_symbol)
            && self
                .declared_type_links(provenance.owner_symbol)
                .is_some_and(|links| links.declared_type == Some(type_));
        let base_is_exact = self
            .type_payload(provenance.base_type)
            .is_some_and(|record| {
                matches!(record.data(), TypeData::Interface(_))
                    && record.symbol() == Some(provenance.base_symbol)
            })
            && self.get_merged_symbol(provenance.base_symbol) == Some(provenance.base_symbol)
            && self
                .declared_type_links(provenance.base_symbol)
                .is_some_and(|links| links.declared_type == Some(provenance.base_type));
        if provenance.owner_symbol == provenance.base_symbol || !owner_is_exact || !base_is_exact {
            return false;
        }
        let std::collections::hash_map::Entry::Vacant(entry) =
            self.direct_interface_heritage_provenance.entry(type_)
        else {
            return false;
        };
        entry.insert(provenance);
        true
    }

    /// Publishes the type, signature, generic metadata, provenance reverse
    /// maps, owner barrier, return annotation, and signature link as one
    /// prevalidated transaction.
    ///
    /// No semantic identity or cache is mutated until every dependency and
    /// capacity has been checked. After the first allocation, all remaining
    /// writes are assertions over that frozen preflight.
    pub(super) fn publish_source_generic_callable(
        &mut self,
        prepared: PreparedSourceGenericCallablePublication<'_>,
    ) -> Option<(TypeId, SignatureId)> {
        let resolution_states = self.validate_source_generic_type_parameters(
            prepared.syntax,
            prepared.declaration,
            &prepared.type_parameters,
        )?;
        let generic_return_type_parameter_valid = self
            .source_generic_return_type_parameter_is_exact(
                prepared.syntax,
                prepared.return_annotation,
                prepared.generic_return_type_parameter,
                &prepared.type_parameters,
            );
        let owner = self.symbol(prepared.owner_symbol)?;
        let owner_valid = owner.flags() == SymbolFlags::FUNCTION
            && owner.check_flags() == CheckFlags::NONE
            && owner.declarations() == Some(&[prepared.declaration])
            && owner.value_declaration() == Some(prepared.declaration)
            && owner.members().is_none()
            && owner.exports().is_none()
            && owner.parent() == prepared.owner_parent
            && owner.export_symbol().is_none()
            && self.get_merged_symbol(prepared.owner_symbol) == Some(prepared.owner_symbol);
        let export_route_valid = match (prepared.owner_parent, prepared.export_local) {
            (None, None) => owner.parent().is_none(),
            (Some(parent), Some(local)) if owner.parent() == Some(parent) => {
                self.symbol(parent).is_some()
                    && self.get_merged_symbol(parent) == Some(parent)
                    && self.symbol(local).is_some_and(|local_record| {
                        local_record.flags() == SymbolFlags::EXPORT_VALUE
                            && local_record.check_flags() == CheckFlags::NONE
                            && local_record.name() == owner.name()
                            && local_record.declarations() == Some(&[prepared.declaration])
                            && local_record.value_declaration().is_none()
                            && local_record.members().is_none()
                            && local_record.exports().is_none()
                            && local_record.parent().is_none()
                            && local_record.export_symbol() == Some(prepared.owner_symbol)
                            && self.get_merged_symbol(local) == Some(local)
                    })
            }
            _ => false,
        };
        let parameters_valid = prepared.parameters.iter().enumerate().all(|(index, parameter)| {
            *parameter != prepared.owner_symbol
                && !prepared.parameters[..index].contains(parameter)
                && self.symbol(*parameter).is_some_and(|symbol| {
                    symbol.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                        && symbol.check_flags() == CheckFlags::NONE
                        && symbol.declarations().is_some_and(|declarations| {
                            matches!(declarations, [declaration]
                                if self.source_node_kind(*declaration) == Some(SyntaxKind::Parameter)
                                    && self.source_node_parent(*declaration)
                                        == Some(SourceNodeParent::Parent(prepared.declaration)))
                        })
                        && symbol.value_declaration()
                            == symbol.declarations().and_then(|declarations| declarations.first()).copied()
                        && symbol.members().is_none()
                        && symbol.exports().is_none()
                        && symbol.parent().is_none()
                        && symbol.export_symbol().is_none()
                        && self.get_merged_symbol(*parameter) == Some(*parameter)
                })
                && self
                    .value_symbol_links(*parameter)
                    .is_none_or(|links| links == &ValueSymbolLinks::default())
        });
        let return_annotation_valid = self
            .source_return_annotation_belongs_to(prepared.declaration, prepared.return_annotation);
        let expected_minimum = i32::try_from(prepared.parameters.len()).ok();
        let owner_links_cold = self
            .value_symbol_links(prepared.owner_symbol)
            .is_none_or(|links| links == &ValueSymbolLinks::default());
        let signature_links_cold = self
            .signature_links(prepared.declaration)
            .is_none_or(|links| links == &SignatureLinks::default());
        if prepared.type_parameters.is_empty()
            || prepared.family != SourceCallableFamily::FunctionDeclaration
            || prepared.syntax.declaration() != prepared.declaration
            || self.source_node_kind(prepared.declaration) != Some(SyntaxKind::FunctionDeclaration)
            || prepared.flags != SignatureFlags::NONE
            || expected_minimum != Some(prepared.min_argument_count)
            || !owner_valid
            || !export_route_valid
            || !parameters_valid
            || !owner_links_cold
            || !signature_links_cold
            || !return_annotation_valid
            || !generic_return_type_parameter_valid
            || prepared
                .export_local
                .is_some_and(|local| !self.symbols.contains_symbol(local))
            || prepared.export_local == Some(prepared.owner_symbol)
            || self.source_callable_provenance.values().any(|provenance| {
                provenance.declaration == prepared.declaration
                    || provenance.owner_symbol == prepared.owner_symbol
            })
            || self
                .source_callable_types_by_declaration
                .contains_key(&prepared.declaration)
            || self
                .source_callable_types_by_owner
                .contains_key(&prepared.owner_symbol)
            || self.source_callable_type_parameters.values().any(|rows| {
                rows.iter().any(|row| {
                    prepared.type_parameters.iter().any(|prepared| {
                        let provenance = prepared.provenance;
                        // Each retained dimension is a unique ownership edge.
                        // Reusing only a symbol or TypeId under a different
                        // declaration would still let two signatures claim
                        // one canonical type-parameter identity.
                        provenance.declaration == row.declaration
                            || provenance.symbol == row.symbol
                            || provenance.type_parameter == row.type_parameter
                    })
                })
            })
        {
            return None;
        }

        // These heap allocations are deliberately completed before the first
        // callable TypeId or SignatureId is allocated. Everything after that
        // identity boundary is a reserved, infallible publication step.
        let provenance_rows = prepared
            .type_parameters
            .iter()
            .map(|row| row.provenance)
            .collect::<Box<[_]>>();
        let type_parameter_ids = prepared
            .type_parameters
            .iter()
            .map(|row| row.provenance.type_parameter)
            .collect::<Vec<_>>();
        let value_link_reservations = prepared.parameters.len().checked_add(1)?;
        if !self.try_reserve_types(1)
            || !self.try_reserve_signatures(1)
            || !self.try_reserve_source_callable_provenance(1)
            || !self.try_reserve_function_signature_return_annotations(1)
            || !self.links.signature.try_reserve(1)
            || !self.links.value_symbol.try_reserve(value_link_reservations)
        {
            return None;
        }

        let type_ = self
            .alloc_plain_object_type(
                super::types::ObjectFlags::ANONYMOUS,
                Some(prepared.owner_symbol),
            )
            .expect("the source generic owner was prevalidated");
        let signature = self
            .alloc_signature(
                prepared.flags,
                Some(prepared.declaration),
                type_parameter_ids,
                None,
                prepared.parameters,
                None,
                None,
                prepared.min_argument_count,
            )
            .expect("the source generic signature was prevalidated");

        for (row, state) in prepared.type_parameters.iter().zip(resolution_states) {
            if state == SourceTypeParameterResolutionState::Cold {
                assert!(self.set_type_parameter_resolution(
                    row.provenance.type_parameter,
                    Some(row.constraint),
                    None,
                    None,
                    Some(row.default_type),
                ));
            }
        }
        assert!(
            self.source_callable_type_parameters
                .insert(signature, provenance_rows)
                .is_none()
        );
        let provenance = SourceCallableProvenance {
            family: prepared.family,
            declaration: prepared.declaration,
            owner_symbol: prepared.owner_symbol,
            owner_parent: prepared.owner_parent,
            export_local: prepared.export_local,
            signature,
            return_provenance: SourceCallableReturnProvenance::Annotated,
            array_targets: prepared.array_targets,
            generic_return_type_parameter: prepared.generic_return_type_parameter,
            contextual_target: None,
            contextual_variable: None,
        };
        assert!(
            self.source_callable_provenance
                .insert(type_, provenance)
                .is_none()
        );
        assert!(
            self.source_callable_types_by_declaration
                .insert(prepared.declaration, type_)
                .is_none()
        );
        assert!(
            self.source_callable_types_by_owner
                .insert(prepared.owner_symbol, type_)
                .is_none()
        );
        assert!(
            self.source_callable_types_by_signature
                .insert(signature, type_)
                .is_none()
        );
        assert!(
            self.function_signature_return_annotations
                .insert(
                    signature,
                    (
                        prepared.return_annotation,
                        prepared.return_null_literal_identity,
                    ),
                )
                .is_none()
        );
        assert!(self.set_value_symbol_links(
            prepared.owner_symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(self.set_structured_type_members(type_, None, None, None, None, None));
        assert!(self.set_signature_links(
            prepared.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        Some((type_, signature))
    }

    fn source_generic_return_type_parameter_is_exact(
        &self,
        syntax: &SourceCallableTypeParameterSyntaxProof,
        annotation: NodeRef,
        return_type_parameter: Option<TypeId>,
        resolved: &[ResolvedSourceCallableTypeParameter],
    ) -> bool {
        match (
            syntax.generic_return_type_parameter_declaration(),
            return_type_parameter,
            syntax.generic_fixed_return_is_exact(),
        ) {
            (None, None, true) => {
                self.source_node_kind(annotation) != Some(SyntaxKind::TypeReference)
            }
            (Some(declaration), Some(type_parameter), false) => {
                let Some(row) = resolved.iter().find(|row| {
                    row.provenance.declaration == declaration
                        && row.provenance.type_parameter == type_parameter
                }) else {
                    return false;
                };
                if self.source_node_kind(annotation) != Some(SyntaxKind::TypeReference) {
                    return false;
                }
                let symbol_links = self.symbol_node_links(annotation);
                let type_links = self.type_node_links(annotation);
                let cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default())
                    && type_links.is_none_or(|links| links == &TypeNodeLinks::default());
                let warm = symbol_links
                    == Some(&SymbolNodeLinks {
                        resolved_symbol: Some(row.provenance.symbol),
                    })
                    && type_links
                        == Some(&TypeNodeLinks {
                            resolved_type: Some(type_parameter),
                            outer_type_parameters: None,
                        });
                cold || warm
            }
            _ => false,
        }
    }

    fn validate_source_generic_type_parameters(
        &self,
        syntax: &SourceCallableTypeParameterSyntaxProof,
        declaration: NodeRef,
        resolved: &[ResolvedSourceCallableTypeParameter],
    ) -> Option<Vec<SourceTypeParameterResolutionState>> {
        let no_constraint = self.intrinsic_bootstrap.as_ref()?.no_constraint_type;
        if syntax.declaration() != declaration || syntax.rows().len() != resolved.len() {
            return None;
        }
        let mut declarations = HashSet::with_capacity(resolved.len());
        let mut symbols = HashSet::with_capacity(resolved.len());
        let mut type_parameters = HashSet::with_capacity(resolved.len());
        let mut expected_bases = Vec::with_capacity(resolved.len());
        let mut states = Vec::with_capacity(resolved.len());
        let mut default_seen = false;
        let computed_type_variable_flags = super::types::ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | super::types::ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;

        for (index, (syntax_row, row)) in syntax.rows().iter().zip(resolved).enumerate() {
            let provenance = row.provenance;
            if syntax_row.declaration() != provenance.declaration
                || syntax_row.constraint() != provenance.constraint
                || syntax_row.default_type() != provenance.default_type
                || !declarations.insert(provenance.declaration)
                || !symbols.insert(provenance.symbol)
                || !type_parameters.insert(provenance.type_parameter)
            {
                return None;
            }
            let record = self.type_payload(provenance.type_parameter)?;
            let TypeData::TypeParameter(data) = record.data() else {
                return None;
            };
            let symbol_record = self.symbol(provenance.symbol)?;
            let exact_declared_links = self.declared_type_links(provenance.symbol)
                == Some(&DeclaredTypeLinks {
                    declared_type: Some(provenance.type_parameter),
                    ..DeclaredTypeLinks::default()
                });
            let constraint_link_valid = match provenance.constraint {
                Some(node) => {
                    row.constraint != no_constraint
                        && self.source_type_node_result_is_exact(
                            node,
                            row.constraint,
                            &resolved[..index],
                        )
                }
                None => row.constraint == no_constraint,
            };
            let default_link_valid = match provenance.default_type {
                Some(node) => {
                    row.default_type != no_constraint
                        && self.source_type_node_result_is_exact(
                            node,
                            row.default_type,
                            &resolved[..index],
                        )
                }
                None => row.default_type == no_constraint,
            };
            let trailing_default_valid = !default_seen || provenance.default_type.is_some();
            default_seen |= provenance.default_type.is_some();
            let exact_constraint_default_pair = provenance.constraint.is_none()
                || provenance.default_type.is_none()
                || row.constraint == row.default_type;
            if record.flags() != super::types::TypeFlags::TYPE_PARAMETER
                || (record.object_flags() != super::types::ObjectFlags::NONE
                    && record.object_flags() != computed_type_variable_flags)
                || record.symbol() != Some(provenance.symbol)
                || record.alias().is_some()
                || data.is_this_type
                || symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
                || symbol_record.check_flags() != CheckFlags::NONE
                || symbol_record.declarations() != Some(&[provenance.declaration])
                || symbol_record.value_declaration().is_some()
                || symbol_record.members().is_some()
                || symbol_record.exports().is_some()
                || symbol_record.parent().is_some()
                || symbol_record.export_symbol().is_some()
                || self.get_merged_symbol(provenance.symbol) != Some(provenance.symbol)
                || !exact_declared_links
                || self.source_node_kind(provenance.declaration) != Some(SyntaxKind::TypeParameter)
                || self.source_node_parent(provenance.declaration)
                    != Some(SourceNodeParent::Parent(declaration))
                || !constraint_link_valid
                || !default_link_valid
                || !trailing_default_valid
                || !exact_constraint_default_pair
                || self.type_payload(row.constraint).is_none()
                || self.type_payload(row.default_type).is_none()
            {
                return None;
            }

            let expected_base = match provenance.constraint {
                None => no_constraint,
                Some(_) => {
                    if let Some(earlier) = resolved[..index]
                        .iter()
                        .position(|candidate| candidate.provenance.type_parameter == row.constraint)
                    {
                        expected_bases[earlier]
                    } else if self.source_direct_constraint_has_leaf_base(row.constraint) {
                        row.constraint
                    } else {
                        return None;
                    }
                }
            };
            expected_bases.push(expected_base);
            if data
                .constrained
                .resolved_base_constraint
                .is_some_and(|base| base != expected_base)
                || data.target.is_some()
                || data.mapper.is_some()
            {
                return None;
            }
            let state = if data.constraint.is_none()
                && data.resolved_default_type.is_none()
                && data.constrained.resolved_base_constraint.is_none()
            {
                SourceTypeParameterResolutionState::Cold
            } else if data.constraint == Some(row.constraint)
                && data.resolved_default_type == Some(row.default_type)
            {
                SourceTypeParameterResolutionState::Warm
            } else {
                return None;
            };
            states.push(state);
        }
        Some(states)
    }

    fn source_direct_constraint_has_leaf_base(&self, constraint: TypeId) -> bool {
        let Some(bootstrap) = self.intrinsic_bootstrap.as_ref() else {
            return false;
        };
        [
            bootstrap.any_type,
            bootstrap.unknown_type,
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.bigint_type,
            bootstrap.boolean_type,
            bootstrap.es_symbol_type,
            bootstrap.void_type,
            bootstrap.undefined_type,
            bootstrap.null_type,
            bootstrap.never_type,
            bootstrap.non_primitive_type,
            bootstrap.intrinsic_marker_type,
        ]
        .contains(&constraint)
            || matches!(
                self.type_payload(constraint).map(TypeRecord::data),
                Some(TypeData::Literal(_) | TypeData::UniqueEsSymbol(_))
            )
    }

    pub(super) fn source_type_node_result_is_exact(
        &self,
        node: NodeRef,
        result: TypeId,
        earlier: &[ResolvedSourceCallableTypeParameter],
    ) -> bool {
        let Some(bootstrap) = self.intrinsic_bootstrap.as_ref() else {
            return false;
        };
        let kind = self.source_node_kind(node);
        let intrinsic = match kind {
            Some(SyntaxKind::AnyKeyword) => Some(bootstrap.any_type),
            Some(SyntaxKind::UnknownKeyword) => Some(bootstrap.unknown_type),
            Some(SyntaxKind::StringKeyword) => Some(bootstrap.string_type),
            Some(SyntaxKind::NumberKeyword) => Some(bootstrap.number_type),
            Some(SyntaxKind::BigIntKeyword) => Some(bootstrap.bigint_type),
            Some(SyntaxKind::BooleanKeyword) => Some(bootstrap.boolean_type),
            Some(SyntaxKind::SymbolKeyword) => Some(bootstrap.es_symbol_type),
            Some(SyntaxKind::VoidKeyword) => Some(bootstrap.void_type),
            Some(SyntaxKind::UndefinedKeyword) => Some(bootstrap.undefined_type),
            Some(SyntaxKind::NullKeyword) => Some(bootstrap.null_type),
            Some(SyntaxKind::NeverKeyword) => Some(bootstrap.never_type),
            Some(SyntaxKind::ObjectKeyword) => Some(bootstrap.non_primitive_type),
            Some(SyntaxKind::IntrinsicKeyword) => Some(bootstrap.intrinsic_marker_type),
            _ => None,
        };
        if let Some(intrinsic) = intrinsic {
            let type_links_valid = self.type_node_links(node).is_none_or(|links| {
                links == &TypeNodeLinks::default()
                    || links
                        == &TypeNodeLinks {
                            resolved_type: Some(result),
                            outer_type_parameters: None,
                        }
            });
            let symbol_links_valid = self
                .symbol_node_links(node)
                .is_none_or(|links| links == &SymbolNodeLinks::default());
            return result == intrinsic && type_links_valid && symbol_links_valid;
        }

        // The opaque source proof does not yet retain enough structure to
        // authenticate aliases or composite type syntax. The one supported
        // non-keyword result is an exact reference to an earlier prepared
        // type parameter, proven by both canonical query links.
        if kind != Some(SyntaxKind::TypeReference) {
            return false;
        }
        let Some(earlier) = earlier
            .iter()
            .find(|row| row.provenance.type_parameter == result)
        else {
            return false;
        };
        self.type_node_links(node)
            == Some(&TypeNodeLinks {
                resolved_type: Some(result),
                outer_type_parameters: None,
            })
            && self.symbol_node_links(node)
                == Some(&SymbolNodeLinks {
                    resolved_symbol: Some(earlier.provenance.symbol),
                })
    }

    fn source_return_annotation_belongs_to(
        &self,
        declaration: NodeRef,
        annotation: NodeRef,
    ) -> bool {
        let Some(kind) = self.source_node_kind(annotation) else {
            return false;
        };
        if !kind.is_keyword_type()
            && ((kind as u16) < (SyntaxKind::FIRST_TYPE_NODE as u16)
                || (kind as u16) > (SyntaxKind::LAST_TYPE_NODE as u16))
        {
            return false;
        }
        let mut current = annotation;
        loop {
            let Some(SourceNodeParent::Parent(parent)) = self.source_node_parent(current) else {
                return false;
            };
            if parent == declaration {
                return true;
            }
            if self.source_node_kind(parent) != Some(SyntaxKind::ParenthesizedType) {
                return false;
            }
            current = parent;
        }
    }

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

    use ts_ast::{
        FileId, IdentifierData, Node, NodeArena, NodeData, NodeFlags, NodeId, NodeRef,
        QualifiedNameData, SyntaxKind,
    };
    use ts_binder::{EscapedName, SymbolData, SymbolFlags, SymbolStore};
    use ts_core::TextRange;
    use ts_parser::{parse_isolated_entity_name, parse_source_file};

    use super::{AstScope, CachedSignatureLookup, SemanticStore, type_list_key};
    use crate::semantic::{
        AccessibleChainCacheKey, AliasSymbolLinks, AliasTargetState, ArrayLiteralLinks,
        AssertionLinks, CacheHashKey, CanonicalTypeMapperStore, ContainingSymbolLinks,
        DeclaredTypeLinks, DecoratorSignatureState, DeferredSymbolLinks, EffectsSignatureState,
        EntityNameNode, EnumMemberLinks, EvaluatorResult, EvaluatorValue, ExhaustiveState,
        ExportTypeLinks, ExtendedContainersState, ExternalEmitHelpers, IntrinsicBootstrapOptions,
        JsxElementLinks, JsxFlags, LateBoundLinks, MappedSymbolLinks, MarkedAssignmentSymbolLinks,
        MembersAndExportsLinks, ModuleSymbolLinks, NodeCheckFlags, NodeLinks,
        OptionalSymbolSequence, OrderedNodeSet, RelationComparisonResult, RelationKind,
        ResolvedSignatureState, ReverseMappedSymbolLinks, SignatureLinks, SourceFileLinks,
        SpreadLinks, SwitchStatementLinks, SymbolNodeLinks, SymbolReferenceLinks, TypeAliasLinks,
        TypeNodeLinks, TypeRecord, TypeResolutionTarget, TypeSystemPropertyName, ValueSymbolLinks,
        VarianceFlags, VarianceLinks,
        signatures::{ElementFlags, SignatureFlags, TypePredicateKind},
        types::{ObjectFlags, TypeFlags},
    };
    use ts_jsnum::Number;

    type TestStore = SemanticStore<&'static str, &'static str>;
    type CanonicalTestStore = SemanticStore<TypeRecord, &'static str>;

    #[test]
    fn source_keyword_result_requires_exact_null_identity_and_unpoisoned_links() {
        let parsed = parse_source_file("type Nullish = null;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_001);
        let mut store = CanonicalTypeMapperStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let null_node = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NullKeyword).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .expect("fixture has a null keyword");
        let literal_wrapper = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::LiteralType).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .expect("the parser wraps null in a literal type");
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let null = bootstrap.null_type;
        let number = bootstrap.number_type;

        assert!(store.source_type_node_result_is_exact(null_node, null, &[]));
        assert!(!store.source_type_node_result_is_exact(null_node, number, &[]));
        assert!(!store.source_type_node_result_is_exact(literal_wrapper, null, &[]));

        assert!(store.set_type_node_links(
            null_node,
            TypeNodeLinks {
                resolved_type: Some(number),
                outer_type_parameters: None,
            },
        ));
        assert!(!store.source_type_node_result_is_exact(null_node, null, &[]));
    }

    #[test]
    fn strict_function_types_claim_is_immutable() {
        let mut enabled = TestStore::new();
        assert_eq!(enabled.claimed_strict_function_types(), None);
        assert_eq!(enabled.claim_strict_function_types(true), Ok(()));
        assert_eq!(enabled.claimed_strict_function_types(), Some(true));
        assert_eq!(enabled.claim_strict_function_types(true), Ok(()));
        assert_eq!(enabled.claim_strict_function_types(false), Err(true));
        assert_eq!(enabled.claimed_strict_function_types(), Some(true));

        let mut disabled = TestStore::new();
        assert_eq!(disabled.claim_strict_function_types(false), Ok(()));
        assert_eq!(disabled.claim_strict_function_types(true), Err(false));
        assert_eq!(disabled.claimed_strict_function_types(), Some(false));
    }

    #[test]
    fn cached_signatures_retain_exact_arguments_and_publish_insert_only() {
        let mut store = TestStore::new();
        let argument = store.alloc_type("argument");
        let collision_argument = store.alloc_type("collision");
        let target = empty_signature(&mut store);
        let mapper = store.alloc_mapper("mapper");
        let instantiated = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(argument),
                None,
                0,
            )
            .unwrap();
        assert!(store.set_signature_target_and_mapper(instantiated, Some(target), Some(mapper)));
        let key = type_list_key(&[argument]);
        assert_eq!(
            store.cached_signature(target, key, &[argument]),
            CachedSignatureLookup::Missing
        );
        assert!(store.try_reserve_cached_signatures(1));
        assert!(store.set_cached_signature(target, key, Box::new([argument]), instantiated));
        assert_eq!(store.cached_signature_len(), 1);
        assert_eq!(
            store.cached_signature(target, key, &[argument]),
            CachedSignatureLookup::Hit(instantiated)
        );
        assert_eq!(
            store.cached_signature(target, key, &[collision_argument]),
            CachedSignatureLookup::Invalid
        );
        let collision_key = type_list_key(&[collision_argument]);
        assert_eq!(
            store.cached_signature(target, collision_key, &[collision_argument]),
            CachedSignatureLookup::Missing
        );
        let wrong_key = CacheHashKey::new(collision_key.get() ^ 1);
        assert!(!store.set_cached_signature(
            target,
            wrong_key,
            Box::new([collision_argument]),
            instantiated
        ));
        assert!(!store.set_cached_signature(target, key, Box::new([argument]), instantiated));
        assert_eq!(store.cached_signature_len(), 1);
    }

    #[test]
    fn mapper_reservation_failure_preserves_counts_and_allows_retry() {
        let mut store = TestStore::new();
        assert!(!store.try_reserve_mappers(usize::MAX));
        assert_eq!(store.mapper_len(), 0);
        assert!(store.try_reserve_mappers(1));
        store.alloc_mapper("mapper");
        assert_eq!(store.mapper_len(), 1);
    }

    #[test]
    fn index_info_reservation_failure_preserves_counts_and_allows_retry() {
        let mut store = TestStore::new();
        assert!(!store.try_reserve_index_infos(usize::MAX));
        assert_eq!(store.index_info_len(), 0);
        let key = store.alloc_type("key");
        let value = store.alloc_type("value");
        assert!(store.try_reserve_index_infos(1));
        assert!(
            store
                .alloc_index_info(key, value, false, None, Vec::new())
                .is_some()
        );
        assert_eq!(store.index_info_len(), 1);
    }

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

    fn node_ref_of_kind(arena: &NodeArena, file: FileId, kind: SyntaxKind) -> NodeRef {
        let node = arena
            .iter()
            .find_map(|(id, node)| (node.kind == kind).then_some(id))
            .unwrap_or_else(|| panic!("parsed source must contain {kind:?}"));
        NodeRef::new(arena.id(), file, node)
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
    fn relation_cache_owners_are_lazy_distinct_and_exact_through_the_store() {
        let mut store = TestStore::new();
        let key = CacheHashKey::from_halves(7, 11);
        for relation in RelationKind::ALL {
            assert!(!store.relation_cache_is_allocated(relation));
            assert_eq!(store.relation_cache_size(relation), 0);
            assert_eq!(store.relation_comparison_budget(relation), 2_000_000);
            assert_eq!(
                store.relation_cache_get(relation, key),
                RelationComparisonResult::NONE
            );
            assert!(!store.relation_cache_is_allocated(relation));
        }

        let values = [
            RelationComparisonResult::SUCCEEDED,
            RelationComparisonResult::FAILED,
            RelationComparisonResult::REPORTS_UNMEASURABLE,
            RelationComparisonResult::REPORTS_UNRELIABLE,
            RelationComparisonResult::STACK_DEPTH_OVERFLOW,
        ];
        for (relation, result) in RelationKind::ALL.into_iter().zip(values) {
            store.relation_cache_set(relation, key, result);
        }
        for (relation, result) in RelationKind::ALL.into_iter().zip(values) {
            assert_eq!(store.relation_cache_get(relation, key), result);
            assert_eq!(store.relation_cache_size(relation), 1);
            assert!(store.relation_cache_is_allocated(relation));
            assert_eq!(store.relation_comparison_budget(relation), 1_999_999);
        }
    }

    #[test]
    fn enum_relation_cache_uses_directional_global_symbol_identity_atomically() {
        let mut store = TestStore::new();
        let source = alloc_test_symbol(&mut store, "Source");
        let target = alloc_test_symbol(&mut store, "Target");
        assert_eq!(store.enum_relation_cache_size(), 0);
        assert_eq!(
            store.enum_relation_cache_get(source, target),
            Some(RelationComparisonResult::NONE)
        );
        assert_eq!(store.enum_relation_cache_size(), 0);

        assert!(
            store.enum_relation_cache_set(source, target, RelationComparisonResult::SUCCEEDED,)
        );
        assert_eq!(store.enum_relation_cache_size(), 1);
        assert_eq!(
            store.enum_relation_cache_get(source, target),
            Some(RelationComparisonResult::SUCCEEDED)
        );
        assert_eq!(
            store.enum_relation_cache_get(target, source),
            Some(RelationComparisonResult::NONE)
        );
        assert!(store.enum_relation_cache_set(target, source, RelationComparisonResult::FAILED,));
        assert_eq!(store.enum_relation_cache_size(), 2);

        let mut foreign = TestStore::new();
        let foreign_symbol = alloc_test_symbol(&mut foreign, "Foreign");
        let before = store.relation_state_snapshot();
        assert_eq!(store.enum_relation_cache_get(source, foreign_symbol), None);
        assert!(!store.enum_relation_cache_set(
            foreign_symbol,
            target,
            RelationComparisonResult::SUCCEEDED,
        ));
        assert_eq!(store.relation_state_snapshot(), before);
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
    fn source_file_tokens_validate_exact_roots_and_reject_cross_wiring_atomically() {
        let first = parse_source_file("type Value = Namespace.Member;");
        let second = parse_source_file("type Value = Namespace.Member;");
        let first_file = FileId::new(31);
        let second_file = FileId::new(32);
        let mut store = TestStore::new();

        let first_source = store
            .register_source_file(&first.arena, first.source_file, first_file)
            .unwrap();
        assert_eq!(first_source.file(), first_file);
        assert!(store.contains_source_file(first_source));
        assert_eq!(
            store.register_source_file(&first.arena, first.source_file, first_file),
            Some(first_source),
            "exact re-registration is idempotent"
        );

        let crossed_file_ref = NodeRef::new(first.arena.id(), second_file, first.source_file);
        assert_eq!(
            store.register_source_file(&first.arena, first.source_file, second_file),
            None
        );
        assert!(!store.contains_node_ref(crossed_file_ref));

        let crossed_arena_ref = NodeRef::new(second.arena.id(), first_file, second.source_file);
        assert_eq!(
            store.register_source_file(&second.arena, second.source_file, first_file),
            None
        );
        assert!(!store.contains_node_ref(crossed_arena_ref));
        assert!(store.contains_source_file(first_source));

        let second_source = store
            .register_source_file(&second.arena, second.source_file, second_file)
            .unwrap();
        assert!(store.contains_source_file(second_source));

        let mut invalid_arena = NodeArena::new();
        let mut invalid_root = first.arena.get(first.source_file).unwrap().clone();
        invalid_root.parent = Some(NodeId::new(0));
        let invalid_root = invalid_arena.alloc(invalid_root);
        assert_eq!(
            store.register_source_file(&invalid_arena, invalid_root, FileId::new(33)),
            None
        );
        assert!(!store.contains_node_ref(NodeRef::new(
            invalid_arena.id(),
            FileId::new(33),
            invalid_root
        )));
    }

    #[test]
    fn source_file_tokens_reject_the_same_root_registered_by_another_store() {
        let parsed = parse_source_file("type Value = string;");
        let file = FileId::new(34);
        let mut first = TestStore::new();
        let mut second = TestStore::new();
        let first_source = first
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let second_source = second
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();

        assert_eq!(first_source.node_ref(), second_source.node_ref());
        assert_ne!(first_source, second_source);
        assert!(first.contains_source_file(first_source));
        assert!(!first.contains_source_file(second_source));
        assert!(second.contains_source_file(second_source));
        assert!(!second.contains_source_file(first_source));
    }

    #[test]
    fn source_kind_branding_validates_reachable_payloads_and_ignores_discarded_nodes() {
        let mut mismatched = parse_source_file("const value = 1;");
        let identifier = mismatched
            .arena
            .iter()
            .find_map(|(id, node)| (node.kind == SyntaxKind::Identifier).then_some(id))
            .unwrap();
        mismatched.arena.get_mut(identifier).unwrap().kind = SyntaxKind::EnumMember;

        let mut store = TestStore::new();
        let mismatched_file = FileId::new(34);
        let mismatched_ref = NodeRef::new(mismatched.arena.id(), mismatched_file, identifier);
        let before = store.checker_link_allocated_lengths();
        assert_eq!(
            store.register_source_file(&mismatched.arena, mismatched.source_file, mismatched_file),
            None
        );
        assert!(!store.contains_node_ref(mismatched_ref));
        assert!(!store.ensure_enum_member_links(mismatched_ref));
        assert_eq!(store.checker_link_allocated_lengths(), before);

        let mut parsed = parse_source_file("enum E { A }");
        let file = FileId::new(35);
        let member = parsed
            .arena
            .iter()
            .find_map(|(id, node)| (node.kind == SyntaxKind::EnumMember).then_some(id))
            .unwrap();
        let mut discarded = parsed.arena.get(member).unwrap().clone();
        discarded.parent = None;
        let discarded = parsed.arena.alloc(discarded);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );

        let member = NodeRef::new(parsed.arena.id(), file, member);
        let discarded = NodeRef::new(parsed.arena.id(), file, discarded);
        assert!(store.contains_node_ref(discarded));
        assert!(store.ensure_enum_member_links(member));
        let before = store.checker_link_allocated_lengths();
        assert!(!store.ensure_enum_member_links(discarded));
        assert!(!store.ensure_jsx_element_links(discarded));
        assert_eq!(store.enum_member_links(discarded), None);
        assert_eq!(store.jsx_element_links(discarded), None);
        assert_eq!(store.checker_link_allocated_lengths(), before);
    }

    #[test]
    fn specialized_node_links_enforce_their_pinned_call_domains_atomically() {
        let parsed = parse_source_file(
            "enum E { A } const asserted = value as string; \
             const angled = <string>value; const array = [...items]; \
             switch (value) { case 0: break; } factory(); \
             const sum = left + right; const test = value instanceof Factory;",
        );
        let file = FileId::new(37);
        let mut store = TestStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );

        let ordinary = node_ref_of_kind(&parsed.arena, file, SyntaxKind::Identifier);
        let enum_member = node_ref_of_kind(&parsed.arena, file, SyntaxKind::EnumMember);
        let as_expression = node_ref_of_kind(&parsed.arena, file, SyntaxKind::AsExpression);
        let type_assertion =
            node_ref_of_kind(&parsed.arena, file, SyntaxKind::TypeAssertionExpression);
        let array = node_ref_of_kind(&parsed.arena, file, SyntaxKind::ArrayLiteralExpression);
        let switch = node_ref_of_kind(&parsed.arena, file, SyntaxKind::SwitchStatement);
        let call = node_ref_of_kind(&parsed.arena, file, SyntaxKind::CallExpression);
        let binary_with_operator = |operator_kind| {
            parsed
                .arena
                .iter()
                .find_map(|(id, node)| {
                    let NodeData::BinaryExpression(binary) = &node.data else {
                        return None;
                    };
                    parsed
                        .arena
                        .get(binary.operator_token)
                        .is_some_and(|operator| operator.kind == operator_kind)
                        .then_some(NodeRef::new(parsed.arena.id(), file, id))
                })
                .unwrap_or_else(|| panic!("parsed source must contain {operator_kind:?}"))
        };
        let addition = binary_with_operator(SyntaxKind::PlusToken);
        let instance_of = binary_with_operator(SyntaxKind::InstanceOfKeyword);

        let before = store.checker_link_allocated_lengths();
        assert!(!store.ensure_enum_member_links(ordinary));
        assert!(!store.set_enum_member_links(ordinary, EnumMemberLinks::default()));
        assert!(!store.ensure_assertion_links(ordinary));
        assert!(!store.set_assertion_links(ordinary, AssertionLinks::default()));
        assert!(!store.ensure_array_literal_links(ordinary));
        assert!(!store.set_array_literal_links(ordinary, ArrayLiteralLinks::default()));
        assert!(!store.ensure_switch_statement_links(ordinary));
        assert!(!store.set_switch_statement_links(ordinary, SwitchStatementLinks::default()));
        assert!(!store.ensure_signature_links(ordinary));
        assert!(!store.set_signature_links(ordinary, SignatureLinks::default()));
        assert!(!store.ensure_signature_links(addition));
        assert!(!store.set_signature_links(addition, SignatureLinks::default()));
        assert_eq!(store.checker_link_allocated_lengths(), before);

        assert!(store.ensure_enum_member_links(enum_member));
        assert!(store.ensure_assertion_links(as_expression));
        assert!(store.ensure_assertion_links(type_assertion));
        assert!(store.ensure_array_literal_links(array));
        assert!(store.ensure_switch_statement_links(switch));
        assert!(store.ensure_signature_links(call));
        assert!(store.ensure_signature_links(instance_of));
        assert!(
            store.ensure_jsx_element_links(ordinary),
            "JSX namespace caching accepts arbitrary source locations upstream"
        );

        let foreign = parse_source_file("const ordinary = 1;");
        let foreign_file = FileId::new(38);
        let foreign_node = node_ref_of_kind(&foreign.arena, foreign_file, SyntaxKind::Identifier);
        let mut foreign_store = TestStore::new();
        assert!(
            foreign_store
                .register_source_file(&foreign.arena, foreign.source_file, foreign_file)
                .is_some()
        );
        let before = store.checker_link_allocated_lengths();
        assert!(!store.ensure_jsx_element_links(foreign_node));
        assert!(!store.set_jsx_element_links(foreign_node, JsxElementLinks::default()));
        assert_eq!(store.jsx_element_links(foreign_node), None);
        assert_eq!(store.checker_link_allocated_lengths(), before);
    }

    #[test]
    fn checker_owned_entity_names_validate_exact_closure_and_preserve_identity() {
        let mut store = TestStore::new();
        let parsed = parse_isolated_entity_name("Namespace.Nested.factory").unwrap();
        let entity = store.register_parsed_entity_name(&parsed).unwrap();
        assert_eq!(store.entity_name_len(), 5);
        let EntityNameNode::QualifiedName { left, right } = store.entity_name(entity).unwrap()
        else {
            panic!("three-part entity name must end in a qualified node")
        };
        assert_eq!(
            store.entity_name(*right),
            Some(&EntityNameNode::Identifier {
                text: "factory".into(),
            })
        );
        let EntityNameNode::QualifiedName {
            left: first,
            right: nested,
        } = store.entity_name(*left).unwrap()
        else {
            panic!("nested left child must remain qualified")
        };
        assert_eq!(
            store.entity_name(*first),
            Some(&EntityNameNode::Identifier {
                text: "Namespace".into(),
            })
        );
        assert_eq!(
            store.entity_name(*nested),
            Some(&EntityNameNode::Identifier {
                text: "Nested".into(),
            })
        );

        let duplicate = store
            .register_entity_name_text("Namespace.Nested.factory")
            .unwrap();
        assert_ne!(duplicate, entity, "separate parses retain distinct roots");
        assert_eq!(store.entity_name_len(), 10);

        let before = store.entity_name_len();
        for invalid in [
            "",
            "Namespace.",
            "Namespace..factory",
            "Namespace factory",
            "Namespace.factory()",
            "#private",
            "Namespace.\\u{notHex}",
        ] {
            assert_eq!(store.register_entity_name_text(invalid), None);
            assert_eq!(store.entity_name_len(), before);
        }

        let source = parse_source_file("type Value = Namespace.Member;");
        let qualified = source
            .arena
            .iter()
            .find_map(|(id, node)| (node.kind == SyntaxKind::QualifiedName).then_some(id))
            .unwrap();
        assert_eq!(store.register_entity_name(&source.arena, qualified), None);
        assert_eq!(store.entity_name_len(), before);

        let mut malformed = NodeArena::new();
        let root = NodeId::new(2);
        let left = malformed.alloc(Node {
            kind: SyntaxKind::Identifier,
            flags: NodeFlags::JAVASCRIPT_FILE,
            range: TextRange::default(),
            parent: Some(root),
            data: NodeData::Identifier(Box::new(IdentifierData {
                flow_node: None,
                text: "Namespace".into(),
            })),
        });
        let mut invalid_right = source.arena.get(source.source_file).unwrap().clone();
        invalid_right.flags = NodeFlags::JAVASCRIPT_FILE;
        invalid_right.parent = Some(root);
        let right = malformed.alloc(invalid_right);
        assert_eq!(right, NodeId::new(1));
        let malformed_root = malformed.alloc(Node {
            kind: SyntaxKind::QualifiedName,
            flags: NodeFlags::JAVASCRIPT_FILE,
            range: TextRange::default(),
            parent: None,
            data: NodeData::QualifiedName(Box::new(QualifiedNameData {
                flow_node: None,
                left,
                right,
                facts: 0,
            })),
        });
        assert_eq!(malformed_root, root);
        assert_eq!(store.register_entity_name(&malformed, malformed_root), None);
        assert_eq!(store.entity_name_len(), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Every ID-bearing slot gets an independent foreign probe.
    fn final_sparse_link_stores_preserve_state_and_reject_every_foreign_id_atomically() {
        let local_parse = parse_source_file("enum E { A } type Value = Namespace.Member;");
        let other_parse = parse_source_file("type Other = OtherNamespace.Member;");
        let foreign_parse = parse_source_file("enum E { A } type Value = Namespace.Member;");
        let local_file = FileId::new(41);
        let other_file = FileId::new(42);

        let mut store = TestStore::new();
        let local_source = store
            .register_source_file(&local_parse.arena, local_parse.source_file, local_file)
            .unwrap();
        let other_source = store
            .register_source_file(&other_parse.arena, other_parse.source_file, other_file)
            .unwrap();
        let local_node = node_ref_of_kind(&local_parse.arena, local_file, SyntaxKind::EnumMember);
        let local_factory = store
            .register_entity_name_text("Namespace.factory")
            .unwrap();
        let local_fragment_factory = store
            .register_entity_name_text("Namespace.Fragment")
            .unwrap();
        assert_ne!(local_factory, local_fragment_factory);
        let other_identifier = other_parse
            .arena
            .iter()
            .find_map(|(id, node)| (node.kind == SyntaxKind::Identifier).then_some(id))
            .unwrap();
        let other_node = NodeRef::new(other_parse.arena.id(), other_file, other_identifier);
        let local_symbol = alloc_test_symbol(&mut store, "local");
        let local_container = alloc_test_symbol(&mut store, "container");
        let local_type = store.alloc_type("local type");

        let mut foreign = TestStore::new();
        let foreign_source = foreign
            .register_source_file(&foreign_parse.arena, foreign_parse.source_file, local_file)
            .unwrap();
        let foreign_node =
            node_ref_of_kind(&foreign_parse.arena, local_file, SyntaxKind::EnumMember);
        let foreign_factory = foreign
            .register_entity_name_text("Namespace.factory")
            .unwrap();
        let foreign_fragment_factory = foreign
            .register_entity_name_text("Namespace.Fragment")
            .unwrap();
        let foreign_symbol = alloc_test_symbol(&mut foreign, "foreign");
        let foreign_type = foreign.alloc_type("foreign type");

        assert_eq!(local_symbol.get(), foreign_symbol.get());
        assert_eq!(local_type.get(), foreign_type.get());
        assert_eq!(local_node.file, foreign_node.file);
        assert_eq!(local_node.node, foreign_node.node);
        assert_ne!(local_node.arena, foreign_node.arena);
        assert!(store.entity_name(local_factory).is_some());
        assert!(foreign.entity_name(foreign_factory).is_some());
        assert_eq!(store.entity_name(foreign_factory), None);

        let enum_links = EnumMemberLinks {
            value: EvaluatorResult {
                value: Some(EvaluatorValue::Number(Number::new(7.0))),
                is_syntactically_string: false,
                resolved_other_files: true,
                has_external_references: true,
            },
        };
        assert!(store.set_enum_member_links(local_node, enum_links.clone()));
        let counts_after_enum = store.checker_link_allocated_lengths();
        assert!(!store.set_enum_member_links(foreign_node, EnumMemberLinks::default()));
        assert_eq!(store.enum_member_links(local_node), Some(&enum_links));
        assert_eq!(store.checker_link_allocated_lengths(), counts_after_enum);

        let accessible_key = AccessibleChainCacheKey {
            use_only_external_aliasing: true,
            location: Some(local_node),
            meaning: SymbolFlags::VALUE,
        };
        let containing_links = ContainingSymbolLinks {
            extended_containers_by_file: Some(HashMap::from([(
                local_source,
                OptionalSymbolSequence::Allocated(vec![local_container, local_symbol]),
            )])),
            extended_containers: ExtendedContainersState::Computed(OptionalSymbolSequence::Nil),
            accessible_chain_cache: Some(HashMap::from([(
                accessible_key,
                OptionalSymbolSequence::Nil,
            )])),
        };
        assert!(store.set_containing_symbol_links(local_symbol, containing_links.clone()));
        assert_eq!(
            store
                .containing_symbol_links(local_symbol)
                .unwrap()
                .accessible_chain_cache
                .as_ref()
                .unwrap()
                .get(&accessible_key),
            Some(&OptionalSymbolSequence::Nil),
            "a present nil sequence is the cached accessible-chain miss"
        );
        let containing_counts = store.checker_link_allocated_lengths();
        assert!(!store.set_containing_symbol_links(foreign_symbol, containing_links.clone()));

        let mut invalid = containing_links.clone();
        invalid.extended_containers_by_file = Some(HashMap::from([(
            foreign_source,
            OptionalSymbolSequence::Allocated(vec![local_symbol]),
        )]));
        assert!(!store.set_containing_symbol_links(local_symbol, invalid));

        let mut invalid = containing_links.clone();
        invalid.extended_containers_by_file = Some(HashMap::from([(
            local_source,
            OptionalSymbolSequence::Allocated(vec![foreign_symbol]),
        )]));
        assert!(!store.set_containing_symbol_links(local_symbol, invalid));

        let mut invalid = containing_links.clone();
        invalid.extended_containers =
            ExtendedContainersState::Computed(OptionalSymbolSequence::Allocated(vec![
                foreign_symbol,
            ]));
        assert!(!store.set_containing_symbol_links(local_symbol, invalid));

        let mut invalid = containing_links.clone();
        invalid.accessible_chain_cache = Some(HashMap::from([(
            AccessibleChainCacheKey {
                location: Some(foreign_node),
                ..accessible_key
            },
            OptionalSymbolSequence::Nil,
        )]));
        assert!(!store.set_containing_symbol_links(local_symbol, invalid));

        let mut invalid = containing_links.clone();
        invalid.accessible_chain_cache = Some(HashMap::from([(
            accessible_key,
            OptionalSymbolSequence::Allocated(vec![foreign_symbol]),
        )]));
        assert!(!store.set_containing_symbol_links(local_symbol, invalid));
        assert_eq!(
            store.containing_symbol_links(local_symbol),
            Some(&containing_links)
        );
        assert_eq!(store.checker_link_allocated_lengths(), containing_counts);

        let mut deferred_nodes = OrderedNodeSet::allocated();
        assert!(deferred_nodes.insert(local_source.node_ref()));
        assert!(deferred_nodes.insert(local_node));
        let source_links = SourceFileLinks {
            type_checked: true,
            unused_checked: true,
            external_helpers_module: Some(local_symbol),
            requested_external_emit_helpers: ExternalEmitHelpers::REST
                | ExternalEmitHelpers::IMPORT_STAR,
            deferred_nodes,
            identifier_check_nodes: Some(vec![local_source.node_ref(), local_node]),
            local_jsx_namespace: "Namespace".into(),
            local_jsx_fragment_namespace: "Fragment".into(),
            local_jsx_factory: Some(local_factory),
            local_jsx_fragment_factory: Some(local_fragment_factory),
            jsx_fragment_type: Some(local_type),
        };
        assert!(store.set_source_file_links(local_source, source_links.clone()));
        assert_eq!(store.source_file_links(local_source), Some(&source_links));
        let source_counts = store.checker_link_allocated_lengths();
        assert!(!store.set_source_file_links(foreign_source, source_links.clone()));

        let mut invalid = source_links.clone();
        invalid.external_helpers_module = Some(foreign_symbol);
        assert!(!store.set_source_file_links(local_source, invalid));

        let mut invalid = source_links.clone();
        invalid.deferred_nodes.insert(foreign_node);
        assert!(!store.set_source_file_links(local_source, invalid));

        let mut invalid = source_links.clone();
        invalid.identifier_check_nodes = Some(vec![foreign_node]);
        assert!(!store.set_source_file_links(local_source, invalid));

        let mut invalid = source_links.clone();
        invalid.local_jsx_factory = Some(foreign_factory);
        assert!(!store.set_source_file_links(local_source, invalid));

        let mut invalid = source_links.clone();
        invalid.local_jsx_fragment_factory = Some(foreign_fragment_factory);
        assert!(!store.set_source_file_links(local_source, invalid));

        let mut invalid = source_links.clone();
        invalid.jsx_fragment_type = Some(foreign_type);
        assert!(!store.set_source_file_links(local_source, invalid));

        let mut invalid = source_links.clone();
        invalid.deferred_nodes.insert(other_node);
        assert!(!store.set_source_file_links(local_source, invalid));

        let mut invalid = source_links.clone();
        invalid.identifier_check_nodes = Some(vec![other_node]);
        assert!(!store.set_source_file_links(local_source, invalid));

        assert_eq!(store.source_file_links(local_source), Some(&source_links));
        assert_eq!(store.source_file_links(other_source), None);
        assert_eq!(store.checker_link_allocated_lengths(), source_counts);
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
        let parsed = parse_source_file(
            "const asserted = value as string; const array = [...items]; \
             switch (value) { case 0: break; } factory();",
        );
        let file = FileId::new(21);
        let node = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let assertion_node = node_ref_of_kind(&parsed.arena, file, SyntaxKind::AsExpression);
        let array_node = node_ref_of_kind(&parsed.arena, file, SyntaxKind::ArrayLiteralExpression);
        let switch_node = node_ref_of_kind(&parsed.arena, file, SyntaxKind::SwitchStatement);
        let signature_node = node_ref_of_kind(&parsed.arena, file, SyntaxKind::CallExpression);
        let mut store = TestStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let symbol = alloc_test_symbol(&mut store, "T");

        assert_eq!(store.node_links(node), None);
        assert_eq!(store.symbol_node_links(node), None);
        assert_eq!(store.type_node_links(node), None);
        assert_eq!(store.assertion_links(assertion_node), None);
        assert_eq!(store.array_literal_links(array_node), None);
        assert_eq!(store.switch_statement_links(switch_node), None);
        assert_eq!(store.jsx_element_links(node), None);
        assert_eq!(store.signature_links(signature_node), None);
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
        assert!(store.ensure_assertion_links(assertion_node));
        assert!(store.ensure_array_literal_links(array_node));
        assert!(store.ensure_switch_statement_links(switch_node));
        assert!(store.ensure_jsx_element_links(node));
        assert!(store.ensure_signature_links(signature_node));
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
            store.assertion_links(assertion_node),
            Some(&AssertionLinks::default())
        );
        assert_eq!(
            store.array_literal_links(array_node),
            Some(&ArrayLiteralLinks::default())
        );
        assert_eq!(
            store.switch_statement_links(switch_node),
            Some(&SwitchStatementLinks::default())
        );
        assert_eq!(
            store.jsx_element_links(node),
            Some(&JsxElementLinks::default())
        );
        assert_eq!(
            store.signature_links(signature_node),
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
    fn undefined_flag_bits_are_rejected_without_replacing_sparse_records() {
        let parsed = parse_source_file("const value = 1;");
        let file = FileId::new(36);
        let mut store = TestStore::new();
        let source = store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let node = source.node_ref();

        let node_links = NodeLinks {
            flags: NodeCheckFlags::TYPE_CHECKED,
            ..NodeLinks::default()
        };
        assert!(store.set_node_links(node, node_links.clone()));
        let node_counts = store.checker_link_allocated_lengths();
        let invalid_node_links = NodeLinks {
            flags: NodeCheckFlags::from_bits_retain(NodeCheckFlags::TYPE_CHECKED.bits() | (1 << 2)),
            ..NodeLinks::default()
        };
        assert!(!store.set_node_links(node, invalid_node_links));
        assert_eq!(store.node_links(node), Some(&node_links));
        assert_eq!(store.checker_link_allocated_lengths(), node_counts);

        let source_links = SourceFileLinks {
            requested_external_emit_helpers: ExternalEmitHelpers::REST,
            ..SourceFileLinks::default()
        };
        assert!(store.set_source_file_links(source, source_links.clone()));
        let source_counts = store.checker_link_allocated_lengths();
        let invalid_source_links = SourceFileLinks {
            requested_external_emit_helpers: ExternalEmitHelpers::from_bits_retain(
                ExternalEmitHelpers::REST.bits() | (1 << 31),
            ),
            ..SourceFileLinks::default()
        };
        assert!(!store.set_source_file_links(source, invalid_source_links));
        assert_eq!(store.source_file_links(source), Some(&source_links));
        assert_eq!(store.checker_link_allocated_lengths(), source_counts);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Exercises every field in the dependency-closed link slice.
    fn semantic_link_commits_accept_owned_ids_and_exact_field_states() {
        let parsed = parse_source_file(
            "const asserted = value as string; const array = [...items]; \
             switch (value) { case 0: break; } factory();",
        );
        let file = FileId::new(22);
        let node = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let signature_node = node_ref_of_kind(&parsed.arena, file, SyntaxKind::CallExpression);
        let assertion_node = node_ref_of_kind(&parsed.arena, file, SyntaxKind::AsExpression);
        let array_node = node_ref_of_kind(&parsed.arena, file, SyntaxKind::ArrayLiteralExpression);
        let switch_node = node_ref_of_kind(&parsed.arena, file, SyntaxKind::SwitchStatement);
        let mut store = TestStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
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
        assert!(store.set_signature_links(signature_node, signature_links.clone()));
        assert_eq!(
            store.signature_links(signature_node),
            Some(&signature_links)
        );
        let completed_signature_links = SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            effects_signature: EffectsSignatureState::Resolved(signature),
            decorator_signature: DecoratorSignatureState::NotApplicable,
        };
        assert!(store.set_signature_links(signature_node, completed_signature_links.clone()));
        assert_eq!(
            store.signature_links(signature_node),
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
        assert!(store.set_assertion_links(assertion_node, assertion.clone()));
        assert_eq!(store.assertion_links(assertion_node), Some(&assertion));

        let array_literal = ArrayLiteralLinks {
            indices_computed: true,
            first_spread_index: -1,
            last_spread_index: -1,
        };
        assert!(store.set_array_literal_links(array_node, array_literal.clone()));
        assert_eq!(store.array_literal_links(array_node), Some(&array_literal));

        let switch_statement = SwitchStatementLinks {
            exhaustive_state: ExhaustiveState::True,
            switch_types_computed: true,
            witnesses_computed: true,
            switch_types: Some(vec![type_id]),
            witnesses: Some(Vec::new()),
        };
        assert!(store.set_switch_statement_links(switch_node, switch_statement.clone()));
        assert_eq!(
            store.switch_statement_links(switch_node),
            Some(&switch_statement)
        );

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
        let source = "const asserted = value as string; const array = [...items]; \
                      switch (value) { case 0: break; } factory();";
        let first_parse = parse_source_file(source);
        let second_parse = parse_source_file(source);
        let file = FileId::new(23);
        let first_node = NodeRef::new(first_parse.arena.id(), file, first_parse.source_file);
        let first_assertion = node_ref_of_kind(&first_parse.arena, file, SyntaxKind::AsExpression);
        let first_array =
            node_ref_of_kind(&first_parse.arena, file, SyntaxKind::ArrayLiteralExpression);
        let first_switch = node_ref_of_kind(&first_parse.arena, file, SyntaxKind::SwitchStatement);
        let first_signature =
            node_ref_of_kind(&first_parse.arena, file, SyntaxKind::CallExpression);
        let second_node = NodeRef::new(second_parse.arena.id(), file, second_parse.source_file);
        let second_assertion =
            node_ref_of_kind(&second_parse.arena, file, SyntaxKind::AsExpression);
        let second_array = node_ref_of_kind(
            &second_parse.arena,
            file,
            SyntaxKind::ArrayLiteralExpression,
        );
        let second_switch =
            node_ref_of_kind(&second_parse.arena, file, SyntaxKind::SwitchStatement);
        let second_signature =
            node_ref_of_kind(&second_parse.arena, file, SyntaxKind::CallExpression);

        let mut first = TestStore::new();
        assert!(
            first
                .register_source_file(&first_parse.arena, first_parse.source_file, file)
                .is_some()
        );
        let foreign_symbol = alloc_test_symbol(&mut first, "foreign");
        let foreign_type = first.alloc_type("foreign type");
        let foreign_mapper = first.alloc_mapper("foreign mapper");
        let foreign_signature = empty_signature(&mut first);
        let foreign_table = first.alloc_symbol_table();

        let mut store = TestStore::new();
        assert!(
            store
                .register_source_file(&second_parse.arena, second_parse.source_file, file)
                .is_some()
        );
        let symbol = alloc_test_symbol(&mut store, "local");
        let local_type = store.alloc_type("local type");
        let local_table = store.alloc_symbol_table();

        assert!(!store.ensure_node_links(first_node));
        assert!(!store.ensure_symbol_node_links(first_node));
        assert!(!store.ensure_type_node_links(first_node));
        assert!(!store.ensure_assertion_links(first_assertion));
        assert!(!store.ensure_array_literal_links(first_array));
        assert!(!store.ensure_switch_statement_links(first_switch));
        assert!(!store.ensure_jsx_element_links(first_node));
        assert!(!store.ensure_signature_links(first_signature));
        assert_eq!(store.node_links(second_node), None);
        assert_eq!(store.symbol_node_links(second_node), None);
        assert_eq!(store.type_node_links(second_node), None);
        assert_eq!(store.assertion_links(second_assertion), None);
        assert_eq!(store.array_literal_links(second_array), None);
        assert_eq!(store.switch_statement_links(second_switch), None);
        assert_eq!(store.jsx_element_links(second_node), None);
        assert_eq!(store.signature_links(second_signature), None);

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
            assert!(!store.set_signature_links(second_signature, invalid));
            assert_eq!(store.signature_links(second_signature), None);
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
            second_assertion,
            AssertionLinks {
                expr_type: Some(foreign_type),
            },
        ));
        assert_eq!(store.assertion_links(second_assertion), None);

        assert!(!store.set_switch_statement_links(
            second_switch,
            SwitchStatementLinks {
                switch_types: Some(vec![foreign_type]),
                ..SwitchStatementLinks::default()
            },
        ));
        assert_eq!(store.switch_statement_links(second_switch), None);

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
