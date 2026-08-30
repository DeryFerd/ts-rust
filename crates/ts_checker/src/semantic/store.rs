//! Aggregate ownership and provenance validation for canonical semantic data.

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    num::NonZeroU32,
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering},
    },
};

use ts_ast::{FileId, NodeArena, NodeArenaId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    AstScope, CanonicalSourceFileFacts, CheckFlags, EscapedName, EscapedNameRef,
    InternalSymbolName, SemanticStoreId, SemanticSymbolId, SymbolData, SymbolFlags, SymbolStore,
    SymbolTableId,
    semantic::{PreparedSymbolTable, Symbol, SymbolTable},
};
use ts_core::TextRange;
use ts_parser::{IsolatedEntityName, parse_isolated_entity_name};

use super::{
    alias_provider::SourceFileNamespaceWrapper,
    array_types::CanonicalArrayTargets,
    bootstrap::{CanonicalUnionCreationProof, IntrinsicBootstrap},
    classes::{ClassInstanceSuperMember, ClassInstanceSuperView, SourceClassProvenance},
    conditional_types::{
        ConditionalQueryKey, ConditionalQueryProduction, ConditionalTypeProduction,
    },
    declared_values::DeclaredValueProvenance,
    derived_types::DerivedTypeCaches,
    global_types::ResolvedGlobalType,
    ids::{
        ConditionalRootId, IndexInfoId, SignatureId, TypeAliasId, TypeId, TypeMapperId,
        TypePredicateId, TypedArena,
    },
    instantiate::{InlinePropertyObjectRecovery, PropertyObjectAliasRecovery},
    instantiated_members::{
        InstantiatedIndexRecovery, InstantiatedPropertyAliasCallable, InstantiatedPropertyRecovery,
        PublishedInterfaceMethodOrigin, PublishedInterfaceMethodRecovery,
    },
    intersection_types::IntersectionTypeCacheKey,
    jsdoc::{SourceJsDocCallbackIdentity, SourceJsDocTypedefIdentity},
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
    mapped_types::{MappedIndexRecovery, MappedPropertyRecovery, MappedTypeModifiers},
    object_members::{
        ObjectLiteralGetterOrigin, ObjectLiteralGetterReturnProof, ObjectLiteralPropertyCloneOrigin,
    },
    relation::{RelationCaches, RelationComparisonResult, RelationKind, RelationStateSnapshot},
    signatures::{
        CompositeSignature, ElementFlags, IndexFlags, IndexInfo, IndexInfoArena, Signature,
        SignatureArena, SignatureFlags, TupleElementInfo, TupleMetadata, TypePredicate,
        TypePredicateArena, TypePredicateKind,
    },
    source_callables::{
        SourceCallableAliasAnnotation, SourceCallableAliasSnapshot,
        SourceCallableTypeParameterSyntaxProof, source_generic_index_map_syntax,
        source_type_parameter_default_is_assignable, valid_source_generic_index_map,
    },
    source_flow::SourceCapturedLocal,
    source_imports::SourceFileNamespaceIdentity,
    source_meta::ImportMetaExpressionIdentity,
    source_namespaces::ModuleValueIdentity,
    type_nodes::{
        ConstructorAnnotationProof, OrdinaryIntersectionAliasRequestRecovery,
        PropertyObjectAliasRequestRecovery, SourceCallableAliasResolution,
        SourceCallableInterfaceReturnProof, SourceCallableTypeQueryEvidence,
        UnionAliasInstantiationProof,
    },
    type_records::{
        CacheHashKey, ConditionalRoot, ConstrainedTypeData, LiteralValue, TypeAlias,
        TypeCacheState, TypeData, TypeRecord, type_list_key,
    },
    types::{ObjectFlags, TypeFlags},
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceNodeFacts {
    kind: SyntaxKind,
    ordinary_arrow_type_parameters: bool,
    parent: Option<NodeId>,
    start: u32,
    identifier_text: Option<Box<str>>,
    default_function_name: Option<NodeId>,
    prefix_unary_operator: Option<SyntaxKind>,
    type_operator: Option<SyntaxKind>,
    alias_type_parameter: Option<Box<AliasTypeParameterSyntaxFacts>>,
    mapped_type: Option<Box<MappedTypeSyntaxFacts>>,
    plain_interface_heritage: Option<Box<PlainInterfaceHeritageFacts>>,
    exported: bool,
    signature_links_eligible: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AliasTypeParameterSyntaxFacts {
    constraint: Option<NodeId>,
    default_type: Option<NodeId>,
}

/// Actual annotation roles on a type parameter owned by a type alias.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceAliasTypeParameterAnnotations {
    pub constraint: Option<NodeRef>,
    pub default_type: Option<NodeRef>,
}

/// Exact heritage syntax retained without resolving base names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PlainInterfaceHeritageFacts {
    NoHeritage,
    Plain {
        clause: NodeId,
        bases: Box<[PlainInterfaceBaseFacts]>,
    },
    Unsupported,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlainInterfaceBaseFacts {
    pub expression: NodeId,
    pub name: NodeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MappedTypeSyntaxFacts {
    type_parameter: NodeId,
    constraint: Option<NodeId>,
    name_type: Option<NodeId>,
    template: Option<NodeId>,
    modifiers: Option<MappedTypeModifiers>,
}

/// Exact operand roles retained from one registered mapped declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceMappedTypeOperands {
    pub type_parameter: NodeRef,
    pub constraint: NodeRef,
    pub name_type: Option<NodeRef>,
    pub template: Option<NodeRef>,
}

#[derive(Debug)]
struct SourceSymbolDeclarations {
    flags: SymbolFlags,
    declarations: Box<[NodeRef]>,
    value_declaration: Option<NodeRef>,
}

#[derive(Clone, Debug)]
pub(super) struct SourceGlobalBinding {
    pub(super) table_symbol: SemanticSymbolId,
    pub(super) symbol: SemanticSymbolId,
    pub(super) flags: SymbolFlags,
    declarations: Option<Box<[NodeRef]>>,
}

impl SourceGlobalBinding {
    pub(super) fn declarations(&self) -> Option<&[NodeRef]> {
        self.declarations.as_deref()
    }
}

/// Global bindings retained after all initialization merges finish.
#[derive(Debug)]
pub(super) struct SourceGlobalBindings {
    pub(super) table: SymbolTableId,
    entries: HashMap<EscapedName, SourceGlobalBinding>,
}

impl SourceGlobalBindings {
    pub(super) fn get(&self, name: EscapedNameRef<'_>) -> Option<&SourceGlobalBinding> {
        self.entries.get(name.as_bytes())
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = &SourceGlobalBinding> {
        self.entries.values()
    }
}

#[derive(Debug)]
struct ComputedMethodNameGroup {
    owner: SemanticSymbolId,
    key_type: TypeId,
    key_symbol: SemanticSymbolId,
    sources: Box<[SemanticSymbolId]>,
}

pub(super) struct PreparedComputedMethodNameGroup {
    owner: SemanticSymbolId,
    key_type: TypeId,
    sources: Box<[SemanticSymbolId]>,
    declarations: Vec<NodeRef>,
    keys: Box<[super::object_members::PlannedComputedMemberKey]>,
    flags: SymbolFlags,
    name: EscapedName,
    existing: Option<SemanticSymbolId>,
}

#[derive(Debug)]
struct CachedSignatureEntry {
    type_arguments: Box<[TypeId]>,
    instantiated: SignatureId,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct UnresolvedSymbolKey {
    parent: Option<SemanticSymbolId>,
    name: EscapedName,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum UnresolvedTypeError {
    MissingBootstrap,
    InvalidName,
    InvalidSymbol(SemanticSymbolId),
    Capacity,
}

#[derive(Debug, Default)]
struct RelationReadObservations {
    types: HashSet<TypeId>,
    type_aliases: HashSet<TypeAliasId>,
    signatures: HashSet<SignatureId>,
    symbols: HashSet<SemanticSymbolId>,
    symbol_tables: HashSet<SymbolTableId>,
    object_instantiation_maps: HashSet<TypeId>,
    object_instantiations: HashSet<(TypeId, CacheHashKey)>,
    nodes: HashSet<NodeRef>,
    derived_cache_sources: HashSet<TypeId>,
    derived_cache_targets: HashSet<TypeId>,
    enum_pairs: HashSet<(SemanticSymbolId, SemanticSymbolId)>,
}

#[derive(Debug)]
struct ActiveRelationReadObservations {
    token: RelationObservationToken,
    observations: RelationReadObservations,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct RelationObservationToken(u64);

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

/// Exact key for pinned checker `propertiesTypes`.
///
/// `include` and `include_origin` distinguish the internal
/// `getLiteralTypeFromProperties` modes. `unresolved_members` is retained even
/// when the first installed `keyof` slice accepts only fully resolved objects,
/// because upstream deliberately prevents a WIP member surface from aliasing
/// its final cache entry.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct PropertiesTypeCacheKey {
    type_id: TypeId,
    include: TypeFlags,
    include_origin: bool,
    unresolved_members: bool,
}

impl PropertiesTypeCacheKey {
    pub(super) const fn new(
        type_id: TypeId,
        include: TypeFlags,
        include_origin: bool,
        unresolved_members: bool,
    ) -> Self {
        Self {
            type_id,
            include,
            include_origin,
            unresolved_members,
        }
    }
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

/// Source links retained when a real inferred-return cycle recovers to `any`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableInferredReturnCycle {
    pub(super) callable: TypeId,
    pub(super) declaration: NodeRef,
    pub(super) body: NodeRef,
    pub(super) body_type: TypeId,
    pub(super) query: NodeRef,
    pub(super) query_name: NodeRef,
    pub(super) variable: SemanticSymbolId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SignatureReturnProvenance {
    Annotation(TypeId),
    RecoveredInferred(SourceCallableInferredReturnCycle),
    InvalidatedRecovery(SourceCallableInferredReturnCycle),
}

impl SourceCallableFamily {
    pub(super) const fn syntax_kind(self) -> SyntaxKind {
        match self {
            Self::FunctionDeclaration => SyntaxKind::FunctionDeclaration,
            Self::ArrowFunction => SyntaxKind::ArrowFunction,
        }
    }

    /// Anonymous function expressions share the existing anonymous callable brand.
    pub(super) const fn matches_syntax_kind(self, kind: SyntaxKind) -> bool {
        matches!(
            (self, kind),
            (Self::FunctionDeclaration, SyntaxKind::FunctionDeclaration)
                | (
                    Self::ArrowFunction,
                    SyntaxKind::ArrowFunction | SyntaxKind::FunctionExpression
                )
        )
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
    /// Flags authenticated by source planning before publication.
    pub(super) flags: SignatureFlags,
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
    /// Object-property arrows use their exact binder-owned property as the
    /// contextual anchor instead of a variable symbol.
    pub(super) contextual_target: Option<TypeId>,
    pub(super) contextual_variable: Option<SemanticSymbolId>,
    /// Opaque captured-let authority from the source callable's exact plan.
    pub(super) captured_assignment: Option<SourceCapturedLocal>,
}

/// Exact annotation and value edges for one source-overload parameter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceOverloadParameterProvenance {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) annotation: NodeRef,
    pub(super) annotation_null_literal_identity: bool,
    pub(super) base_type: TypeId,
    pub(super) call_type: TypeId,
    pub(super) optional: bool,
}

/// One declaration-order signature row owned by a source overload group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceOverloadSignatureProvenance {
    pub(super) declaration: NodeRef,
    pub(super) signature: SignatureId,
    pub(super) flags: SignatureFlags,
    pub(super) parameters: Box<[SourceOverloadParameterProvenance]>,
    pub(super) return_annotation: NodeRef,
    pub(super) return_annotation_null_literal_identity: bool,
    pub(super) return_type: TypeId,
}

/// Immutable source/binder provenance for one local ambient overload value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceOverloadProvenance {
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) signatures: Box<[SourceOverloadSignatureProvenance]>,
    pub(super) array_targets: Option<CanonicalArrayTargets>,
}

/// Fully resolved parameter row staged before overload publication.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PreparedSourceOverloadParameter {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) annotation: NodeRef,
    pub(super) annotation_null_literal_identity: bool,
    pub(super) base_type: TypeId,
    pub(super) call_type: TypeId,
    pub(super) optional: bool,
}

/// Fully resolved signature row staged before overload publication.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PreparedSourceOverloadSignature {
    pub(super) declaration: NodeRef,
    pub(super) parameters: Vec<PreparedSourceOverloadParameter>,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) return_annotation: NodeRef,
    pub(super) return_annotation_null_literal_identity: bool,
    pub(super) return_type: TypeId,
}

/// Dependency-closed transaction input for one source overload group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PreparedSourceOverloadPublication {
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) signatures: Vec<PreparedSourceOverloadSignature>,
    pub(super) array_targets: Option<CanonicalArrayTargets>,
}

/// Immutable syntax-plan edges for the admitted direct-interface heritage slice.
///
/// `resolved_base_types` remains the pinned semantic cache, while this separate
/// provenance retains every base contribution in source order, including repeats.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectInterfaceHeritageProvenance {
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) bases: Vec<(SemanticSymbolId, TypeId)>,
}

/// Immutable source-plan edge for one direct local class base.
///
/// Classes retain two distinct base identities: the constructor value cached
/// on the derived instance and the declared instance cached in
/// `resolved_base_types`. Keeping both edges separate prevents a coherent but
/// source-wrong class graph from reaching relation through a poisoned cache.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DirectClassHeritageProvenance {
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) owner_value_type: TypeId,
    pub(super) base_symbol: SemanticSymbolId,
    pub(super) base_instance_type: TypeId,
    pub(super) base_value_type: TypeId,
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
    /// The effective direct constraint, or the canonical `no_constraint_type`.
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
    pub(super) query_evidence: Option<Arc<SourceCallableTypeQueryEvidence>>,
    pub(super) parameters: Vec<SemanticSymbolId>,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) return_annotation: Option<NodeRef>,
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
    conditional_type_productions: HashMap<TypeId, ConditionalTypeProduction>,
    conditional_query_productions: HashMap<ConditionalQueryKey, ConditionalQueryProduction>,
    entity_names: Vec<EntityNameNode>,
    source_files: BTreeMap<FileId, SourceFileRef>,
    source_file_facts: BTreeMap<FileId, CanonicalSourceFileFacts>,
    source_file_ranks: BTreeMap<FileId, usize>,
    source_files_by_arena: BTreeMap<NodeArenaId, SourceFileRef>,
    source_node_facts: BTreeMap<NodeArenaId, Vec<Option<SourceNodeFacts>>>,
    source_node_children: BTreeMap<NodeArenaId, Vec<Box<[NodeId]>>>,
    source_symbol_declarations: HashMap<SemanticSymbolId, SourceSymbolDeclarations>,
    source_global_bindings: Option<SourceGlobalBindings>,
    computed_method_name_groups: HashMap<SemanticSymbolId, ComputedMethodNameGroup>,
    source_declaration_owners: HashMap<NodeRef, Vec<SemanticSymbolId>>,
    type_alias_declared_type_owners: HashMap<TypeId, HashSet<SemanticSymbolId>>,
    merged_symbols: HashMap<SemanticSymbolId, SemanticSymbolId>,
    links: CheckerLinkStores,
    declared_types_in_progress: HashSet<SemanticSymbolId>,
    function_type_provenance: HashSet<TypeId>,
    declared_call_set_provenance: HashSet<TypeId>,
    declared_call_set_types_by_signature: HashMap<SignatureId, TypeId>,
    direct_interface_heritage_provenance: HashMap<TypeId, DirectInterfaceHeritageProvenance>,
    direct_class_heritage_provenance: HashMap<TypeId, DirectClassHeritageProvenance>,
    constructor_annotation_bindings: HashMap<NodeRef, SemanticSymbolId>,
    declared_value_provenance: HashMap<SemanticSymbolId, DeclaredValueProvenance>,
    instantiated_property_alias_callables: HashMap<TypeId, InstantiatedPropertyAliasCallable>,
    published_interface_method_origins: HashMap<TypeId, PublishedInterfaceMethodOrigin>,
    published_interface_method_signature_owners: HashMap<SignatureId, TypeId>,
    published_interface_method_recoveries: HashMap<TypeId, PublishedInterfaceMethodRecovery>,
    instantiated_property_alias_callable_types_by_signature: HashMap<SignatureId, TypeId>,
    instantiated_property_recoveries: HashMap<SemanticSymbolId, InstantiatedPropertyRecovery>,
    instantiated_index_recoveries: HashMap<IndexInfoId, InstantiatedIndexRecovery>,
    property_object_alias_recoveries: HashMap<TypeId, PropertyObjectAliasRecovery>,
    inline_property_object_recoveries: HashMap<TypeId, InlinePropertyObjectRecovery>,
    property_object_alias_request_recoveries:
        HashMap<(SemanticSymbolId, CacheHashKey), PropertyObjectAliasRequestRecovery>,
    ordinary_intersection_alias_request_recoveries:
        HashMap<(SemanticSymbolId, CacheHashKey), OrdinaryIntersectionAliasRequestRecovery>,
    mapped_property_recoveries: HashMap<SemanticSymbolId, MappedPropertyRecovery>,
    mapped_index_recoveries: HashMap<IndexInfoId, MappedIndexRecovery>,
    source_class_provenance: HashMap<TypeId, SourceClassProvenance>,
    source_classes_by_symbol: HashMap<SemanticSymbolId, TypeId>,
    class_instance_super_views: HashMap<TypeId, ClassInstanceSuperView>,
    class_instance_super_views_by_instance: HashMap<TypeId, TypeId>,
    class_instance_super_members: HashMap<(TypeId, SemanticSymbolId), ClassInstanceSuperMember>,
    source_callable_provenance: HashMap<TypeId, SourceCallableProvenance>,
    source_callable_interface_return_proofs:
        HashMap<SignatureId, SourceCallableInterfaceReturnProof>,
    source_callable_alias_annotations: HashMap<
        NodeRef,
        (
            SourceCallableAliasAnnotation,
            Option<SourceCallableAliasResolution>,
        ),
    >,
    source_callable_alias_owners: HashMap<SemanticSymbolId, NodeRef>,
    source_jsdoc_typedefs: HashMap<TypeId, SourceJsDocTypedefIdentity>,
    source_jsdoc_callbacks: HashMap<TypeId, SourceJsDocCallbackIdentity>,
    source_callable_types_by_declaration: HashMap<NodeRef, TypeId>,
    source_callable_types_by_owner: HashMap<SemanticSymbolId, TypeId>,
    source_callable_types_by_signature: HashMap<SignatureId, TypeId>,
    source_callable_type_parameters:
        HashMap<SignatureId, Box<[SourceCallableTypeParameterProvenance]>>,
    source_callable_type_queries: HashMap<SignatureId, Arc<SourceCallableTypeQueryEvidence>>,
    module_value_identities: HashMap<SemanticSymbolId, ModuleValueIdentity>,
    object_literal_property_clone_origins:
        HashMap<SemanticSymbolId, ObjectLiteralPropertyCloneOrigin>,
    object_literal_getter_origins: HashMap<SemanticSymbolId, ObjectLiteralGetterOrigin>,
    object_literal_getter_return_proofs: HashMap<SemanticSymbolId, ObjectLiteralGetterReturnProof>,
    source_file_namespace_identities: HashMap<SemanticSymbolId, SourceFileNamespaceIdentity>,
    source_file_namespace_wrappers: HashMap<SemanticSymbolId, SourceFileNamespaceWrapper>,
    source_file_namespace_wrapper_aliases: HashMap<SemanticSymbolId, SemanticSymbolId>,
    source_file_namespace_wrapper_defaults: HashMap<SemanticSymbolId, SemanticSymbolId>,
    source_overload_provenance: HashMap<TypeId, SourceOverloadProvenance>,
    source_overload_types_by_declaration: HashMap<NodeRef, TypeId>,
    source_overload_types_by_owner: HashMap<SemanticSymbolId, TypeId>,
    source_overload_types_by_signature: HashMap<SignatureId, TypeId>,
    /// Pinned checker `cachedSignatures`, keyed by generic target and the
    /// ordered type-argument hash.
    cached_signatures: HashMap<(SignatureId, CacheHashKey), CachedSignatureEntry>,
    unresolved_symbols: HashMap<UnresolvedSymbolKey, SemanticSymbolId>,
    unresolved_symbol_keys: HashMap<SemanticSymbolId, UnresolvedSymbolKey>,
    /// Pinned checker `propertiesTypes`, including its WIP unresolved-members
    /// discriminator and origin-preservation mode.
    properties_types: HashMap<PropertiesTypeCacheKey, TypeId>,
    function_signature_return_annotations: HashMap<SignatureId, (NodeRef, bool)>,
    callable_signature_parameter_types: HashMap<SignatureId, Vec<TypeId>>,
    checked_source_callable_returns: HashMap<SignatureId, TypeId>,
    signature_return_provenance: HashMap<SignatureId, SignatureReturnProvenance>,
    canonical_tuple_targets: HashMap<CanonicalTupleTargetKey, CanonicalTupleTargetProvenance>,
    canonical_empty_tuple: Option<CanonicalEmptyTupleProvenance>,
    pub(super) intersection_types: HashMap<IntersectionTypeCacheKey, TypeId>,
    pub(super) intersection_keys_by_type: HashMap<TypeId, IntersectionTypeCacheKey>,
    type_resolutions: TypeResolutionStack,
    relations: RelationCaches,
    relation_inputs_generation: u64,
    relation_cache_generation: u64,
    relation_observable_types: HashSet<TypeId>,
    relation_observable_type_aliases: HashSet<TypeAliasId>,
    relation_observable_signatures: HashSet<SignatureId>,
    relation_observable_symbols: HashSet<SemanticSymbolId>,
    relation_observable_symbol_tables: HashSet<SymbolTableId>,
    relation_observable_object_instantiation_maps: HashSet<TypeId>,
    relation_observable_object_instantiations: HashSet<(TypeId, CacheHashKey)>,
    relation_observable_nodes: HashSet<NodeRef>,
    relation_observable_derived_cache_sources: HashSet<TypeId>,
    relation_observable_derived_cache_targets: HashSet<TypeId>,
    relation_observable_enum_pairs: HashSet<(SemanticSymbolId, SemanticSymbolId)>,
    relation_read_observation_active: AtomicBool,
    active_relation_read_observations: Mutex<Option<ActiveRelationReadObservations>>,
    next_relation_observation_token: u64,
    pub(super) derived_types: DerivedTypeCaches,
    pub(super) intrinsic_bootstrap: Option<IntrinsicBootstrap>,
    import_meta_global: Option<ResolvedGlobalType>,
    import_meta_expression: Option<ImportMetaExpressionIdentity>,
    canonical_union_creations: HashMap<TypeId, CanonicalUnionCreationProof>,
    union_alias_instantiations:
        HashMap<SemanticSymbolId, HashMap<CacheHashKey, UnionAliasInstantiationProof>>,
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
        let mut source_symbol_declarations = HashMap::new();
        let mut source_declaration_owners = HashMap::<NodeRef, Vec<SemanticSymbolId>>::new();
        for (symbol, record) in symbols.symbols() {
            let Some(declarations) = record.declarations() else {
                continue;
            };
            for declaration in declarations {
                source_declaration_owners
                    .entry(*declaration)
                    .or_default()
                    .push(symbol);
            }
            source_symbol_declarations.insert(
                symbol,
                SourceSymbolDeclarations {
                    flags: record.flags(),
                    declarations: declarations.into(),
                    value_declaration: record.value_declaration(),
                },
            );
        }
        Self {
            symbols,
            types: TypedArena::new(id),
            mappers: TypedArena::new(id),
            signatures: SignatureArena::new(id),
            predicates: TypePredicateArena::new(id),
            index_infos: IndexInfoArena::new(id),
            type_aliases: TypedArena::new(id),
            conditional_roots: TypedArena::new(id),
            conditional_type_productions: HashMap::new(),
            conditional_query_productions: HashMap::new(),
            entity_names: Vec::new(),
            source_files: BTreeMap::new(),
            source_file_facts: BTreeMap::new(),
            source_file_ranks: BTreeMap::new(),
            source_files_by_arena: BTreeMap::new(),
            source_node_facts: BTreeMap::new(),
            source_node_children: BTreeMap::new(),
            source_symbol_declarations,
            source_global_bindings: None,
            computed_method_name_groups: HashMap::new(),
            source_declaration_owners,
            type_alias_declared_type_owners: HashMap::new(),
            merged_symbols: HashMap::new(),
            links: CheckerLinkStores::default(),
            declared_types_in_progress: HashSet::new(),
            function_type_provenance: HashSet::new(),
            declared_call_set_provenance: HashSet::new(),
            declared_call_set_types_by_signature: HashMap::new(),
            direct_interface_heritage_provenance: HashMap::new(),
            direct_class_heritage_provenance: HashMap::new(),
            constructor_annotation_bindings: HashMap::new(),
            declared_value_provenance: HashMap::new(),
            instantiated_property_alias_callables: HashMap::new(),
            published_interface_method_origins: HashMap::new(),
            published_interface_method_signature_owners: HashMap::new(),
            published_interface_method_recoveries: HashMap::new(),
            instantiated_property_alias_callable_types_by_signature: HashMap::new(),
            instantiated_property_recoveries: HashMap::new(),
            instantiated_index_recoveries: HashMap::new(),
            property_object_alias_recoveries: HashMap::new(),
            inline_property_object_recoveries: HashMap::new(),
            property_object_alias_request_recoveries: HashMap::new(),
            ordinary_intersection_alias_request_recoveries: HashMap::new(),
            mapped_property_recoveries: HashMap::new(),
            mapped_index_recoveries: HashMap::new(),
            source_class_provenance: HashMap::new(),
            source_classes_by_symbol: HashMap::new(),
            class_instance_super_views: HashMap::new(),
            class_instance_super_views_by_instance: HashMap::new(),
            class_instance_super_members: HashMap::new(),
            source_callable_provenance: HashMap::new(),
            source_callable_interface_return_proofs: HashMap::new(),
            source_callable_alias_annotations: HashMap::new(),
            source_callable_alias_owners: HashMap::new(),
            source_jsdoc_typedefs: HashMap::new(),
            source_jsdoc_callbacks: HashMap::new(),
            source_callable_types_by_declaration: HashMap::new(),
            source_callable_types_by_owner: HashMap::new(),
            source_callable_types_by_signature: HashMap::new(),
            source_callable_type_parameters: HashMap::new(),
            source_callable_type_queries: HashMap::new(),
            module_value_identities: HashMap::new(),
            object_literal_property_clone_origins: HashMap::new(),
            object_literal_getter_origins: HashMap::new(),
            object_literal_getter_return_proofs: HashMap::new(),
            source_file_namespace_identities: HashMap::new(),
            source_file_namespace_wrappers: HashMap::new(),
            source_file_namespace_wrapper_aliases: HashMap::new(),
            source_file_namespace_wrapper_defaults: HashMap::new(),
            source_overload_provenance: HashMap::new(),
            source_overload_types_by_declaration: HashMap::new(),
            source_overload_types_by_owner: HashMap::new(),
            source_overload_types_by_signature: HashMap::new(),
            cached_signatures: HashMap::new(),
            unresolved_symbols: HashMap::new(),
            unresolved_symbol_keys: HashMap::new(),
            properties_types: HashMap::new(),
            function_signature_return_annotations: HashMap::new(),
            callable_signature_parameter_types: HashMap::new(),
            checked_source_callable_returns: HashMap::new(),
            signature_return_provenance: HashMap::new(),
            canonical_tuple_targets: HashMap::new(),
            canonical_empty_tuple: None,
            intersection_types: HashMap::new(),
            intersection_keys_by_type: HashMap::new(),
            type_resolutions: TypeResolutionStack::new(id),
            relations: RelationCaches::default(),
            relation_inputs_generation: 0,
            relation_cache_generation: 0,
            relation_observable_types: HashSet::new(),
            relation_observable_type_aliases: HashSet::new(),
            relation_observable_signatures: HashSet::new(),
            relation_observable_symbols: HashSet::new(),
            relation_observable_symbol_tables: HashSet::new(),
            relation_observable_object_instantiation_maps: HashSet::new(),
            relation_observable_object_instantiations: HashSet::new(),
            relation_observable_nodes: HashSet::new(),
            relation_observable_derived_cache_sources: HashSet::new(),
            relation_observable_derived_cache_targets: HashSet::new(),
            relation_observable_enum_pairs: HashSet::new(),
            relation_read_observation_active: AtomicBool::new(false),
            active_relation_read_observations: Mutex::new(None),
            next_relation_observation_token: 0,
            derived_types: DerivedTypeCaches::default(),
            intrinsic_bootstrap: None,
            import_meta_global: None,
            import_meta_expression: None,
            canonical_union_creations: HashMap::new(),
            union_alias_instantiations: HashMap::new(),
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

        let node_children = Self::index_source_node_children(&node_facts)?;
        if !self.symbols.register_ast_scope(AstScope::new(file, arena)) {
            return None;
        }
        let next_rank = self.source_files.len();
        self.source_file_ranks.entry(file).or_insert(next_rank);
        self.source_files.insert(file, source);
        self.source_files_by_arena.insert(arena.id(), source);
        self.source_node_facts.insert(arena.id(), node_facts);
        self.source_node_children.insert(arena.id(), node_children);
        Some(source)
    }

    /// Source registration follows the caller's Program order, not numeric file IDs.
    #[must_use]
    pub(super) fn source_file_rank(&self, file: FileId) -> Option<usize> {
        self.source_file_ranks.get(&file).copied()
    }

    /// Retains the binder's file facts once for semantic-only ownership checks.
    pub(super) fn register_source_file_facts(
        &mut self,
        source: SourceFileRef,
        facts: &CanonicalSourceFileFacts,
    ) -> bool {
        if !self.contains_source_file(source) {
            return false;
        }
        match self.source_file_facts.entry(source.file()) {
            std::collections::btree_map::Entry::Occupied(entry) => entry.get() == facts,
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(facts.clone());
                true
            }
        }
    }

    #[must_use]
    pub(super) fn source_is_default_library_declaration(&self, node: NodeRef) -> bool {
        self.contains_node_ref(node)
            && self.source_file_facts.get(&node.file).is_some_and(|facts| {
                facts.is_default_library()
                    && facts.is_declaration_file()
                    && !facts.is_javascript_file()
                    && !facts.is_external_or_common_js_module()
            })
    }

    /// Reads retained binder facts for an ambient script source.
    #[must_use]
    pub(super) fn source_is_script_declaration_file(&self, node: NodeRef) -> bool {
        self.contains_node_ref(node)
            && self.source_file_facts.get(&node.file).is_some_and(|facts| {
                facts.is_declaration_file()
                    && !facts.is_javascript_file()
                    && !facts.is_external_or_common_js_module()
            })
    }

    /// Reads retained binder facts for a TypeScript script source.
    #[must_use]
    pub(super) fn source_is_typescript_script(&self, node: NodeRef) -> bool {
        self.contains_node_ref(node)
            && self.source_file_facts.get(&node.file).is_some_and(|facts| {
                !facts.is_javascript_file() && !facts.is_external_or_common_js_module()
            })
    }

    /// Checks immutable binder ownership, including canonical merged-symbol redirects.
    #[must_use]
    pub(super) fn source_declaration_belongs_to_symbol(
        &self,
        declaration: NodeRef,
        symbol: SemanticSymbolId,
    ) -> bool {
        self.source_node_fact(declaration).is_some()
            && self
                .source_declaration_owners
                .get(&declaration)
                .is_some_and(|owners| {
                    owners
                        .iter()
                        .any(|owner| self.get_merged_symbol(*owner) == Some(symbol))
                })
    }

    /// Returns a declaration's unique binder owner after canonical merges.
    #[must_use]
    pub(super) fn source_declaration_symbol(
        &self,
        declaration: NodeRef,
    ) -> Option<SemanticSymbolId> {
        self.source_node_fact(declaration)?;
        let mut owner = None;
        for source in self.source_declaration_owners.get(&declaration)? {
            let symbol = self.get_merged_symbol(*source)?;
            if owner.is_some_and(|owner| owner != symbol) {
                return None;
            }
            owner = Some(symbol);
        }
        owner
    }

    /// Checks declarations against the symbol graph adopted from the binder.
    #[must_use]
    pub(super) fn source_symbol_declarations_match(&self, symbol: SemanticSymbolId) -> bool {
        let Some(source) = self.source_symbol_declarations.get(&symbol) else {
            return false;
        };
        self.symbol(symbol).is_some_and(|record| {
            record.declarations() == Some(source.declarations.as_ref())
                && record.value_declaration() == source.value_declaration
                && source.declarations.iter().all(|declaration| {
                    self.source_declaration_belongs_to_symbol(*declaration, symbol)
                })
        })
    }

    /// Reads original binder flags after canonical symbol merges.
    #[must_use]
    pub(super) fn source_symbol_flags(&self, symbol: SemanticSymbolId) -> Option<SymbolFlags> {
        std::iter::once(symbol)
            .chain(self.merged_symbols.keys().copied())
            .filter(|source| self.get_merged_symbol(*source) == Some(symbol))
            .filter_map(|source| self.source_symbol_declarations.get(&source))
            .map(|source| source.flags.without(SymbolFlags::TRANSIENT))
            .reduce(|left, right| left | right)
    }

    /// Saves global identities once, before source checks or artifact queries can run.
    pub(super) fn record_source_global_bindings(&mut self, table: SymbolTableId) -> bool {
        if self.source_global_bindings.is_some()
            || self
                .intrinsic_bootstrap
                .as_ref()
                .map(|bootstrap| bootstrap.globals)
                != Some(table)
        {
            return false;
        }
        let Some(globals) = self.symbol_table(table) else {
            return false;
        };
        let mut entries = HashMap::new();
        if entries.try_reserve(globals.len()).is_err() {
            return false;
        }
        for (name, table_symbol) in globals.iter() {
            let Some(symbol) = self.get_merged_symbol(table_symbol) else {
                return false;
            };
            let Some(record) = self.symbol(symbol) else {
                return false;
            };
            let declarations = if let Some(declarations) = record.declarations() {
                let mut snapshot = Vec::new();
                if snapshot.try_reserve_exact(declarations.len()).is_err() {
                    return false;
                }
                snapshot.extend_from_slice(declarations);
                Some(snapshot.into_boxed_slice())
            } else {
                None
            };
            entries.insert(
                name.to_owned(),
                SourceGlobalBinding {
                    table_symbol,
                    symbol,
                    flags: record.flags(),
                    declarations,
                },
            );
        }
        self.source_global_bindings = Some(SourceGlobalBindings { table, entries });
        true
    }

    pub(super) fn source_global_bindings(&self) -> Option<&SourceGlobalBindings> {
        self.source_global_bindings.as_ref()
    }

    /// Checks complete binder declarations and flags after canonical symbol merges.
    #[must_use]
    pub(super) fn source_merged_symbol_declarations_match(&self, symbol: SemanticSymbolId) -> bool {
        let Some(declarations) = self.symbol(symbol).and_then(Symbol::declarations) else {
            return false;
        };
        let mut expected = HashSet::new();
        let mut expected_flags = SymbolFlags::NONE;
        for source in std::iter::once(symbol).chain(self.merged_symbols.keys().copied()) {
            if self.get_merged_symbol(source) == Some(symbol)
                && let Some(original) = self.source_symbol_declarations.get(&source)
            {
                expected.extend(original.declarations.iter().copied());
                expected_flags |= original.flags.without(SymbolFlags::TRANSIENT);
            }
        }
        let actual = declarations.iter().copied().collect::<HashSet<_>>();
        !expected.is_empty()
            && actual.len() == declarations.len()
            && actual == expected
            && self.symbol(symbol).is_some_and(|record| {
                record.flags().without(SymbolFlags::TRANSIENT) == expected_flags
            })
            && declarations
                .iter()
                .all(|declaration| self.source_declaration_belongs_to_symbol(*declaration, symbol))
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
        self.observe_relation_type_alias_read(id);
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

    pub(super) fn conditional_type_production(
        &self,
        type_: TypeId,
    ) -> Option<&ConditionalTypeProduction> {
        self.conditional_type_productions.get(&type_)
    }

    pub(super) fn conditional_query_production(
        &self,
        key: ConditionalQueryKey,
    ) -> Option<&ConditionalQueryProduction> {
        self.conditional_query_productions.get(&key)
    }

    pub(super) fn try_reserve_conditional_productions(
        &mut self,
        types: usize,
        queries: usize,
    ) -> bool {
        self.conditional_type_productions.try_reserve(types).is_ok()
            && self
                .conditional_query_productions
                .try_reserve(queries)
                .is_ok()
    }

    pub(super) fn publish_conditional_type_production(
        &mut self,
        proof: ConditionalTypeProduction,
    ) -> bool {
        let type_ = proof.type_id();
        if self.types.get(type_).is_none()
            || self.conditional_roots.get(proof.root()).is_none()
            || self.conditional_type_productions.contains_key(&type_)
        {
            return false;
        }
        self.conditional_type_productions.insert(type_, proof);
        true
    }

    pub(super) fn publish_conditional_query_production(
        &mut self,
        proof: ConditionalQueryProduction,
    ) -> bool {
        let key = proof.key();
        let Some(root) = self.conditional_roots.get(proof.root()) else {
            return false;
        };
        let valid_key = match key {
            ConditionalQueryKey::Node(node) => root.node() == node,
            ConditionalQueryKey::Instantiation(root, _) => root == proof.root(),
            ConditionalQueryKey::AliasReference(node) => {
                self.source_node_kind(node) == Some(SyntaxKind::TypeReference)
            }
            ConditionalQueryKey::AliasDeclaration(symbol) => self.symbols.contains_symbol(symbol),
        };
        if !valid_key
            || self.types.get(proof.result()).is_none()
            || self.conditional_query_productions.contains_key(&key)
        {
            return false;
        }
        self.conditional_query_productions.insert(key, proof);
        true
    }

    #[cfg(test)]
    pub(super) fn conditional_production_lengths(&self) -> (usize, usize) {
        (
            self.conditional_type_productions.len(),
            self.conditional_query_productions.len(),
        )
    }

    #[must_use]
    pub fn type_payload(&self, id: TypeId) -> Option<&TypePayload> {
        self.observe_relation_type_read(id);
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

    pub(super) fn try_reserve_source_jsdoc_typedefs(&mut self, additional: usize) -> bool {
        self.source_jsdoc_typedefs.try_reserve(additional).is_ok()
    }

    pub(super) fn try_reserve_source_jsdoc_callbacks(&mut self, additional: usize) -> bool {
        self.source_jsdoc_callbacks.try_reserve(additional).is_ok()
    }

    pub(super) fn source_jsdoc_callback_type(
        &self,
        owner: NodeRef,
        range: TextRange,
    ) -> Option<TypeId> {
        self.source_jsdoc_callbacks
            .iter()
            .find_map(|(type_, identity)| {
                (identity.owner == owner && identity.definition.range() == range).then_some(*type_)
            })
    }

    pub(super) fn source_jsdoc_callback_identity(
        &self,
        type_: TypeId,
    ) -> Option<&SourceJsDocCallbackIdentity> {
        self.source_jsdoc_callbacks.get(&type_)
    }

    pub(super) fn source_jsdoc_callback_type_for_signature(
        &self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        self.source_jsdoc_callbacks
            .iter()
            .find_map(|(type_, identity)| (identity.signature == signature).then_some(*type_))
    }

    pub(super) fn publish_source_jsdoc_callback(
        &mut self,
        type_: TypeId,
        identity: SourceJsDocCallbackIdentity,
    ) -> bool {
        if self.types.get(type_).is_none()
            || self.source_node_kind(identity.owner).is_none()
            || self.source_jsdoc_callbacks.contains_key(&type_)
            || self
                .source_jsdoc_callback_type(identity.owner, identity.definition.range())
                .is_some()
        {
            return false;
        }
        self.source_jsdoc_callbacks.insert(type_, identity);
        true
    }

    pub(super) fn source_jsdoc_typedef_type(
        &self,
        owner: NodeRef,
        range: TextRange,
    ) -> Option<TypeId> {
        self.source_jsdoc_typedefs
            .iter()
            .find_map(|(type_, identity)| {
                (identity.owner == owner && identity.definition.range() == range).then_some(*type_)
            })
    }

    pub(super) fn source_jsdoc_typedef_identity(
        &self,
        type_: TypeId,
    ) -> Option<&SourceJsDocTypedefIdentity> {
        self.source_jsdoc_typedefs.get(&type_)
    }

    pub(super) fn publish_source_jsdoc_typedef(
        &mut self,
        type_: TypeId,
        identity: SourceJsDocTypedefIdentity,
    ) -> bool {
        if self.types.get(type_).is_none()
            || self.source_node_kind(identity.owner).is_none()
            || self.source_jsdoc_typedefs.contains_key(&type_)
            || self
                .source_jsdoc_typedef_type(identity.owner, identity.definition.range())
                .is_some()
        {
            return false;
        }
        self.source_jsdoc_typedefs.insert(type_, identity);
        true
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
        let inserted = self.function_type_provenance.insert(type_);
        if inserted && self.relation_type_is_observable(type_) {
            self.mark_relation_inputs_dirty();
        }
        inserted
    }

    pub(super) fn type_has_function_type_provenance(&self, type_: TypeId) -> bool {
        self.observe_relation_type_read(type_);
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
                            match self.source_node_kind(declaration) {
                                Some(SyntaxKind::CallSignature) => {
                                    record.flags().contains(SignatureFlags::CONSTRUCT)
                                }
                                Some(
                                    SyntaxKind::ConstructSignature | SyntaxKind::ConstructorType,
                                ) => !record.flags().contains(SignatureFlags::CONSTRUCT),
                                _ => true,
                            }
                        })
                    })
            })
        {
            return false;
        }
        let relation_dirty = self.relation_type_is_observable(type_)
            || signatures
                .iter()
                .any(|signature| self.relation_signature_is_observable(*signature));
        assert!(self.declared_call_set_provenance.insert(type_));
        for signature in signatures {
            assert!(
                self.declared_call_set_types_by_signature
                    .insert(*signature, type_)
                    .is_none()
            );
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    pub(super) fn type_has_declared_call_set_provenance(&self, type_: TypeId) -> bool {
        self.observe_relation_type_read(type_);
        self.declared_call_set_provenance.contains(&type_)
    }

    pub(super) fn declared_call_set_type_for_signature(
        &self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        self.observe_relation_signature_read(signature);
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
            && self
                .source_callable_type_queries
                .try_reserve(additional)
                .is_ok()
            && self
                .checked_source_callable_returns
                .try_reserve(additional)
                .is_ok()
    }

    pub(super) fn source_callable_type_parameters(
        &self,
        signature: SignatureId,
    ) -> Option<&[SourceCallableTypeParameterProvenance]> {
        self.observe_relation_signature_read(signature);
        self.source_callable_type_parameters
            .get(&signature)
            .map(Box::as_ref)
    }

    pub(super) fn source_callable_type_query(
        &self,
        signature: SignatureId,
    ) -> Option<&SourceCallableTypeQueryEvidence> {
        self.observe_relation_signature_read(signature);
        self.source_callable_type_queries
            .get(&signature)
            .map(Arc::as_ref)
    }

    #[cfg(test)]
    pub(super) fn source_callable_type_query_len(&self) -> usize {
        self.source_callable_type_queries.len()
    }

    #[cfg(test)]
    pub(super) fn replace_source_callable_type_query_for_test(
        &mut self,
        signature: SignatureId,
        replacement: Option<Arc<SourceCallableTypeQueryEvidence>>,
    ) -> Option<Arc<SourceCallableTypeQueryEvidence>> {
        match replacement {
            Some(replacement) => self
                .source_callable_type_queries
                .insert(signature, replacement),
            None => self.source_callable_type_queries.remove(&signature),
        }
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
        provenance: &SourceCallableProvenance,
    ) -> bool {
        let contextual_pair = match (provenance.contextual_target, provenance.contextual_variable) {
            (None, None) => provenance.captured_assignment.is_none(),
            (Some(target), Some(variable)) => {
                provenance.family == SourceCallableFamily::ArrowFunction
                    && provenance.return_provenance == SourceCallableReturnProvenance::Inferred
                    && provenance.captured_assignment.is_none()
                    && target != type_
                    && self.types.get(target).is_some()
                    && self.source_contextual_callable_anchor_is_exact(
                        provenance.declaration,
                        provenance.owner_symbol,
                        variable,
                    )
            }
            (Some(target), None) => {
                provenance.family == SourceCallableFamily::ArrowFunction
                    && provenance.return_provenance == SourceCallableReturnProvenance::Inferred
                    && target != type_
                    && self.types.get(target).is_some()
                    && (self.source_direct_call_contextual_callable_is_exact(
                        provenance.declaration,
                        provenance.owner_symbol,
                        provenance.signature,
                        target,
                        provenance.captured_assignment,
                    ) || provenance.captured_assignment.is_none()
                        && self.source_prototype_contextual_callable_is_exact(
                            provenance.declaration,
                            provenance.owner_symbol,
                            provenance.signature,
                            target,
                        ))
            }
            _ => false,
        };
        self.set_source_callable_provenance_with_context(type_, provenance, contextual_pair)
    }

    fn set_source_callable_provenance_with_context(
        &mut self,
        type_: TypeId,
        provenance: &SourceCallableProvenance,
        contextual_pair: bool,
    ) -> bool {
        let exact_type_parameters =
            self.signatures
                .get(provenance.signature)
                .is_some_and(|signature| {
                    signature.type_parameters().is_empty()
                        && !self
                            .source_callable_type_parameters
                            .contains_key(&provenance.signature)
                        && !self
                            .source_callable_type_queries
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
            || self
                .source_node_kind(provenance.declaration)
                .is_none_or(|kind| !provenance.family.matches_syntax_kind(kind))
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
            || self
                .signatures
                .get(provenance.signature)
                .is_none_or(|signature| signature.flags() != provenance.flags)
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
        let relation_dirty = self.relation_type_is_observable(type_)
            || self.relation_signature_is_observable(provenance.signature)
            || self
                .relation_observable_nodes
                .contains(&provenance.declaration)
            || self
                .relation_observable_symbols
                .contains(&provenance.owner_symbol);
        let by_type = self.source_callable_provenance.insert(type_, *provenance);
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
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    fn source_prototype_contextual_callable_is_exact(
        &self,
        declaration: NodeRef,
        owner_symbol: SemanticSymbolId,
        signature: SignatureId,
        contextual_target: TypeId,
    ) -> bool {
        let Some(owner) = self.symbol(owner_symbol) else {
            return false;
        };
        let Some(SourceNodeParent::Parent(assignment)) = self.source_node_parent(declaration)
        else {
            return false;
        };
        let Some(SourceNodeParent::Parent(statement)) = self.source_node_parent(assignment) else {
            return false;
        };
        let Some(SourceNodeParent::Parent(source)) = self.source_node_parent(statement) else {
            return false;
        };
        if self.source_node_kind(declaration) != Some(SyntaxKind::FunctionExpression)
            || self.source_node_kind(assignment) != Some(SyntaxKind::BinaryExpression)
            || self.source_node_kind(statement) != Some(SyntaxKind::ExpressionStatement)
            || self.source_node_kind(source) != Some(SyntaxKind::SourceFile)
            || owner.flags() != SymbolFlags::FUNCTION
            || owner.check_flags() != CheckFlags::NONE
            || owner.name() != InternalSymbolName::Function.as_ref()
            || owner.declarations() != Some(&[declaration])
            || owner.value_declaration() != Some(declaration)
            || owner.members().is_some()
            || owner.exports().is_some()
            || owner.parent().is_some()
            || owner.export_symbol().is_some()
            || self.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        {
            return false;
        }

        let unique_property_access = |parent: NodeRef| {
            let mut found = None;
            for (index, facts) in self
                .source_node_facts
                .get(&parent.arena)?
                .iter()
                .enumerate()
            {
                if facts.as_ref().is_some_and(|facts| {
                    facts.kind == SyntaxKind::PropertyAccessExpression
                        && facts.parent == Some(parent.node)
                }) {
                    let candidate = NodeRef::new(
                        parent.arena,
                        parent.file,
                        NodeId::new(u32::try_from(index).ok()?),
                    );
                    if found.replace(candidate).is_some() {
                        return None;
                    }
                }
            }
            found
        };
        let Some(left) = unique_property_access(assignment) else {
            return false;
        };
        let Some(prototype_access) = unique_property_access(left) else {
            return false;
        };
        let Some(facts) = self.source_node_facts.get(&declaration.arena) else {
            return false;
        };
        let mut assignment_children = facts.iter().enumerate().filter_map(|(index, facts)| {
            let facts = facts.as_ref()?;
            (facts.parent == Some(assignment.node)).then_some((index, facts.kind))
        });
        if assignment_children.next()
            != Some((left.node.index(), SyntaxKind::PropertyAccessExpression))
            || assignment_children
                .next()
                .is_none_or(|(_, kind)| kind != SyntaxKind::EqualsToken)
            || assignment_children.next()
                != Some((declaration.node.index(), SyntaxKind::FunctionExpression))
            || assignment_children.next().is_some()
        {
            return false;
        }

        let mut prototype_children = facts.iter().enumerate().filter_map(|(index, facts)| {
            let facts = facts.as_ref()?;
            (facts.parent == Some(prototype_access.node)).then_some((index, facts.kind))
        });
        let Some((receiver_index, SyntaxKind::Identifier)) = prototype_children.next() else {
            return false;
        };
        if !matches!(prototype_children.next(), Some((_, SyntaxKind::Identifier)))
            || prototype_children.next().is_some()
        {
            return false;
        }
        let Ok(receiver_index) = u32::try_from(receiver_index) else {
            return false;
        };
        let receiver = NodeRef::new(
            declaration.arena,
            declaration.file,
            NodeId::new(receiver_index),
        );
        let Some(method_symbol) = self
            .links
            .value_symbol
            .find_key(|symbol| {
                self.symbol(*symbol)
                    .is_some_and(|method| method.flags() == SymbolFlags::METHOD)
                    && self.value_symbol_links(*symbol)
                        == Some(&ValueSymbolLinks {
                            resolved_type: Some(contextual_target),
                            ..ValueSymbolLinks::default()
                        })
            })
            .copied()
        else {
            return false;
        };
        let Some(method) = self.symbol(method_symbol) else {
            return false;
        };
        let Some([method_declaration]) = method.declarations() else {
            return false;
        };
        let method_declaration = *method_declaration;
        let Some(class_symbol) = method.parent() else {
            return false;
        };
        let Some(class) = self.symbol(class_symbol) else {
            return false;
        };
        let Some([class_declaration]) = class.declarations() else {
            return false;
        };
        let class_declaration = *class_declaration;
        let Some(method_name) = method.name().as_utf8() else {
            return false;
        };
        let Some(class_type) = self
            .declared_type_links(class_symbol)
            .and_then(|links| links.declared_type)
        else {
            return false;
        };
        let Some(class_value) = self
            .value_symbol_links(class_symbol)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        let Some(prototype_symbol) = class
            .exports()
            .and_then(|exports| self.symbol_table(exports))
            .and_then(|exports| exports.get_source("prototype"))
        else {
            return false;
        };
        let Some(prototype) = self.symbol(prototype_symbol) else {
            return false;
        };
        if method.check_flags() != CheckFlags::NONE
            || method.value_declaration() != Some(method_declaration)
            || method.members().is_some()
            || method.exports().is_some()
            || method.export_symbol().is_some()
            || self.get_merged_symbol(method_symbol) != Some(method_symbol)
            || self.source_node_kind(method_declaration) != Some(SyntaxKind::MethodDeclaration)
            || self.source_node_parent(method_declaration)
                != Some(SourceNodeParent::Parent(class_declaration))
            || class.flags() != SymbolFlags::CLASS
            || class.check_flags() != CheckFlags::NONE
            || class.value_declaration() != Some(class_declaration)
            || class.parent().is_some()
            || class.export_symbol().is_some()
            || self.get_merged_symbol(class_symbol) != Some(class_symbol)
            || self.value_symbol_links(class_symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(class_value),
                    ..ValueSymbolLinks::default()
                })
            || self.source_node_kind(class_declaration) != Some(SyntaxKind::ClassDeclaration)
            || self.source_node_parent(class_declaration) != Some(SourceNodeParent::Parent(source))
            || class
                .members()
                .and_then(|members| self.symbol_table(members))
                .and_then(|members| members.get_source(method_name))
                != Some(method_symbol)
            || prototype.flags() != SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE
            || prototype.check_flags() != CheckFlags::NONE
            || prototype.name().as_utf8() != Some("prototype")
            || prototype.declarations().is_some()
            || prototype.value_declaration().is_some()
            || prototype.members().is_some()
            || prototype.exports().is_some()
            || prototype.parent() != Some(class_symbol)
            || prototype.export_symbol().is_some()
            || self.get_merged_symbol(prototype_symbol) != Some(prototype_symbol)
            || self.type_node_links(receiver)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(class_value),
                    ..TypeNodeLinks::default()
                })
            || self.symbol_node_links(receiver).is_some_and(|links| {
                links != &SymbolNodeLinks::default()
                    && links
                        != &SymbolNodeLinks {
                            resolved_symbol: Some(class_symbol),
                        }
            })
            || self.type_node_links(left)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(contextual_target),
                    ..TypeNodeLinks::default()
                })
            || self.type_node_links(prototype_access)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(class_type),
                    ..TypeNodeLinks::default()
                })
            || self.symbol_node_links(left).is_some_and(|links| {
                links != &SymbolNodeLinks::default()
                    && links
                        != &SymbolNodeLinks {
                            resolved_symbol: Some(method_symbol),
                        }
            })
            || self
                .symbol_node_links(prototype_access)
                .is_some_and(|links| {
                    links != &SymbolNodeLinks::default()
                        && links
                            != &SymbolNodeLinks {
                                resolved_symbol: Some(prototype_symbol),
                            }
                })
        {
            return false;
        }

        let Some(target_signature) = self
            .signature_links(method_declaration)
            .and_then(|links| links.resolved_signature.signature())
        else {
            return false;
        };
        if self.declared_method_linked_type(target_signature, method_symbol)
            != Some(contextual_target)
        {
            return false;
        }
        let Some(target_record) = self.signature(target_signature) else {
            return false;
        };
        let Some(record) = self.signature(signature) else {
            return false;
        };
        let parameters = record.parameters();
        if self.signature_links(method_declaration)
            != Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(target_signature),
                ..SignatureLinks::default()
            })
            || target_record.declaration() != Some(method_declaration)
            || record.declaration() != Some(declaration)
            || target_record.flags() != SignatureFlags::NONE
            || record.flags() != target_record.flags()
            || !target_record.type_parameters().is_empty()
            || !record.type_parameters().is_empty()
            || target_record.this_parameter().is_some()
            || record.this_parameter().is_some()
            || parameters.is_empty()
            || target_record.parameters().len() != parameters.len()
            || usize::try_from(target_record.min_argument_count()).ok() != Some(parameters.len())
            || record.min_argument_count() != target_record.min_argument_count()
            || target_record.resolved_min_argument_count() != -1
            || record.resolved_min_argument_count() != -1
            || target_record
                .resolved_return_type()
                .is_none_or(|type_| self.types.get(type_).is_none())
            || record.resolved_return_type() != target_record.resolved_return_type()
            || target_record.resolved_type_predicate().is_some()
            || record.resolved_type_predicate().is_some()
            || target_record.target().is_some()
            || record.target().is_some()
            || target_record.mapper().is_some()
            || record.mapper().is_some()
            || target_record.isolated_signature_type().is_some()
            || record.isolated_signature_type().is_some()
            || target_record.composite().is_some()
            || record.composite().is_some()
        {
            return false;
        }

        parameters
            .iter()
            .zip(target_record.parameters())
            .enumerate()
            .all(|(index, (parameter, target_parameter))| {
                let Some(parameter_record) = self.symbol(*parameter) else {
                    return false;
                };
                let Some([parameter_declaration]) = parameter_record.declarations() else {
                    return false;
                };
                let parameter_declaration = *parameter_declaration;
                let Some(target_parameter_record) = self.symbol(*target_parameter) else {
                    return false;
                };
                let Some([target_parameter_declaration]) = target_parameter_record.declarations()
                else {
                    return false;
                };
                let target_parameter_declaration = *target_parameter_declaration;
                let Some(expected_type) = self
                    .value_symbol_links(*target_parameter)
                    .and_then(|links| links.resolved_type)
                else {
                    return false;
                };
                !parameters[..index].contains(parameter)
                    && !target_record.parameters()[..index].contains(target_parameter)
                    && parameter_record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    && parameter_record.check_flags() == CheckFlags::NONE
                    && parameter_record.value_declaration() == Some(parameter_declaration)
                    && parameter_record.members().is_none()
                    && parameter_record.exports().is_none()
                    && parameter_record.parent().is_none()
                    && parameter_record.export_symbol().is_none()
                    && self.get_merged_symbol(*parameter) == Some(*parameter)
                    && self.source_node_kind(parameter_declaration) == Some(SyntaxKind::Parameter)
                    && self.source_node_parent(parameter_declaration)
                        == Some(SourceNodeParent::Parent(declaration))
                    && target_parameter_record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    && target_parameter_record.check_flags() == CheckFlags::NONE
                    && target_parameter_record.value_declaration()
                        == Some(target_parameter_declaration)
                    && target_parameter_record.members().is_none()
                    && target_parameter_record.exports().is_none()
                    && target_parameter_record.parent().is_none()
                    && target_parameter_record.export_symbol().is_none()
                    && self.get_merged_symbol(*target_parameter) == Some(*target_parameter)
                    && self.source_node_kind(target_parameter_declaration)
                        == Some(SyntaxKind::Parameter)
                    && self.source_node_parent(target_parameter_declaration)
                        == Some(SourceNodeParent::Parent(method_declaration))
                    && self.types.get(expected_type).is_some()
                    && self.value_symbol_links(*target_parameter)
                        == Some(&ValueSymbolLinks {
                            resolved_type: Some(expected_type),
                            ..ValueSymbolLinks::default()
                        })
                    && self.value_symbol_links(*parameter).is_none_or(|links| {
                        links == &ValueSymbolLinks::default()
                            || links
                                == &ValueSymbolLinks {
                                    resolved_type: Some(expected_type),
                                    ..ValueSymbolLinks::default()
                                }
                    })
            })
    }

    fn source_direct_call_contextual_callable_is_exact(
        &self,
        declaration: NodeRef,
        owner_symbol: SemanticSymbolId,
        signature: SignatureId,
        contextual_target: TypeId,
        captured_assignment: Option<SourceCapturedLocal>,
    ) -> bool {
        let Some(owner) = self.symbol(owner_symbol) else {
            return false;
        };
        let Some(SourceNodeParent::Parent(call)) = self.source_node_parent(declaration) else {
            return false;
        };
        let Some(SourceNodeParent::Parent(container)) = self.source_node_parent(call) else {
            return false;
        };
        let source = match self.source_node_kind(container) {
            Some(SyntaxKind::ExpressionStatement) if captured_assignment.is_none() => {
                let Some(SourceNodeParent::Parent(source)) = self.source_node_parent(container)
                else {
                    return false;
                };
                source
            }
            Some(SyntaxKind::VariableDeclaration) if captured_assignment.is_none() => {
                let Some(SourceNodeParent::Parent(list)) = self.source_node_parent(container)
                else {
                    return false;
                };
                let Some(SourceNodeParent::Parent(statement)) = self.source_node_parent(list)
                else {
                    return false;
                };
                let Some(SourceNodeParent::Parent(source)) = self.source_node_parent(statement)
                else {
                    return false;
                };
                if self.source_node_kind(list) != Some(SyntaxKind::VariableDeclarationList)
                    || self.source_node_kind(statement) != Some(SyntaxKind::VariableStatement)
                {
                    return false;
                }
                source
            }
            Some(SyntaxKind::BinaryExpression) => {
                let Some(captured) = captured_assignment else {
                    return false;
                };
                let Some(bootstrap) = self.intrinsic_bootstrap.as_ref() else {
                    return false;
                };
                if !super::source_callables::stored_captured_assignment_callback_is_exact(
                    self,
                    declaration,
                    owner_symbol,
                    captured,
                    bootstrap.globals,
                ) {
                    return false;
                }
                let Some(source) = self.source_files.get(&declaration.file) else {
                    return false;
                };
                source.node_ref()
            }
            _ => return false,
        };
        if self.source_node_kind(declaration) != Some(SyntaxKind::ArrowFunction)
            || !matches!(
                (
                    self.source_node_kind(call),
                    self.source_node_kind(container)
                ),
                (Some(SyntaxKind::CallExpression), _)
                    | (
                        Some(SyntaxKind::NewExpression),
                        Some(SyntaxKind::ExpressionStatement)
                    )
            )
            || self.source_node_kind(source) != Some(SyntaxKind::SourceFile)
            || owner.flags() != SymbolFlags::FUNCTION
            || owner.check_flags() != CheckFlags::NONE
            || owner.name() != InternalSymbolName::Function.as_ref()
            || owner.declarations() != Some(&[declaration])
            || owner.value_declaration() != Some(declaration)
            || owner.members().is_some()
            || owner.exports().is_some()
            || owner.parent().is_some()
            || owner.export_symbol().is_some()
            || self.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        {
            return false;
        }

        let Some(record) = self.signature(signature) else {
            return false;
        };
        let parameters = record.parameters();
        if record.declaration() != Some(declaration)
            || record.flags() != SignatureFlags::NONE
            || !record.type_parameters().is_empty()
            || record.this_parameter().is_some()
            || parameters.is_empty()
            || usize::try_from(record.min_argument_count()).ok() != Some(parameters.len())
            || record.resolved_min_argument_count() != -1
            || record
                .resolved_return_type()
                .is_none_or(|type_| self.types.get(type_).is_none())
            || record.resolved_type_predicate().is_some()
            || record.target().is_some()
            || record.mapper().is_some()
            || record.isolated_signature_type().is_some()
            || record.composite().is_some()
            || parameters.iter().enumerate().any(|(index, parameter)| {
                let Some(parameter_record) = self.symbol(*parameter) else {
                    return true;
                };
                let Some([parameter_declaration]) = parameter_record.declarations() else {
                    return true;
                };
                let parameter_declaration = *parameter_declaration;
                parameters[..index].contains(parameter)
                    || parameter_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    || parameter_record.check_flags() != CheckFlags::NONE
                    || parameter_record.value_declaration() != Some(parameter_declaration)
                    || parameter_record.members().is_some()
                    || parameter_record.exports().is_some()
                    || parameter_record.parent().is_some()
                    || parameter_record.export_symbol().is_some()
                    || self.get_merged_symbol(*parameter) != Some(*parameter)
                    || self.source_node_kind(parameter_declaration) != Some(SyntaxKind::Parameter)
                    || self.source_node_parent(parameter_declaration)
                        != Some(SourceNodeParent::Parent(declaration))
            })
        {
            return false;
        }

        let mut expected_parameters = None;
        for (target_signature, target_record) in self.signatures.iter() {
            let Some(target_declaration) = target_record.declaration() else {
                continue;
            };
            let function_type = self.function_type_provenance.contains(&contextual_target)
                && self.source_node_kind(target_declaration) == Some(SyntaxKind::FunctionType)
                && self
                    .signature_links(target_declaration)
                    .and_then(|links| links.resolved_signature.signature())
                    == Some(target_signature)
                && self.type_node_links(target_declaration)
                    == Some(&TypeNodeLinks {
                        resolved_type: Some(contextual_target),
                        ..TypeNodeLinks::default()
                    });
            let source_callable = self
                .source_callable_provenance
                .get(&contextual_target)
                .is_some_and(|provenance| {
                    provenance.signature == target_signature
                        && provenance.declaration == target_declaration
                });
            if !function_type && !source_callable {
                continue;
            }
            let Some(target_parameters) = self
                .callable_signature_parameter_types
                .get(&target_signature)
                .map(Vec::as_slice)
            else {
                return false;
            };
            if target_parameters.is_empty() {
                return false;
            }
            if self.signature_links(target_declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(target_signature),
                    ..SignatureLinks::default()
                })
                || !target_record.type_parameters().is_empty()
                || target_record.has_rest_parameter()
                || target_record.min_argument_count() < 1
                || target_record.parameters().len() != target_parameters.len()
                || usize::try_from(target_record.min_argument_count())
                    .ok()
                    .is_none_or(|minimum| minimum > target_parameters.len())
                || target_record
                    .parameters()
                    .iter()
                    .copied()
                    .zip(target_parameters)
                    .any(|(parameter, type_)| {
                        self.types.get(*type_).is_none()
                            || self.value_symbol_links(parameter)
                                != Some(&ValueSymbolLinks {
                                    resolved_type: Some(*type_),
                                    ..ValueSymbolLinks::default()
                                })
                    })
                || expected_parameters
                    .replace((target_parameters, target_declaration))
                    .is_some()
            {
                return false;
            }
        }
        let Some((expected_parameters, target_declaration)) = expected_parameters else {
            return false;
        };
        if parameters.len() > expected_parameters.len()
            || parameters.len() > 1
                && (parameters.len() != 2
                    || expected_parameters.len() != 2
                    || !self.source_direct_array_sort_callback_target_is_exact(
                        declaration,
                        call,
                        contextual_target,
                        target_declaration,
                    ))
        {
            return false;
        }
        parameters
            .iter()
            .zip(expected_parameters)
            .all(|(parameter, expected_parameter)| {
                self.value_symbol_links(*parameter).is_none_or(|links| {
                    links == &ValueSymbolLinks::default()
                        || links.resolved_type.is_some_and(|actual| {
                            links
                                == &ValueSymbolLinks {
                                    resolved_type: Some(actual),
                                    ..ValueSymbolLinks::default()
                                }
                                && (actual == *expected_parameter
                                    || parameters.len() == 1
                                        && self.source_direct_array_callback_parameter_is_exact(
                                            contextual_target,
                                            target_declaration,
                                            *expected_parameter,
                                            actual,
                                        ))
                        })
                })
            })
    }

    fn source_direct_array_sort_callback_target_is_exact(
        &self,
        declaration: NodeRef,
        call: NodeRef,
        contextual_target: TypeId,
        callback_declaration: NodeRef,
    ) -> bool {
        let Some(SourceNodeParent::Parent(parameter_declaration)) =
            self.source_node_parent(callback_declaration)
        else {
            return false;
        };
        let Some(SourceNodeParent::Parent(method_declaration)) =
            self.source_node_parent(parameter_declaration)
        else {
            return false;
        };
        let Some(array) = self
            .intrinsic_bootstrap
            .as_ref()
            .and_then(|bootstrap| self.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Array"))
            .and_then(|symbol| self.get_merged_symbol(symbol))
        else {
            return false;
        };
        let Some(array_type) = self
            .declared_type_links(array)
            .and_then(|links| links.declared_type)
        else {
            return false;
        };
        let Some(method) = self
            .symbol(array)
            .and_then(Symbol::members)
            .and_then(|members| self.symbol_table(members))
            .and_then(|members| members.get_source("sort"))
            .and_then(|symbol| self.get_merged_symbol(symbol))
        else {
            return false;
        };
        if self.source_node_kind(call) != Some(SyntaxKind::CallExpression)
            || !self.function_type_provenance.contains(&contextual_target)
            || self.source_node_kind(callback_declaration) != Some(SyntaxKind::FunctionType)
            || self.source_node_kind(parameter_declaration) != Some(SyntaxKind::Parameter)
            || self.source_node_kind(method_declaration) != Some(SyntaxKind::MethodSignature)
            || self.source_direct_type_annotation(parameter_declaration)
                != Some(callback_declaration)
            || self
                .type_node_links(callback_declaration)
                .and_then(|links| links.resolved_type)
                != Some(contextual_target)
            || self.authenticated_interface_method_owner(method) != Some((array, array_type))
            || self
                .symbol(method)
                .and_then(Symbol::declarations)
                .is_none_or(|declarations| !declarations.contains(&method_declaration))
        {
            return false;
        }

        let mut property = None;
        for index in 0..declaration.node.index() {
            let Ok(index) = u32::try_from(index) else {
                return false;
            };
            let candidate = NodeRef::new(declaration.arena, declaration.file, NodeId::new(index));
            if self.source_node_kind(candidate) == Some(SyntaxKind::PropertyAccessExpression)
                && self.source_node_parent(candidate) == Some(SourceNodeParent::Parent(call))
                && property.replace(candidate).is_some()
            {
                return false;
            }
        }
        property.is_some_and(|property| {
            self.symbol_node_links(property)
                .and_then(|links| links.resolved_symbol)
                == Some(method)
                && self
                    .type_node_links(property)
                    .and_then(|links| links.resolved_type)
                    .is_some()
        })
    }

    fn source_direct_array_callback_parameter_is_exact(
        &self,
        contextual_target: TypeId,
        callback_declaration: NodeRef,
        source_parameter: TypeId,
        actual_parameter: TypeId,
    ) -> bool {
        let Some(parameter_symbol) = self
            .links
            .declared_type
            .find_key(|symbol| {
                self.links
                    .declared_type
                    .try_get(symbol)
                    .is_some_and(|links| links.declared_type == Some(source_parameter))
                    && self.symbol(*symbol).is_some_and(|record| {
                        record.flags().contains(SymbolFlags::TYPE_PARAMETER)
                            && !record
                                .flags()
                                .intersects(SymbolFlags::TYPE_PARAMETER_EXCLUDES)
                    })
            })
            .copied()
        else {
            return false;
        };
        let Some(owner) = self.get_parent_of_symbol(parameter_symbol) else {
            return false;
        };
        let Some(owner_record) = self.symbol(owner) else {
            return false;
        };
        let Some(owner_name) = owner_record.name().as_utf8() else {
            return false;
        };
        let Some(SourceNodeParent::Parent(parameter_declaration)) =
            self.source_node_parent(callback_declaration)
        else {
            return false;
        };
        let Some(SourceNodeParent::Parent(method_declaration)) =
            self.source_node_parent(parameter_declaration)
        else {
            return false;
        };
        let Some(members) = owner_record
            .members()
            .and_then(|members| self.symbol_table(members))
        else {
            return false;
        };
        matches!(owner_name, "Array" | "ReadonlyArray")
            && self
                .intrinsic_bootstrap
                .as_ref()
                .and_then(|bootstrap| self.symbol_table(bootstrap.globals))
                .and_then(|globals| globals.get_source(owner_name))
                .and_then(|symbol| self.get_merged_symbol(symbol))
                == Some(owner)
            && self.types.get(actual_parameter).is_some()
            && self.function_type_provenance.contains(&contextual_target)
            && self.source_node_kind(callback_declaration) == Some(SyntaxKind::FunctionType)
            && self.source_direct_type_annotation(parameter_declaration)
                == Some(callback_declaration)
            && self
                .type_node_links(callback_declaration)
                .and_then(|links| links.resolved_type)
                == Some(contextual_target)
            && members.iter().any(|(_, method)| {
                self.get_merged_symbol(method).is_some_and(|method| {
                    self.symbol(method).is_some_and(|record| {
                        record.flags() == SymbolFlags::METHOD
                            && record.name().as_utf8().is_some_and(|name| {
                                matches!(name, "map" | "filter" | "find" | "forEach")
                            })
                            && record.declarations().is_some_and(|declarations| {
                                declarations.contains(&method_declaration)
                            })
                            && self.get_parent_of_symbol(method) == Some(owner)
                    })
                })
            })
    }

    /// Proves the exact variable or object-property owner of a contextual arrow.
    pub(super) fn source_contextual_callable_anchor_is_exact(
        &self,
        declaration: NodeRef,
        owner_symbol: SemanticSymbolId,
        anchor: SemanticSymbolId,
    ) -> bool {
        let Some(owner) = self.symbol(owner_symbol) else {
            return false;
        };
        if anchor == owner_symbol
            || self.get_merged_symbol(owner_symbol) != Some(owner_symbol)
            || self.get_merged_symbol(anchor) != Some(anchor)
            || self.source_node_kind(declaration) != Some(SyntaxKind::ArrowFunction)
            || owner.flags() != SymbolFlags::FUNCTION
            || owner.check_flags() != CheckFlags::NONE
            || owner.declarations() != Some(&[declaration])
            || owner.value_declaration() != Some(declaration)
            || owner.members().is_some()
            || owner.parent().is_some()
            || owner.export_symbol().is_some()
        {
            return false;
        }
        let Some(symbol) = self.symbol(anchor) else {
            return false;
        };
        let Some([anchor_declaration]) = symbol.declarations() else {
            return false;
        };
        let anchor_declaration = *anchor_declaration;
        if symbol.check_flags() != CheckFlags::NONE
            || symbol.value_declaration() != Some(anchor_declaration)
            || symbol.members().is_some()
            || symbol.exports().is_some()
            || symbol.export_symbol().is_some()
        {
            return false;
        }

        if symbol.flags() == SymbolFlags::BLOCK_SCOPED_VARIABLE {
            return symbol.parent().is_none()
                && self.source_node_kind(anchor_declaration)
                    == Some(SyntaxKind::VariableDeclaration)
                && (owner.exports().is_none()
                    || self.source_contextual_variable_expando_exports_are_exact(
                        declaration,
                        owner_symbol,
                        anchor_declaration,
                    ));
        }
        if owner.exports().is_some()
            || symbol.flags() != SymbolFlags::PROPERTY
            || self.source_node_kind(anchor_declaration) != Some(SyntaxKind::PropertyAssignment)
            || self.source_node_parent(declaration)
                != Some(SourceNodeParent::Parent(anchor_declaration))
        {
            return false;
        }

        let Some(SourceNodeParent::Parent(object_declaration)) =
            self.source_node_parent(anchor_declaration)
        else {
            return false;
        };
        let Some(object_owner) = symbol
            .parent()
            .and_then(|parent| self.get_merged_symbol(parent))
        else {
            return false;
        };
        let Some(object) = self.symbol(object_owner) else {
            return false;
        };
        self.source_node_kind(object_declaration) == Some(SyntaxKind::ObjectLiteralExpression)
            && object.flags() == SymbolFlags::OBJECT_LITERAL
            && object.check_flags() == CheckFlags::NONE
            && object.declarations() == Some(&[object_declaration])
            && object.value_declaration() == Some(object_declaration)
            && object.parent().is_none()
            && object.exports().is_none()
            && object.export_symbol().is_none()
            && self.get_merged_symbol(object_owner) == Some(object_owner)
            && object
                .members()
                .and_then(|members| self.symbol_table(members))
                .and_then(|members| members.get(symbol.name()))
                == Some(anchor)
    }

    fn source_contextual_variable_expando_exports_are_exact(
        &self,
        declaration: NodeRef,
        owner_symbol: SemanticSymbolId,
        variable: NodeRef,
    ) -> bool {
        let Some(owner) = self.symbol(owner_symbol) else {
            return false;
        };
        let Some(exports) = owner
            .exports()
            .and_then(|exports| self.symbol_table(exports))
        else {
            return false;
        };
        let Some(SourceNodeParent::Parent(list)) = self.source_node_parent(variable) else {
            return false;
        };
        let Some(SourceNodeParent::Parent(variable_statement)) = self.source_node_parent(list)
        else {
            return false;
        };
        let Some(SourceNodeParent::Parent(source)) = self.source_node_parent(variable_statement)
        else {
            return false;
        };
        let Some(facts) = self.source_node_facts.get(&declaration.arena) else {
            return false;
        };
        let mut annotations = facts.iter().enumerate().filter_map(|(index, facts)| {
            let facts = facts.as_ref()?;
            (facts.kind == SyntaxKind::TypeLiteral && facts.parent == Some(variable.node))
                .then_some(index)
        });
        let Some(annotation) = annotations.next() else {
            return false;
        };
        let Ok(annotation) = u32::try_from(annotation) else {
            return false;
        };
        let annotation = NodeRef::new(declaration.arena, declaration.file, NodeId::new(annotation));
        let Some(target) = self
            .type_node_links(annotation)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        if exports.is_empty()
            || annotations.next().is_some()
            || self.source_node_parent(declaration) != Some(SourceNodeParent::Parent(variable))
            || self.source_node_kind(list) != Some(SyntaxKind::VariableDeclarationList)
            || self.source_node_kind(variable_statement) != Some(SyntaxKind::VariableStatement)
            || self.source_node_kind(source) != Some(SyntaxKind::SourceFile)
            || !self.type_has_declared_call_set_provenance(target)
        {
            return false;
        }

        exports.iter().all(|(name, property_symbol)| {
            let Some(property) = self.symbol(property_symbol) else {
                return false;
            };
            let Some([assignment]) = property.declarations() else {
                return false;
            };
            let assignment = *assignment;
            let Some(SourceNodeParent::Parent(statement)) = self.source_node_parent(assignment)
            else {
                return false;
            };
            let matching_declared_property = self.links.value_symbol.find_key(|candidate| {
                let Some(declared) = self.symbol(*candidate) else {
                    return false;
                };
                let Some([property_declaration]) = declared.declarations() else {
                    return false;
                };
                let Some(target_owner) = declared.parent().and_then(|owner| self.symbol(owner))
                else {
                    return false;
                };
                let flags = declared.flags();
                (flags == SymbolFlags::PROPERTY
                    || flags == (SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL))
                    && declared.name() == name
                    && declared.check_flags() == CheckFlags::NONE
                    && declared.value_declaration() == Some(*property_declaration)
                    && declared.members().is_none()
                    && declared.exports().is_none()
                    && declared.export_symbol().is_none()
                    && self.get_merged_symbol(*candidate) == Some(*candidate)
                    && target_owner.flags() == SymbolFlags::TYPE_LITERAL
                    && target_owner.declarations() == Some(&[annotation])
                    && self.source_node_kind(*property_declaration)
                        == Some(SyntaxKind::PropertyDeclaration)
                    && self.source_node_parent(*property_declaration)
                        == Some(SourceNodeParent::Parent(annotation))
                    && self
                        .value_symbol_links(*candidate)
                        .and_then(|links| links.resolved_type)
                        .is_some_and(|type_| self.types.get(type_).is_some())
            });
            property.flags() == (SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT)
                && property.check_flags() == CheckFlags::NONE
                && property.name() == name
                && property.value_declaration() == Some(assignment)
                && property.members().is_none()
                && property.exports().is_none()
                && property.parent() == Some(owner_symbol)
                && property.export_symbol().is_none()
                && self.get_merged_symbol(property_symbol) == Some(property_symbol)
                && self.source_node_kind(assignment) == Some(SyntaxKind::BinaryExpression)
                && self.source_node_kind(statement) == Some(SyntaxKind::ExpressionStatement)
                && self.source_node_parent(statement) == Some(SourceNodeParent::Parent(source))
                && matching_declared_property.is_some()
        })
    }

    pub(super) fn source_callable_provenance(
        &self,
        type_: TypeId,
    ) -> Option<SourceCallableProvenance> {
        self.observe_relation_type_read(type_);
        self.source_callable_provenance.get(&type_).copied()
    }

    pub(super) fn source_callable_alias_annotation(
        &self,
        annotation: NodeRef,
    ) -> Option<&SourceCallableAliasAnnotation> {
        self.observe_relation_node_read(annotation);
        self.source_callable_alias_annotations
            .get(&annotation)
            .map(|(proof, _)| proof)
    }

    /// Reads the retained import proof, including an orphan left by a changed return cache.
    pub(super) fn source_callable_interface_return_proof(
        &self,
        signature: SignatureId,
    ) -> Option<SourceCallableInterfaceReturnProof> {
        self.observe_relation_signature_read(signature);
        self.source_callable_interface_return_proofs
            .get(&signature)
            .copied()
    }

    #[cfg(test)]
    pub(super) fn source_callable_interface_return_proof_count(&self) -> usize {
        self.source_callable_interface_return_proofs.len()
    }

    #[cfg(test)]
    pub(super) fn replace_source_callable_interface_return_proof_for_test(
        &mut self,
        signature: SignatureId,
        replacement: Option<SourceCallableInterfaceReturnProof>,
    ) -> Option<SourceCallableInterfaceReturnProof> {
        let previous = self
            .source_callable_interface_return_proofs
            .get(&signature)
            .copied();
        if previous == replacement {
            return previous;
        }
        match replacement {
            Some(proof) => {
                self.source_callable_interface_return_proofs
                    .insert(signature, proof);
            }
            None => {
                self.source_callable_interface_return_proofs
                    .remove(&signature);
            }
        }
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        previous
    }

    pub(super) fn source_callable_alias_parameter_annotation(
        &self,
        parameter: SemanticSymbolId,
    ) -> Option<NodeRef> {
        self.observe_relation_symbol_read(parameter);
        self.source_callable_alias_owners.get(&parameter).copied()
    }

    pub(super) fn source_callable_alias_resolution_matches(
        &self,
        proof: &SourceCallableAliasAnnotation,
        resolution: &SourceCallableAliasSnapshot,
    ) -> bool {
        self.observe_relation_node_read(proof.annotation());
        self.source_callable_alias_annotations
            .get(&proof.annotation())
            .is_none_or(|(expected, recorded)| {
                expected == proof
                    && recorded
                        .as_ref()
                        .is_none_or(|recorded| recorded.snapshot() == resolution)
            })
    }

    pub(super) fn source_callable_alias_resolution(
        &self,
        annotation: NodeRef,
    ) -> Option<&SourceCallableAliasResolution> {
        self.observe_relation_node_read(annotation);
        self.source_callable_alias_annotations
            .get(&annotation)?
            .1
            .as_ref()
    }

    #[cfg(test)]
    pub(super) fn replace_source_callable_provenance_for_test(
        &mut self,
        type_: TypeId,
        replacement: Option<&SourceCallableProvenance>,
    ) -> Option<SourceCallableProvenance> {
        if self.source_callable_provenance.get(&type_) != replacement
            && let Some(provenance) = self.source_callable_provenance.get(&type_)
        {
            self.invalidate_inferred_return_cycles_for_node(provenance.declaration, None);
        }
        match replacement {
            Some(replacement) => self.source_callable_provenance.insert(type_, *replacement),
            None => self.source_callable_provenance.remove(&type_),
        }
    }

    #[cfg(test)]
    pub(super) fn replace_source_callable_type_for_declaration_for_test(
        &mut self,
        declaration: NodeRef,
        replacement: Option<TypeId>,
    ) -> Option<TypeId> {
        if self
            .source_callable_types_by_declaration
            .get(&declaration)
            .copied()
            != replacement
        {
            self.invalidate_inferred_return_cycles_for_node(declaration, None);
        }
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
        self.observe_relation_symbol_read(owner);
        self.source_callable_types_by_owner.get(&owner).copied()
    }

    pub(super) fn source_callable_type_for_signature(
        &self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        self.observe_relation_signature_read(signature);
        self.source_callable_types_by_signature
            .get(&signature)
            .copied()
    }

    pub(super) fn source_callable_type_for_declaration(
        &self,
        declaration: NodeRef,
    ) -> Option<TypeId> {
        self.observe_relation_node_read(declaration);
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

    #[must_use]
    pub(super) fn source_overload_provenance(
        &self,
        type_: TypeId,
    ) -> Option<&SourceOverloadProvenance> {
        self.observe_relation_type_read(type_);
        self.source_overload_provenance.get(&type_)
    }

    #[must_use]
    pub(super) fn source_overload_type_for_owner(&self, owner: SemanticSymbolId) -> Option<TypeId> {
        self.observe_relation_symbol_read(owner);
        self.source_overload_types_by_owner.get(&owner).copied()
    }

    #[must_use]
    pub(super) fn source_overload_type_for_declaration(
        &self,
        declaration: NodeRef,
    ) -> Option<TypeId> {
        self.observe_relation_node_read(declaration);
        self.source_overload_types_by_declaration
            .get(&declaration)
            .copied()
    }

    #[must_use]
    pub(super) fn source_overload_type_for_signature(
        &self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        self.observe_relation_signature_read(signature);
        self.source_overload_types_by_signature
            .get(&signature)
            .copied()
    }

    #[must_use]
    pub(super) fn source_overload_provenance_claims(
        &self,
        owner: SemanticSymbolId,
        declarations: &[NodeRef],
    ) -> bool {
        self.source_overload_provenance.values().any(|provenance| {
            provenance.owner_symbol == owner
                || provenance
                    .signatures
                    .iter()
                    .any(|signature| declarations.contains(&signature.declaration))
        })
    }

    pub(super) fn try_reserve_source_overload_provenance(
        &mut self,
        groups: usize,
        declarations: usize,
        signatures: usize,
    ) -> bool {
        self.source_overload_provenance.try_reserve(groups).is_ok()
            && self
                .source_overload_types_by_owner
                .try_reserve(groups)
                .is_ok()
            && self
                .source_overload_types_by_declaration
                .try_reserve(declarations)
                .is_ok()
            && self
                .source_overload_types_by_signature
                .try_reserve(signatures)
                .is_ok()
    }

    #[cfg(test)]
    pub(super) fn replace_source_overload_type_for_declaration_for_test(
        &mut self,
        declaration: NodeRef,
        replacement: Option<TypeId>,
    ) -> Option<TypeId> {
        match replacement {
            Some(type_) => self
                .source_overload_types_by_declaration
                .insert(declaration, type_),
            None => self
                .source_overload_types_by_declaration
                .remove(&declaration),
        }
    }

    fn has_callable_provenance(&self) -> bool {
        !self.function_type_provenance.is_empty()
            || !self.declared_call_set_provenance.is_empty()
            || !self.source_callable_provenance.is_empty()
            || !self.source_overload_provenance.is_empty()
            || !self.object_literal_getter_origins.is_empty()
            || self.signatures.iter().any(|(_, signature)| {
                signature.declaration().is_some_and(|node| {
                    self.node_is_declared_callable_signature(node)
                        || self.node_is_global_interface_method(node)
                        || self.node_is_interface_method(node)
                        || self.node_is_type_literal_method(node)
                })
            })
    }

    pub(super) fn mark_union_cache_validation_dirty(&mut self) {
        if self.intrinsic_bootstrap.is_some() {
            self.union_cache_needs_validation = true;
        }
    }

    pub(super) fn try_reserve_canonical_union_creations(&mut self, count: usize) -> bool {
        self.canonical_union_creations.try_reserve(count).is_ok()
    }

    pub(super) fn canonical_union_creation(
        &self,
        type_: TypeId,
    ) -> Option<&CanonicalUnionCreationProof> {
        self.canonical_union_creations.get(&type_)
    }

    pub(super) fn object_literal_property_clone_origin(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&ObjectLiteralPropertyCloneOrigin> {
        self.object_literal_property_clone_origins.get(&symbol)
    }

    pub(super) fn object_literal_getter_origin(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&ObjectLiteralGetterOrigin> {
        self.observe_relation_symbol_read(symbol);
        self.object_literal_getter_origins.get(&symbol)
    }

    pub(super) fn object_literal_getter_origin_for_type(
        &self,
        type_: TypeId,
    ) -> Option<&ObjectLiteralGetterOrigin> {
        self.object_literal_getter_origins
            .values()
            .find(|origin| origin.object_type() == type_)
    }

    pub(super) fn try_reserve_object_literal_getter_origins(&mut self, count: usize) -> bool {
        self.object_literal_getter_origins
            .try_reserve(count)
            .is_ok()
    }

    pub(super) fn record_object_literal_getter_origin(
        &mut self,
        origin: ObjectLiteralGetterOrigin,
    ) -> bool {
        if self.source_node_kind(origin.object()) != Some(SyntaxKind::ObjectLiteralExpression)
            || self.source_node_kind(origin.declaration()) != Some(SyntaxKind::GetAccessor)
            || self.source_declaration_symbol(origin.declaration()) != Some(origin.symbol())
            || self.type_payload(origin.object_type()).is_none()
        {
            return false;
        }
        match self.object_literal_getter_origins.entry(origin.symbol()) {
            std::collections::hash_map::Entry::Occupied(existing) => existing.get() == &origin,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(origin);
                true
            }
        }
    }

    pub(super) fn object_literal_getter_return_proof(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&ObjectLiteralGetterReturnProof> {
        self.observe_relation_symbol_read(symbol);
        self.object_literal_getter_return_proofs.get(&symbol)
    }

    pub(super) fn try_reserve_object_literal_getter_return_proofs(&mut self, count: usize) -> bool {
        self.object_literal_getter_return_proofs
            .try_reserve(count)
            .is_ok()
    }

    pub(super) fn record_object_literal_getter_return_proof(
        &mut self,
        proof: ObjectLiteralGetterReturnProof,
    ) -> bool {
        if !self
            .object_literal_getter_origins
            .contains_key(&proof.symbol())
            || self.signature(proof.signature()).is_none()
        {
            return false;
        }
        match self
            .object_literal_getter_return_proofs
            .entry(proof.symbol())
        {
            std::collections::hash_map::Entry::Occupied(existing) => existing.get() == &proof,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(proof);
                self.mark_union_cache_validation_dirty();
                true
            }
        }
    }

    pub(super) fn try_reserve_object_literal_property_clone_origins(
        &mut self,
        additional: usize,
    ) -> bool {
        self.object_literal_property_clone_origins
            .try_reserve(additional)
            .is_ok()
    }

    pub(super) fn record_object_literal_property_clone_origin(
        &mut self,
        origin: ObjectLiteralPropertyCloneOrigin,
    ) -> bool {
        if origin.symbol() == origin.source()
            || self.symbol(origin.symbol()).is_none()
            || self.symbol(origin.source()).is_none()
            || self.source_node_kind(origin.owner()) != Some(SyntaxKind::ObjectLiteralExpression)
        {
            return false;
        }
        match self
            .object_literal_property_clone_origins
            .entry(origin.symbol())
        {
            std::collections::hash_map::Entry::Occupied(existing) => existing.get() == &origin,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(origin);
                true
            }
        }
    }

    pub(super) fn module_value_identity(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&ModuleValueIdentity> {
        self.module_value_identities.get(&symbol)
    }

    pub(super) fn source_file_namespace_identity(
        &self,
        module: SemanticSymbolId,
    ) -> Option<&SourceFileNamespaceIdentity> {
        self.source_file_namespace_identities.get(&module)
    }

    pub(super) fn source_file_namespace_identity_for_type(
        &self,
        type_: TypeId,
    ) -> Option<&SourceFileNamespaceIdentity> {
        self.source_file_namespace_identities
            .values()
            .find(|identity| identity.type_() == type_)
    }

    pub(super) fn try_reserve_source_file_namespace_identities(&mut self, count: usize) -> bool {
        self.source_file_namespace_identities
            .try_reserve(count)
            .is_ok()
    }

    pub(super) fn source_file_namespace_wrapper(
        &self,
        alias: SemanticSymbolId,
    ) -> Option<&SourceFileNamespaceWrapper> {
        self.source_file_namespace_wrappers.get(&alias)
    }

    pub(super) fn import_meta_global(&self) -> Option<&ResolvedGlobalType> {
        self.import_meta_global.as_ref()
    }

    pub(super) fn set_import_meta_global(&mut self, value: ResolvedGlobalType) -> bool {
        if !value.is_for("ImportMeta", 0) || self.type_payload(value.type_()).is_none() {
            return false;
        }
        if let Some(existing) = &self.import_meta_global {
            return existing == &value;
        }
        self.import_meta_global = Some(value);
        true
    }

    pub(super) fn import_meta_expression(&self) -> Option<ImportMetaExpressionIdentity> {
        self.import_meta_expression
    }

    pub(super) fn set_import_meta_expression(
        &mut self,
        value: ImportMetaExpressionIdentity,
    ) -> bool {
        if let Some(existing) = self.import_meta_expression {
            return existing == value;
        }
        if self.type_payload(value.type_).is_none()
            || self.type_payload(value.import_meta_type).is_none()
            || self.symbol(value.symbol).is_none()
            || self.symbol(value.meta).is_none()
            || self.symbol_table(value.members).is_none()
            || self.import_meta_global().map(ResolvedGlobalType::type_)
                != Some(value.import_meta_type)
        {
            return false;
        }
        self.import_meta_expression = Some(value);
        true
    }

    pub(super) fn source_file_namespace_wrapper_for_module(
        &self,
        module: SemanticSymbolId,
    ) -> Option<&SourceFileNamespaceWrapper> {
        let alias = self.source_file_namespace_wrapper_aliases.get(&module)?;
        self.source_file_namespace_wrappers.get(alias)
    }

    pub(super) fn source_file_namespace_wrapper_default(
        &self,
        module: SemanticSymbolId,
    ) -> Option<SemanticSymbolId> {
        self.source_file_namespace_wrapper_defaults
            .get(&module)
            .copied()
    }

    pub(super) fn try_reserve_source_file_namespace_wrappers(&mut self, count: usize) -> bool {
        self.source_file_namespace_wrappers
            .try_reserve(count)
            .is_ok()
            && self
                .source_file_namespace_wrapper_aliases
                .try_reserve(count)
                .is_ok()
            && self
                .source_file_namespace_wrapper_defaults
                .try_reserve(count)
                .is_ok()
    }

    pub(super) fn record_source_file_namespace_wrapper(
        &mut self,
        wrapper: SourceFileNamespaceWrapper,
    ) -> bool {
        if let Some(existing) = self
            .source_file_namespace_wrappers
            .get(&wrapper.source.alias)
        {
            return existing == &wrapper;
        }
        if self
            .source_file_namespace_wrapper_aliases
            .contains_key(&wrapper.namespace)
            || self
                .source_file_namespace_wrapper_defaults
                .get(&wrapper.source.module)
                .is_some_and(|default| *default != wrapper.default)
            || [
                wrapper.source.alias,
                wrapper.source.module,
                wrapper.namespace,
                wrapper.default,
            ]
            .iter()
            .any(|symbol| self.symbol(*symbol).is_none())
        {
            return false;
        }
        self.source_file_namespace_wrapper_aliases
            .insert(wrapper.namespace, wrapper.source.alias);
        self.source_file_namespace_wrapper_defaults
            .insert(wrapper.source.module, wrapper.default);
        self.source_file_namespace_wrappers
            .insert(wrapper.source.alias, wrapper);
        true
    }

    pub(super) fn record_source_file_namespace_identity(
        &mut self,
        identity: SourceFileNamespaceIdentity,
    ) -> bool {
        if self.symbol(identity.module()).is_none() || self.type_payload(identity.type_()).is_none()
        {
            return false;
        }
        match self
            .source_file_namespace_identities
            .entry(identity.module())
        {
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                if !entry.get().accepts_completion(&identity) {
                    return false;
                }
                if entry.get() != &identity {
                    entry.insert(identity);
                }
                true
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(identity);
                true
            }
        }
    }

    pub(super) fn try_reserve_module_value_identities(&mut self, additional: usize) -> bool {
        self.module_value_identities.try_reserve(additional).is_ok()
    }

    pub(super) fn record_module_value_identity(&mut self, identity: ModuleValueIdentity) -> bool {
        if self.symbol(identity.symbol()).is_none() || self.type_payload(identity.type_()).is_none()
        {
            return false;
        }
        match self.module_value_identities.entry(identity.symbol()) {
            std::collections::hash_map::Entry::Occupied(existing) => existing.get() == &identity,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(identity);
                true
            }
        }
    }

    pub(super) fn record_canonical_union_creation(
        &mut self,
        proof: CanonicalUnionCreationProof,
    ) -> bool {
        if self.type_payload(proof.type_id()).is_none() {
            return false;
        }
        match self.canonical_union_creations.entry(proof.type_id()) {
            std::collections::hash_map::Entry::Occupied(existing) => existing.get() == &proof,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(proof);
                true
            }
        }
    }

    pub(super) fn try_reserve_union_alias_instantiations(
        &mut self,
        symbol: SemanticSymbolId,
        count: usize,
    ) -> bool {
        if self.union_alias_instantiations.try_reserve(1).is_err() {
            return false;
        }
        self.union_alias_instantiations
            .entry(symbol)
            .or_default()
            .try_reserve(count)
            .is_ok()
    }

    pub(super) fn union_alias_instantiation(
        &self,
        symbol: SemanticSymbolId,
        key: CacheHashKey,
    ) -> Option<&UnionAliasInstantiationProof> {
        self.union_alias_instantiations
            .get(&symbol)
            .and_then(|entries| entries.get(&key))
    }

    pub(super) fn union_alias_instantiation_count(&self, symbol: SemanticSymbolId) -> usize {
        self.union_alias_instantiations
            .get(&symbol)
            .map_or(0, HashMap::len)
    }

    pub(super) fn record_union_alias_instantiation(
        &mut self,
        proof: UnionAliasInstantiationProof,
    ) -> bool {
        if self.symbol(proof.cache_key().0).is_none()
            || proof
                .types()
                .iter()
                .any(|type_| self.type_payload(*type_).is_none())
        {
            return false;
        }
        let (symbol, key) = proof.cache_key();
        let Some(entries) = self.union_alias_instantiations.get_mut(&symbol) else {
            return false;
        };
        match entries.entry(key) {
            std::collections::hash_map::Entry::Occupied(existing) => existing.get() == &proof,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(proof);
                true
            }
        }
    }

    fn node_is_function_type(&self, node: NodeRef) -> bool {
        self.source_node_kind(node) == Some(SyntaxKind::FunctionType)
    }

    fn node_is_declared_callable_signature(&self, node: NodeRef) -> bool {
        matches!(
            self.source_node_kind(node),
            Some(
                SyntaxKind::CallSignature
                    | SyntaxKind::ConstructSignature
                    | SyntaxKind::ConstructorType
            )
        )
    }

    /// Returns the binder symbol retained when a computed method was published.
    pub(super) fn late_bound_method_source(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<SemanticSymbolId> {
        let source = self.links.late_bound.find_key(|source| {
            self.links
                .late_bound
                .try_get(source)
                .and_then(|links| links.late_symbol)
                == Some(symbol)
        })?;
        self.links
            .late_bound
            .find_key(|candidate| {
                candidate != source
                    && self
                        .links
                        .late_bound
                        .try_get(candidate)
                        .and_then(|links| links.late_symbol)
                        == Some(symbol)
            })
            .is_none()
            .then_some(*source)
    }

    /// Returns every original symbol of a published computed method group.
    /// The retained record owns names only. Signature result records stay separate.
    pub(super) fn late_bound_method_sources(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<Vec<SemanticSymbolId>> {
        let method = self.symbol(symbol)?;
        let flags = method.flags().without(SymbolFlags::TRANSIENT);
        if !method
            .flags()
            .contains(SymbolFlags::METHOD | SymbolFlags::TRANSIENT)
            || flags.without(SymbolFlags::METHOD | SymbolFlags::OPTIONAL) != SymbolFlags::NONE
            || method.check_flags() != CheckFlags::LATE
            || !method.name().is_late_bound()
            || self.get_merged_symbol(symbol) != Some(symbol)
        {
            return None;
        }
        let Some(group) = self.computed_method_name_groups.get(&symbol) else {
            return self
                .late_bound_method_source(symbol)
                .map(|source| vec![source]);
        };
        let declarations = method.declarations()?;
        let key = self.symbol(group.key_symbol)?;
        let key_id = self
            .symbol_store()
            .assigned_global_symbol_id(group.key_symbol)?;
        let suffix = method
            .name()
            .as_bytes()
            .strip_prefix(b"\xFE@")?
            .strip_prefix(key.name().as_bytes())?
            .strip_prefix(b"@")?;
        if group.sources.len() < 2
            || declarations.len() != group.sources.len()
            || self.get_parent_of_symbol(symbol) != Some(group.owner)
            || method.value_declaration() != declarations.first().copied()
            || method.members().is_some()
            || method.exports().is_some()
            || method.export_symbol().is_some()
            || self.types.get(group.key_type).is_none()
            || self.value_symbol_links(symbol)?.name_type != Some(group.key_type)
            || self.get_merged_symbol(group.key_symbol) != Some(group.key_symbol)
            || suffix != key_id.to_string().as_bytes()
            || self.value_symbol_links(group.key_symbol)?.resolved_type != Some(group.key_type)
            || !self.source_merged_symbol_declarations_match(group.owner)
        {
            return None;
        }
        let mut seen = HashSet::with_capacity(group.sources.len());
        let mut previous_position = None;
        for (&source, &declaration) in group.sources.iter().zip(declarations) {
            let early = self.symbol(source)?;
            let original = self.source_symbol_declarations.get(&source)?;
            let SourceNodeParent::Parent(owner_declaration) =
                self.source_node_parent(declaration)?
            else {
                return None;
            };
            let position = (
                self.source_file_rank(declaration.file)?,
                self.source_node_start(declaration)?,
            );
            let name =
                self.source_child_with_kind(declaration, SyntaxKind::ComputedPropertyName)?;
            let ((Some(expression), None) | (None, Some(expression))) = (
                self.source_child_with_kind(name, SyntaxKind::Identifier),
                self.source_child_with_kind(name, SyntaxKind::PropertyAccessExpression),
            ) else {
                return None;
            };
            if !seen.insert(source)
                || self.source_declaration_symbol(declaration) != Some(source)
                || !self.source_symbol_declarations_match(source)
                || original.flags != flags
                || early.flags() != flags
                || early.check_flags() != CheckFlags::NONE
                || early.name() != InternalSymbolName::Computed.as_ref()
                || early.declarations() != Some(&[declaration])
                || early.value_declaration() != Some(declaration)
                || early.members().is_some()
                || early.exports().is_some()
                || early.export_symbol().is_some()
                || self.get_parent_of_symbol(source) != Some(group.owner)
                || self.get_merged_symbol(source) != Some(source)
                || self
                    .value_symbol_links(source)
                    .is_some_and(|links| links != &ValueSymbolLinks::default())
                || self.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature)
                || !self.source_declaration_belongs_to_symbol(owner_declaration, group.owner)
                || previous_position.is_some_and(|previous| previous >= position)
                || self.late_bound_links(source)?.late_symbol != Some(symbol)
                || self.symbol_node_links(declaration)?.resolved_symbol != Some(symbol)
                || self.symbol_node_links(expression)?.resolved_symbol != Some(group.key_symbol)
                || self.type_node_links(expression)?.resolved_type != Some(group.key_type)
            {
                return None;
            }
            previous_position = Some(position);
        }
        if self
            .links
            .late_bound
            .find_key(|source| {
                !seen.contains(source)
                    && self
                        .links
                        .late_bound
                        .try_get(source)
                        .and_then(|links| links.late_symbol)
                        == Some(symbol)
            })
            .is_some()
        {
            return None;
        }
        Some(group.sources.to_vec())
    }

    pub(super) fn has_computed_method_name_origin(&self, source: SemanticSymbolId) -> bool {
        self.computed_method_name_groups
            .values()
            .any(|group| group.sources.contains(&source))
    }

    /// Checks the method's optional flag against each source declaration.
    pub(super) fn declared_method_optional_flag(&self, symbol: SemanticSymbolId) -> Option<bool> {
        let method = self.symbol(symbol)?;
        let sources = if method.flags().contains(SymbolFlags::TRANSIENT)
            || method.check_flags().contains(CheckFlags::LATE)
            || method.name().is_late_bound()
        {
            self.late_bound_method_sources(symbol)?
        } else {
            vec![symbol]
        };
        let flags = method.flags().without(SymbolFlags::TRANSIENT);
        if flags.without(SymbolFlags::OPTIONAL) != SymbolFlags::METHOD {
            return None;
        }
        let declarations = method.declarations()?;
        let mut source_declarations = Vec::new();
        for source in sources {
            let source_method = self.symbol(source)?;
            let original = source_method.declarations()?;
            if source_method.flags() != flags
                || source_method.value_declaration() != original.first().copied()
                || source_method.check_flags() != CheckFlags::NONE
            {
                return None;
            }
            source_declarations.extend_from_slice(original);
        }
        if source_declarations != declarations
            || method.value_declaration() != declarations.first().copied()
        {
            return None;
        }
        let optional = flags.contains(SymbolFlags::OPTIONAL);
        if declarations.is_empty()
            || declarations.iter().any(|declaration| {
                self.source_node_kind(*declaration) != Some(SyntaxKind::MethodSignature)
                    || self
                        .source_direct_children(*declaration)
                        .is_none_or(|children| {
                            children
                                .into_iter()
                                .filter(|&child| {
                                    self.source_node_kind(child) == Some(SyntaxKind::QuestionToken)
                                })
                                .count()
                                != usize::from(optional)
                        })
            })
        {
            return None;
        }
        Some(optional)
    }

    pub(super) fn late_bound_method_has_exact_sources(
        &self,
        symbol: SemanticSymbolId,
        owner: SemanticSymbolId,
    ) -> bool {
        let Some(method) = self.symbol(symbol) else {
            return false;
        };
        let Some(declarations) = method.declarations() else {
            return false;
        };
        let Some(sources) = self.late_bound_method_sources(symbol) else {
            return false;
        };
        let mut original_declarations = Vec::new();
        for source in sources {
            let Some(early) = self.symbol(source) else {
                return false;
            };
            let Some(original) = early.declarations() else {
                return false;
            };
            if early.flags() != method.flags().without(SymbolFlags::TRANSIENT)
                || early.check_flags() != CheckFlags::NONE
                || early.name() != InternalSymbolName::Computed.as_ref()
                || early.value_declaration() != original.first().copied()
                || self.get_parent_of_symbol(source) != Some(owner)
                || self.get_merged_symbol(source) != Some(source)
                || early.members().is_some()
                || early.exports().is_some()
                || early.export_symbol().is_some()
            {
                return false;
            }
            original_declarations.extend_from_slice(original);
        }
        original_declarations == declarations
            && method.value_declaration() == declarations.first().copied()
            && declarations.iter().all(|declaration| {
                self.symbol_node_links(*declaration)
                    .and_then(|links| links.resolved_symbol)
                    == Some(symbol)
            })
            && self
                .value_symbol_links(symbol)
                .and_then(|links| links.name_type)
                .is_some_and(|type_| self.types.get(type_).is_some())
    }

    /// Authenticates a declared or late-bound method against its interface owner.
    pub(super) fn authenticated_interface_method_owner(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<(SemanticSymbolId, TypeId)> {
        let method = self.symbol(symbol)?;
        let declarations = method.declarations()?;
        let owner = method
            .parent()
            .and_then(|parent| self.get_merged_symbol(parent))?;
        let interface = self.symbol(owner)?;
        let owner_declarations = interface.declarations()?;
        let interface_type = self.declared_type_links(owner)?.declared_type?;
        let late = method.check_flags().contains(CheckFlags::LATE)
            || method.flags().contains(SymbolFlags::TRANSIENT)
            || method.name().is_late_bound();
        let valid_late = !late || self.late_bound_method_has_exact_sources(symbol, owner);
        let members = if late {
            self.members_and_exports_links(owner).and_then(|links| {
                links.table(super::links::MembersOrExportsResolutionKind::ResolvedMembers)
            })
        } else {
            interface.members()
        };
        let merged_namespace = interface.flags().contains(SymbolFlags::NAMESPACE_MODULE);
        let allowed_owner_flags = SymbolFlags::INTERFACE
            | SymbolFlags::FUNCTION_SCOPED_VARIABLE
            | SymbolFlags::NAMESPACE_MODULE
            | SymbolFlags::TRANSIENT;
        let valid_namespace_owner = !merged_namespace
            || interface.flags().without(
                SymbolFlags::INTERFACE | SymbolFlags::NAMESPACE_MODULE | SymbolFlags::TRANSIENT,
            ) == SymbolFlags::NONE
                && interface.value_declaration().is_none()
                && interface.parent().is_none()
                && interface
                    .exports()
                    .and_then(|exports| self.symbol_table(exports))
                    .is_some_and(|exports| {
                        exports.iter().all(|(_, export)| {
                            self.symbol(export).is_some_and(|record| {
                                record
                                    .flags()
                                    .intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
                                    && !record.flags().intersects(SymbolFlags::VALUE)
                                    && self.get_parent_of_symbol(export) == Some(owner)
                                    && self.get_merged_symbol(export) == Some(export)
                            })
                        })
                    })
                && owner_declarations.iter().any(|declaration| {
                    self.source_node_kind(*declaration) == Some(SyntaxKind::ModuleDeclaration)
                });
        if declarations.is_empty()
            || !method.flags().contains(SymbolFlags::METHOD)
            || method.flags().without(
                SymbolFlags::METHOD
                    | SymbolFlags::OPTIONAL
                    | if late {
                        SymbolFlags::TRANSIENT
                    } else {
                        SymbolFlags::NONE
                    },
            ) != SymbolFlags::NONE
            || self.declared_method_optional_flag(symbol).is_none()
            || method.check_flags()
                != if late {
                    CheckFlags::LATE
                } else {
                    CheckFlags::NONE
                }
            || method.name().is_reserved_member_name()
            || method.name().is_private_identifier()
            || late && (!valid_late || !method.name().is_late_bound())
            || late && !method.flags().contains(SymbolFlags::TRANSIENT)
            || method.value_declaration() != declarations.first().copied()
            || method.members().is_some()
            || method.exports().is_some()
            || method.export_symbol().is_some()
            || self.get_merged_symbol(symbol) != Some(symbol)
            || interface.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
            || interface.flags().without(allowed_owner_flags) != SymbolFlags::NONE
            || !valid_namespace_owner
            || interface.check_flags() != CheckFlags::NONE
            || self.get_merged_symbol(owner) != Some(owner)
            || self.types.get(interface_type).is_none()
            || members
                .and_then(|members| self.symbol_table(members))
                .and_then(|members| members.get(method.name()))
                .and_then(|member| self.get_merged_symbol(member))
                != Some(symbol)
            || declarations.iter().enumerate().any(|(index, declaration)| {
                declarations[..index].contains(declaration)
                    || self.source_node_kind(*declaration) != Some(SyntaxKind::MethodSignature)
                    || self
                        .source_child_with_kind(*declaration, SyntaxKind::QuestionToken)
                        .is_some()
                        != method.flags().contains(SymbolFlags::OPTIONAL)
                    || !matches!(
                        self.source_node_parent(*declaration),
                        Some(SourceNodeParent::Parent(owner_declaration))
                            if owner_declarations.contains(&owner_declaration)
                                && self.source_node_kind(owner_declaration)
                                    == Some(SyntaxKind::InterfaceDeclaration)
                    )
            })
        {
            return None;
        }

        Some((owner, interface_type))
    }

    /// Authenticates a binder-owned method against its exact type-literal owner.
    pub(super) fn authenticated_type_literal_method_owner(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<(SemanticSymbolId, TypeId)> {
        let method = self.symbol(symbol)?;
        let declarations = method.declarations()?;
        let owner = method
            .parent()
            .and_then(|parent| self.get_merged_symbol(parent))?;
        let literal = self.symbol(owner)?;
        let [owner_declaration] = literal.declarations()? else {
            return None;
        };
        let owner_declaration = *owner_declaration;
        let links = self.type_node_links(owner_declaration)?;
        let literal_type = links.resolved_type?;
        let late = method.check_flags().contains(CheckFlags::LATE)
            || method.flags().contains(SymbolFlags::TRANSIENT)
            || method.name().is_late_bound();
        let valid_late = !late || self.late_bound_method_has_exact_sources(symbol, owner);
        let members = if late {
            self.members_and_exports_links(owner).and_then(|links| {
                links.table(super::links::MembersOrExportsResolutionKind::ResolvedMembers)
            })
        } else {
            literal.members()
        };
        if declarations.is_empty()
            || self.declared_method_optional_flag(symbol).is_none()
            || method.check_flags()
                != if late {
                    CheckFlags::LATE
                } else {
                    CheckFlags::NONE
                }
            || method.name().is_reserved_member_name()
            || method.name().is_private_identifier()
            || late && (!valid_late || !method.name().is_late_bound())
            || late && !method.flags().contains(SymbolFlags::TRANSIENT)
            || method.value_declaration() != declarations.first().copied()
            || method.members().is_some()
            || method.exports().is_some()
            || method.export_symbol().is_some()
            || self.get_merged_symbol(symbol) != Some(symbol)
            || literal.flags() != SymbolFlags::TYPE_LITERAL
            || literal.check_flags() != CheckFlags::NONE
            || literal.name() != InternalSymbolName::Type.as_ref()
            || literal.value_declaration().is_some()
            || literal.parent().is_some()
            || literal.exports().is_some()
            || literal.export_symbol().is_some()
            || self.get_merged_symbol(owner) != Some(owner)
            || self.source_node_kind(owner_declaration) != Some(SyntaxKind::TypeLiteral)
            || links
                != &(TypeNodeLinks {
                    resolved_type: Some(literal_type),
                    ..TypeNodeLinks::default()
                })
            || self.types.get(literal_type).is_none()
            || members
                .and_then(|members| self.symbol_table(members))
                .and_then(|members| members.get(method.name()))
                .and_then(|member| self.get_merged_symbol(member))
                != Some(symbol)
            || declarations.iter().enumerate().any(|(index, declaration)| {
                declarations[..index].contains(declaration)
                    || self.source_node_kind(*declaration) != Some(SyntaxKind::MethodSignature)
                    || self.source_node_parent(*declaration)
                        != Some(SourceNodeParent::Parent(owner_declaration))
            })
        {
            return None;
        }

        Some((owner, literal_type))
    }

    fn interface_method_for_declaration(&self, declaration: NodeRef) -> Option<SemanticSymbolId> {
        if self.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature) {
            return None;
        }
        if let Some(method) = self
            .symbol_node_links(declaration)
            .and_then(|links| links.resolved_symbol)
            && self
                .symbol(method)
                .is_some_and(|record| record.check_flags().contains(CheckFlags::LATE))
        {
            return (self.symbol(method)?.declarations()?.contains(&declaration)
                && self.authenticated_interface_method_owner(method).is_some())
            .then_some(method);
        }
        let SourceNodeParent::Parent(owner_declaration) = self.source_node_parent(declaration)?
        else {
            return None;
        };
        let globals = self.symbol_table(self.intrinsic_bootstrap.as_ref()?.globals)?;
        for (_, global) in globals.iter() {
            let Some(owner) = self.get_merged_symbol(global) else {
                continue;
            };
            let Some(interface) = self.symbol(owner) else {
                continue;
            };
            if !interface.flags().contains(SymbolFlags::INTERFACE)
                || interface
                    .declarations()
                    .is_none_or(|declarations| !declarations.contains(&owner_declaration))
            {
                continue;
            }
            let Some(members) = interface
                .members()
                .and_then(|members| self.symbol_table(members))
            else {
                continue;
            };
            for (_, member) in members.iter() {
                let Some(method) = self.get_merged_symbol(member) else {
                    continue;
                };
                if self
                    .symbol(method)
                    .and_then(Symbol::declarations)
                    .is_some_and(|declarations| declarations.contains(&declaration))
                    && self
                        .authenticated_interface_method_owner(method)
                        .is_some_and(|(method_owner, _)| method_owner == owner)
                {
                    return Some(method);
                }
            }
        }

        if self.source_node_kind(owner_declaration) != Some(SyntaxKind::InterfaceDeclaration)
            || !matches!(
                self.source_node_parent(owner_declaration),
                Some(SourceNodeParent::Parent(block))
                    if self.source_node_kind(block) == Some(SyntaxKind::ModuleBlock)
            )
        {
            return None;
        }
        let owner = self
            .links
            .declared_type
            .find_key(|owner| {
                self.symbol(*owner).is_some_and(|interface| {
                    interface.flags().contains(SymbolFlags::INTERFACE)
                        && interface
                            .declarations()
                            .is_some_and(|declarations| declarations.contains(&owner_declaration))
                        && (interface.flags().contains(SymbolFlags::NAMESPACE_MODULE)
                            || self.get_parent_of_symbol(*owner).is_some_and(|namespace| {
                                self.symbol(namespace).is_some_and(|record| {
                                    record.flags().intersects(SymbolFlags::NAMESPACE)
                                        && record.check_flags() == CheckFlags::NONE
                                        && self.get_merged_symbol(namespace) == Some(namespace)
                                        && record
                                            .exports()
                                            .and_then(|exports| self.symbol_table(exports))
                                            .and_then(|exports| exports.get(interface.name()))
                                            .and_then(|export| self.get_merged_symbol(export))
                                            == Some(*owner)
                                })
                            }))
                })
            })
            .copied()?;
        let owner_type = self.declared_type_links(owner)?.declared_type?;
        let members = self
            .symbol(owner)
            .and_then(Symbol::members)
            .and_then(|members| self.symbol_table(members))?;
        members.iter().find_map(|(_, member)| {
            let method = self.get_merged_symbol(member)?;
            (self
                .symbol(method)
                .and_then(Symbol::declarations)
                .is_some_and(|declarations| declarations.contains(&declaration))
                && self.authenticated_interface_method_owner(method) == Some((owner, owner_type)))
            .then_some(method)
        })
    }

    fn node_is_interface_method(&self, node: NodeRef) -> bool {
        self.interface_method_for_declaration(node).is_some()
    }

    fn type_literal_method_for_declaration(
        &self,
        declaration: NodeRef,
    ) -> Option<SemanticSymbolId> {
        if self.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature) {
            return None;
        }
        let SourceNodeParent::Parent(owner_declaration) = self.source_node_parent(declaration)?
        else {
            return None;
        };
        if self.source_node_kind(owner_declaration) != Some(SyntaxKind::TypeLiteral) {
            return None;
        }
        self.type_node_links(owner_declaration)?.resolved_type?;
        self.links
            .value_symbol
            .find_key(|method| {
                self.symbol(*method)
                    .and_then(Symbol::declarations)
                    .is_some_and(|declarations| declarations.contains(&declaration))
                    && self
                        .authenticated_type_literal_method_owner(*method)
                        .is_some_and(|(owner, _)| {
                            self.symbol(owner).and_then(Symbol::declarations)
                                == Some(&[owner_declaration][..])
                        })
            })
            .copied()
    }

    fn node_is_type_literal_method(&self, node: NodeRef) -> bool {
        self.type_literal_method_for_declaration(node).is_some()
    }

    /// Validates every declaration and signature before exposing a method type.
    /// Immutable return and parameter caches may still be unpublished.
    pub(super) fn interface_method_linked_type(&self, requested: SignatureId) -> Option<TypeId> {
        let declaration = self.signature(requested)?.declaration()?;
        let method_symbol = self.interface_method_for_declaration(declaration)?;
        self.authenticated_interface_method_owner(method_symbol)?;
        self.declared_method_linked_type(requested, method_symbol)
    }

    pub(super) fn type_literal_method_linked_type(&self, requested: SignatureId) -> Option<TypeId> {
        let declaration = self.signature(requested)?.declaration()?;
        let method_symbol = self.type_literal_method_for_declaration(declaration)?;
        self.authenticated_type_literal_method_owner(method_symbol)?;
        self.declared_method_linked_type(requested, method_symbol)
    }

    fn valid_declared_method_type_parameters(
        &self,
        signature: &Signature,
        declaration: NodeRef,
    ) -> bool {
        if signature.type_parameters().is_empty() {
            return true;
        }

        let Some(mut declarations) = self.source_direct_children(declaration) else {
            return false;
        };
        declarations.retain(|parameter| {
            parameter.node < declaration.node
                && self.source_node_kind(*parameter) == Some(SyntaxKind::TypeParameter)
        });
        if declarations.len() != signature.type_parameters().len() {
            return false;
        }

        let mut seen = HashSet::with_capacity(signature.type_parameters().len());
        signature
            .type_parameters()
            .iter()
            .copied()
            .zip(declarations)
            .all(|(type_, expected_declaration)| {
                if self.types.get(type_).is_none() || !seen.insert(type_) {
                    return false;
                }
                let Some(symbol) = self
                    .links
                    .declared_type
                    .find_key(|symbol| {
                        self.links
                            .declared_type
                            .try_get(symbol)
                            .is_some_and(|links| links.declared_type == Some(type_))
                            && self
                                .symbol(*symbol)
                                .and_then(Symbol::declarations)
                                .is_some_and(|declarations| declarations == [expected_declaration])
                    })
                    .copied()
                else {
                    return false;
                };
                let Some(record) = self.symbol(symbol) else {
                    return false;
                };
                record.flags() == SymbolFlags::TYPE_PARAMETER
                    && record.check_flags() == CheckFlags::NONE
                    && record.value_declaration().is_none()
                    && record.members().is_none()
                    && record.exports().is_none()
                    && record.parent().is_none()
                    && record.export_symbol().is_none()
                    && self.get_merged_symbol(symbol) == Some(symbol)
            })
    }

    fn declared_method_linked_type(
        &self,
        requested: SignatureId,
        method_symbol: SemanticSymbolId,
    ) -> Option<TypeId> {
        let method = self.symbol(method_symbol)?;
        let declarations = method.declarations()?;
        let value_links = self.value_symbol_links(method_symbol)?;
        let type_ = value_links.resolved_type?;
        if value_links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                name_type: if method.check_flags().contains(CheckFlags::LATE) {
                    value_links.name_type
                } else {
                    None
                },
                ..ValueSymbolLinks::default()
            })
            || self.types.get(type_).is_none()
        {
            return None;
        }

        let mut requested_found = false;
        for method_declaration in declarations {
            let links = self.signature_links(*method_declaration)?;
            let signature_id = links.resolved_signature.signature()?;
            let signature = self.signature(signature_id)?;
            let return_type = signature.resolved_return_type()?;
            let return_annotation = self.source_direct_type_annotation(*method_declaration)?;
            let allowed_flags =
                SignatureFlags::HAS_REST_PARAMETER | SignatureFlags::HAS_LITERAL_TYPES;
            if links
                != &(SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature_id),
                    ..SignatureLinks::default()
                })
                || signature.declaration() != Some(*method_declaration)
                || signature.flags() & !allowed_flags != SignatureFlags::NONE
                || !self.valid_declared_method_type_parameters(signature, *method_declaration)
                || signature.this_parameter().is_some()
                || signature.resolved_min_argument_count() != -1
                || signature.resolved_type_predicate().is_some()
                || signature.target().is_some()
                || signature.mapper().is_some()
                || signature.isolated_signature_type().is_some()
                || signature.composite().is_some()
                || self.types.get(return_type).is_none()
                || !self.source_direct_type_annotation_is_exact(return_annotation, return_type)
                || self
                    .function_signature_return_annotations
                    .get(&signature_id)
                    .is_some_and(|annotation| *annotation != (return_annotation, false))
            {
                return None;
            }

            let mut parameter_declarations = self.source_direct_children(*method_declaration)?;
            parameter_declarations.retain(|parameter| {
                self.source_node_kind(*parameter) == Some(SyntaxKind::Parameter)
            });
            if parameter_declarations.len() != signature.parameters().len() {
                return None;
            }

            let mut minimum = 0usize;
            let mut has_rest = false;
            for (index, (parameter, expected_parameter)) in signature
                .parameters()
                .iter()
                .copied()
                .zip(parameter_declarations)
                .enumerate()
            {
                let parameter_symbol = self.symbol(parameter)?;
                let [parameter_declaration] = parameter_symbol.declarations()? else {
                    return None;
                };
                let parameter_declaration = *parameter_declaration;
                let parameter_links = self.value_symbol_links(parameter)?;
                let parameter_type = parameter_links.resolved_type?;
                let parameter_annotation =
                    self.source_direct_type_annotation(parameter_declaration)?;
                let parameter_children = self.source_direct_children(parameter_declaration)?;
                let optional = parameter_children
                    .iter()
                    .any(|child| self.source_node_kind(*child) == Some(SyntaxKind::QuestionToken));
                let bootstrap = self.intrinsic_bootstrap.as_ref()?;
                let annotation_matches = if optional && bootstrap.options.strict_null_checks {
                    let base = self
                        .type_node_links(parameter_annotation)
                        .and_then(|links| links.resolved_type)
                        .or_else(|| {
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
                            ]
                            .into_iter()
                            .find(|type_| {
                                self.source_direct_type_annotation_is_exact(
                                    parameter_annotation,
                                    *type_,
                                )
                            })
                        });
                    base.is_some_and(|base| {
                        self.source_direct_type_annotation_is_exact(parameter_annotation, base)
                            && bootstrap.cached_optional_parameter_type(base)
                                == Some(parameter_type)
                    })
                } else {
                    self.source_direct_type_annotation_is_exact(
                        parameter_annotation,
                        parameter_type,
                    )
                };
                if parameter_symbol.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    || parameter_symbol.check_flags() != CheckFlags::NONE
                    || parameter_symbol.value_declaration() != Some(parameter_declaration)
                    || parameter_symbol.members().is_some()
                    || parameter_symbol.exports().is_some()
                    || parameter_symbol.parent().is_some()
                    || parameter_symbol.export_symbol().is_some()
                    || self.get_merged_symbol(parameter) != Some(parameter)
                    || parameter_declaration != expected_parameter
                    || self.source_node_kind(parameter_declaration) != Some(SyntaxKind::Parameter)
                    || self.source_node_parent(parameter_declaration)
                        != Some(SourceNodeParent::Parent(*method_declaration))
                    || parameter_links
                        != &(ValueSymbolLinks {
                            resolved_type: Some(parameter_type),
                            ..ValueSymbolLinks::default()
                        })
                    || self.types.get(parameter_type).is_none()
                    || !annotation_matches
                {
                    return None;
                }

                let rest = parameter_children
                    .iter()
                    .any(|child| self.source_node_kind(*child) == Some(SyntaxKind::DotDotDotToken));
                if rest && (has_rest || index + 1 != signature.parameters().len()) {
                    return None;
                }
                has_rest |= rest;
                if !rest && !optional {
                    minimum = minimum.checked_add(1)?;
                }
            }

            if signature
                .flags()
                .contains(SignatureFlags::HAS_REST_PARAMETER)
                != has_rest
                || signature.min_argument_count() != i32::try_from(minimum).ok()?
                || self
                    .callable_signature_parameter_types
                    .get(&signature_id)
                    .is_some_and(|cached| {
                        cached.len() != signature.parameters().len()
                            || signature.parameters().iter().zip(cached).any(
                                |(parameter, expected)| {
                                    self.value_symbol_links(*parameter)
                                        .and_then(|links| links.resolved_type)
                                        != Some(*expected)
                                },
                            )
                    })
            {
                return None;
            }
            requested_found |= signature_id == requested;
        }

        requested_found.then_some(type_)
    }

    /// Authenticates one narrowly supported method on its canonical global interface.
    ///
    /// Merged global interfaces retain their original binder-owned member parents,
    /// so parent identity must be compared after the checker merge redirect.
    pub(super) fn authenticated_global_interface_method(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<(TypeId, NodeRef)> {
        let method = self.symbol(symbol)?;
        let global_name = match method.name().as_utf8()? {
            "toFixed" => "Number",
            "toLowerCase" => "String",
            _ => return None,
        };
        let [declaration] = method.declarations()? else {
            return None;
        };
        let declaration = *declaration;
        let SourceNodeParent::Parent(interface_declaration) =
            self.source_node_parent(declaration)?
        else {
            return None;
        };
        let bootstrap = self.intrinsic_bootstrap.as_ref()?;
        let global = self
            .symbol_table(bootstrap.globals)?
            .get_source(global_name)?;
        let owner = self.get_merged_symbol(global)?;
        let interface = self.symbol(owner)?;
        let wrapper = self.declared_type_links(owner)?.declared_type?;
        let members = interface.members()?;
        let allowed_owner_flags =
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
        if method.flags() != SymbolFlags::METHOD
            || method.check_flags() != CheckFlags::NONE
            || method.value_declaration() != Some(declaration)
            || method.members().is_some()
            || method.exports().is_some()
            || method.export_symbol().is_some()
            || self.get_merged_symbol(symbol) != Some(symbol)
            || method
                .parent()
                .and_then(|parent| self.get_merged_symbol(parent))
                != Some(owner)
            || interface.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
            || interface.flags().without(allowed_owner_flags) != SymbolFlags::NONE
            || interface.check_flags() != CheckFlags::NONE
            || interface.name().as_utf8() != Some(global_name)
            || interface.parent().is_some()
            || interface.exports().is_some()
            || interface.export_symbol().is_some()
            || interface
                .declarations()
                .is_none_or(|declarations| !declarations.contains(&interface_declaration))
            || self.source_node_kind(interface_declaration)
                != Some(SyntaxKind::InterfaceDeclaration)
            || self.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature)
            || self
                .symbol_table(members)?
                .get_source(method.name().as_utf8()?)
                != Some(symbol)
            || self.types.get(wrapper).is_none()
            || self
                .source_primitive_type_annotation(declaration)
                .is_none_or(|annotation| {
                    self.source_node_kind(annotation) != Some(SyntaxKind::StringKeyword)
                        || self.type_node_links(annotation).is_some_and(|links| {
                            links != &TypeNodeLinks::default()
                                && links
                                    != &TypeNodeLinks {
                                        resolved_type: Some(bootstrap.string_type),
                                        outer_type_parameters: None,
                                    }
                        })
                })
        {
            return None;
        }

        Some((wrapper, declaration))
    }

    fn global_interface_method_for_declaration(
        &self,
        declaration: NodeRef,
    ) -> Option<SemanticSymbolId> {
        if self.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature) {
            return None;
        }
        let bootstrap = self.intrinsic_bootstrap.as_ref()?;
        let globals = self.symbol_table(bootstrap.globals)?;
        for (global_name, method_name) in [("Number", "toFixed"), ("String", "toLowerCase")] {
            let Some(owner) = globals
                .get_source(global_name)
                .and_then(|owner| self.get_merged_symbol(owner))
            else {
                continue;
            };
            let Some(method) = self
                .symbol(owner)
                .and_then(Symbol::members)
                .and_then(|members| self.symbol_table(members))
                .and_then(|members| members.get_source(method_name))
            else {
                continue;
            };
            if self
                .authenticated_global_interface_method(method)
                .is_some_and(|(_, candidate)| candidate == declaration)
            {
                return Some(method);
            }
        }
        None
    }

    fn node_is_global_interface_method(&self, node: NodeRef) -> bool {
        self.global_interface_method_for_declaration(node).is_some()
    }

    fn global_interface_method_linked_type(&self, signature: SignatureId) -> Option<TypeId> {
        let signature_record = self.signature(signature)?;
        let declaration = signature_record.declaration()?;
        let method = self.global_interface_method_for_declaration(declaration)?;
        let method_record = self.symbol(method)?;
        let links = self.value_symbol_links(method)?;
        let type_ = links.resolved_type?;
        let bootstrap = self.intrinsic_bootstrap.as_ref()?;
        if links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
            || self.types.get(type_).is_none()
            || self.signature_links(declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
            || signature_record.flags() != SignatureFlags::NONE
            || !signature_record.type_parameters().is_empty()
            || signature_record.this_parameter().is_some()
            || signature_record.min_argument_count() != 0
            || signature_record.resolved_min_argument_count() != -1
            || signature_record.resolved_return_type() != Some(bootstrap.string_type)
            || signature_record.resolved_type_predicate().is_some()
            || signature_record.target().is_some()
            || signature_record.mapper().is_some()
            || signature_record.isolated_signature_type().is_some()
            || signature_record.composite().is_some()
        {
            return None;
        }

        match (
            method_record.name().as_utf8(),
            signature_record.parameters(),
        ) {
            (Some("toLowerCase"), []) => {}
            (Some("toFixed"), [parameter]) => {
                let parameter_record = self.symbol(*parameter)?;
                let [parameter_declaration] = parameter_record.declarations()? else {
                    return None;
                };
                let parameter_declaration = *parameter_declaration;
                let annotation = self.source_primitive_type_annotation(parameter_declaration)?;
                if parameter_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    || parameter_record.check_flags() != CheckFlags::NONE
                    || parameter_record.name().as_utf8() != Some("fractionDigits")
                    || parameter_record.value_declaration() != Some(parameter_declaration)
                    || parameter_record.members().is_some()
                    || parameter_record.exports().is_some()
                    || parameter_record.parent().is_some()
                    || parameter_record.export_symbol().is_some()
                    || self.get_merged_symbol(*parameter) != Some(*parameter)
                    || self.source_node_kind(parameter_declaration) != Some(SyntaxKind::Parameter)
                    || self.source_node_parent(parameter_declaration)
                        != Some(SourceNodeParent::Parent(declaration))
                    || self.source_node_kind(annotation) != Some(SyntaxKind::NumberKeyword)
                    || self.value_symbol_links(*parameter).is_some_and(|links| {
                        if links == &ValueSymbolLinks::default() {
                            return false;
                        }
                        let Some(type_) = links.resolved_type else {
                            return true;
                        };
                        links
                            != &ValueSymbolLinks {
                                resolved_type: Some(type_),
                                ..ValueSymbolLinks::default()
                            }
                            || !bootstrap.options.strict_null_checks
                                && type_ != bootstrap.number_type
                    })
                    || self.type_node_links(annotation).is_some_and(|links| {
                        links != &TypeNodeLinks::default()
                            && links
                                != &TypeNodeLinks {
                                    resolved_type: Some(bootstrap.number_type),
                                    outer_type_parameters: None,
                                }
                    })
                    || self
                        .source_node_facts
                        .get(&annotation.arena)
                        .and_then(|facts| facts.get(annotation.node.index().checked_sub(1)?))
                        .and_then(Option::as_ref)
                        .is_none_or(|facts| {
                            facts.kind != SyntaxKind::QuestionToken
                                || facts.parent != Some(parameter_declaration.node)
                        })
                {
                    return None;
                }
            }
            _ => return None,
        }

        if let Some(parameter_types) = self.callable_signature_parameter_types.get(&signature) {
            if parameter_types.len() != signature_record.parameters().len() {
                return None;
            }
            for (parameter, parameter_type) in signature_record
                .parameters()
                .iter()
                .copied()
                .zip(parameter_types)
            {
                if self.value_symbol_links(parameter)
                    != Some(&ValueSymbolLinks {
                        resolved_type: Some(*parameter_type),
                        ..ValueSymbolLinks::default()
                    })
                {
                    return None;
                }
            }
        }
        Some(type_)
    }

    fn node_is_object_literal_getter_declaration(&self, node: NodeRef) -> bool {
        self.source_declaration_symbol(node)
            .and_then(|symbol| self.object_literal_getter_origins.get(&symbol))
            .is_some_and(|origin| origin.declaration() == node)
    }

    fn node_is_source_callable_declaration(&self, node: NodeRef) -> bool {
        self.source_callable_type_for_declaration(node)
            .and_then(|type_| self.source_callable_provenance(type_))
            .is_some_and(|provenance| {
                provenance.declaration == node
                    && self
                        .source_node_kind(node)
                        .is_some_and(|kind| provenance.family.matches_syntax_kind(kind))
            })
    }

    fn node_is_source_overload_declaration(&self, node: NodeRef) -> bool {
        self.source_overload_type_for_declaration(node)
            .and_then(|type_| self.source_overload_provenance(type_))
            .is_some_and(|provenance| {
                provenance
                    .signatures
                    .iter()
                    .any(|signature| signature.declaration == node)
                    && self.source_node_kind(node) == Some(SyntaxKind::FunctionDeclaration)
            })
    }

    fn node_has_callable_ancestor(&self, mut node: NodeRef) -> bool {
        let mut visited = HashSet::new();
        loop {
            if !visited.insert(node) {
                return false;
            }
            if self.node_is_function_type(node)
                || self.node_is_object_literal_getter_declaration(node)
                || self.node_is_source_callable_declaration(node)
                || self.node_is_source_overload_declaration(node)
                || self.node_is_declared_callable_signature(node)
                || self.node_is_global_interface_method(node)
                || self.node_is_interface_method(node)
                || self.node_is_type_literal_method(node)
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
        if self
            .source_jsdoc_callbacks
            .values()
            .any(|identity| identity.has_parameter(symbol))
        {
            return true;
        }
        let Some([declaration]) = self.symbol(symbol).and_then(Symbol::declarations) else {
            return false;
        };
        self.source_node_kind(*declaration) == Some(SyntaxKind::Parameter)
            && matches!(
                self.source_node_parent(*declaration),
                Some(SourceNodeParent::Parent(parent))
                    if self.node_is_function_type(parent)
                        || self.node_is_source_callable_declaration(parent)
                        || self.node_is_source_overload_declaration(parent)
                        || self.node_is_declared_callable_signature(parent)
                        || self.node_is_global_interface_method(parent)
                        || self.node_is_interface_method(parent)
                        || self.node_is_type_literal_method(parent)
            )
    }

    fn symbol_is_source_callable_owner(&self, symbol: SemanticSymbolId) -> bool {
        self.source_callable_types_by_owner.contains_key(&symbol)
            || self.source_overload_types_by_owner.contains_key(&symbol)
            || self.authenticated_global_interface_method(symbol).is_some()
            || self.authenticated_interface_method_owner(symbol).is_some()
            || self
                .authenticated_type_literal_method_owner(symbol)
                .is_some()
    }

    fn signature_is_callable(&self, signature: SignatureId) -> bool {
        if self
            .object_literal_getter_return_proofs
            .values()
            .any(|proof| proof.signature() == signature)
        {
            return true;
        }
        if self
            .source_jsdoc_callback_type_for_signature(signature)
            .is_some()
        {
            return true;
        }
        self.signature(signature)
            .and_then(Signature::declaration)
            .is_some_and(|declaration| {
                self.node_is_function_type(declaration)
                    || self.source_node_kind(declaration) == Some(SyntaxKind::Parameter)
                        && self
                            .type_node_links(declaration)
                            .and_then(|links| links.resolved_type)
                            .is_some_and(|type_| self.type_has_function_type_provenance(type_))
                    || self.node_is_declared_callable_signature(declaration)
                    || self
                        .global_interface_method_linked_type(signature)
                        .is_some()
                    || self.interface_method_linked_type(signature).is_some()
                    || self.type_literal_method_linked_type(signature).is_some()
                    || self
                        .source_callable_type_for_signature(signature)
                        .and_then(|type_| self.source_callable_provenance(type_))
                        .is_some_and(|provenance| provenance.declaration == declaration)
                    || self
                        .source_overload_type_for_signature(signature)
                        .and_then(|type_| self.source_overload_provenance(type_))
                        .is_some_and(|provenance| {
                            provenance.signatures.iter().any(|row| {
                                row.declaration == declaration && row.signature == signature
                            })
                        })
            })
    }

    fn signature_owns_callable_type(&self, signature: SignatureId) -> bool {
        if let Some(type_) = self.source_jsdoc_callback_type_for_signature(signature) {
            return self.type_has_function_type_provenance(type_)
                && self
                    .signature(signature)
                    .is_some_and(|record| record.declaration().is_none())
                && self
                    .source_jsdoc_callback_identity(type_)
                    .is_some_and(|identity| {
                        self.source_node_kind(identity.owner)
                            == Some(SyntaxKind::VariableDeclaration)
                    });
        }
        let Some(declaration) = self.signature(signature).and_then(Signature::declaration) else {
            return false;
        };
        if self.signature_links(declaration).is_none_or(|links| {
            links.resolved_signature != ResolvedSignatureState::Resolved(signature)
        }) {
            return false;
        }
        let type_ = if self.node_is_function_type(declaration)
            || self.source_node_kind(declaration) == Some(SyntaxKind::Parameter)
        {
            self.type_node_links(declaration)
                .and_then(|links| links.resolved_type)
                .filter(|type_| self.type_has_function_type_provenance(*type_))
        } else if self.node_is_declared_callable_signature(declaration) {
            self.declared_call_set_types_by_signature
                .get(&signature)
                .copied()
                .filter(|type_| self.type_has_declared_call_set_provenance(*type_))
        } else if self.node_is_global_interface_method(declaration) {
            self.global_interface_method_linked_type(signature)
        } else if self.node_is_interface_method(declaration) {
            self.interface_method_linked_type(signature)
        } else if self.node_is_type_literal_method(declaration) {
            self.type_literal_method_linked_type(signature)
        } else {
            self.source_callable_type_for_signature(signature)
                .filter(|type_| {
                    self.source_callable_provenance(*type_)
                        .is_some_and(|provenance| {
                            provenance.declaration == declaration
                                && provenance.signature == signature
                        })
                })
                .or_else(|| {
                    self.source_overload_type_for_signature(signature)
                        .filter(|type_| {
                            self.source_overload_provenance(*type_)
                                .is_some_and(|provenance| {
                                    provenance.signatures.iter().any(|row| {
                                        row.declaration == declaration && row.signature == signature
                                    })
                                })
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
        self.observe_relation_symbol_read(id);
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
        self.observe_relation_symbol_read(symbol);
        let merged = self
            .symbols
            .contains_symbol(symbol)
            .then(|| self.merged_symbols.get(&symbol).copied().unwrap_or(symbol));
        if let Some(merged) = merged {
            self.observe_relation_symbol_read(merged);
        }
        merged
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
        if self.relation_observable_symbols.contains(&source) && previous != Some(target) {
            self.mark_relation_inputs_dirty();
        }
        if self.has_callable_provenance() {
            self.mark_union_cache_validation_dirty();
        }
        Ok(previous)
    }

    /// Returns a symbol's raw parent after exactly one merged redirect.
    #[must_use]
    pub fn get_parent_of_symbol(&self, symbol: SemanticSymbolId) -> Option<SemanticSymbolId> {
        let parent = self.symbol(symbol)?.parent()?;
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
        self.observe_relation_symbol_table_read(id);
        self.symbols.symbol_table(id)
    }

    pub fn insert_symbol(
        &mut self,
        table: SymbolTableId,
        name: EscapedName,
        symbol: SemanticSymbolId,
    ) -> Option<Option<SemanticSymbolId>> {
        let previous = self.symbols.insert_symbol(table, name, symbol)?;
        if let Some(previous) = previous.filter(|previous| *previous != symbol) {
            self.invalidate_inferred_return_cycles_for_symbol(previous, None);
        }
        if self.relation_observable_symbol_tables.contains(&table) && previous != Some(symbol) {
            self.mark_relation_inputs_dirty();
        }
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
        let changed = self.symbol(symbol).is_some_and(|current| {
            current.flags() != flags || current.check_flags() != check_flags
        });
        let relation_dirty = self.relation_observable_symbols.contains(&symbol) && changed;
        if !self.symbols.set_symbol_flags(symbol, flags, check_flags) {
            return false;
        }
        if changed {
            self.invalidate_inferred_return_cycles_for_symbol(symbol, None);
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if self.has_callable_provenance() {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub(super) fn set_source_property_readonly(
        &mut self,
        symbol: SemanticSymbolId,
        readonly: bool,
    ) -> bool {
        let changed = self.symbol(symbol).is_some_and(|current| {
            current.check_flags().contains(CheckFlags::READONLY) != readonly
        });
        let relation_dirty = self.relation_observable_symbols.contains(&symbol) && changed;
        if !self.symbols.set_source_property_readonly(symbol, readonly) {
            return false;
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if changed && self.has_callable_provenance() {
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
        let changed = self.symbol(symbol).is_some_and(|current| {
            current.declarations() != declarations.as_deref()
                || current.value_declaration() != value_declaration
        });
        let relation_dirty = self.relation_observable_symbols.contains(&symbol) && changed;
        if !self
            .symbols
            .set_symbol_declarations(symbol, declarations, value_declaration)
        {
            return false;
        }
        if changed {
            self.invalidate_inferred_return_cycles_for_symbol(symbol, None);
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
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
        let changed = self.symbol(symbol).is_some_and(|current| {
            current.members() != members
                || current.exports() != exports
                || current.parent() != parent
                || current.export_symbol() != export_symbol
        });
        let relation_dirty = self.relation_observable_symbols.contains(&symbol) && changed;
        if !self
            .symbols
            .set_symbol_relationships(symbol, members, exports, parent, export_symbol)
        {
            return false;
        }
        if changed {
            self.invalidate_inferred_return_cycles_for_symbol(symbol, None);
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if self.has_callable_provenance() {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    /// Reads already-allocated common node links without allocating on a miss.
    #[must_use]
    pub fn node_links(&self, node: NodeRef) -> Option<&NodeLinks> {
        self.observe_relation_node_read(node);
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
        let relation_dirty = self.relation_observable_nodes.contains(&node)
            && self
                .node_links(node)
                .is_none_or(|current| current != &links);
        self.links.node.replace_key(node, links);
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    #[must_use]
    pub fn symbol_node_links(&self, node: NodeRef) -> Option<&SymbolNodeLinks> {
        self.observe_relation_node_read(node);
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
        let (changed, published) = self
            .symbol_node_links(node)
            .map_or((true, false), |current| {
                (current != &links, current.resolved_symbol.is_some())
            });
        let changes_recovery = changed
            && (published || self.signature_return_provenance.values().any(|provenance| {
                matches!(provenance,
                    SignatureReturnProvenance::RecoveredInferred(cycle)
                        | SignatureReturnProvenance::InvalidatedRecovery(cycle)
                    if [cycle.declaration, cycle.body, cycle.query, cycle.query_name].contains(&node))
            }));
        let relation_dirty = self.relation_observable_nodes.contains(&node) && changed;
        self.links.symbol_node.replace_key(node, links);
        // A first capture-cache write records the binding that was already checked.
        if changes_recovery {
            self.invalidate_inferred_return_cycles_for_node(node, None);
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if changed
            && self
                .object_literal_getter_origins
                .values()
                .any(|origin| origin.return_expression() == node)
        {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub(super) fn try_reserve_symbol_node_links(&mut self, additional: usize) -> bool {
        self.links.symbol_node.try_reserve(additional)
    }

    #[must_use]
    pub fn type_node_links(&self, node: NodeRef) -> Option<&TypeNodeLinks> {
        self.observe_relation_node_read(node);
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
        let (changed, published) = self.type_node_links(node).map_or((true, false), |current| {
            (current != &links, current != &TypeNodeLinks::default())
        });
        let relation_dirty = self.relation_observable_nodes.contains(&node) && changed;
        let dirty = self.node_has_callable_ancestor(node) && published && changed;
        let published_type = links
            .outer_type_parameters
            .is_none()
            .then_some(links.resolved_type)
            .flatten();
        self.links.type_node.replace_key(node, links);
        if changed {
            self.invalidate_inferred_return_cycles_for_node(node, published_type);
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
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
        self.observe_relation_node_read(node);
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
        let (changed, published) = self.signature_links(node).map_or((true, false), |current| {
            (current != &links, current != &SignatureLinks::default())
        });
        let relation_dirty = self.relation_observable_nodes.contains(&node) && changed;
        let dirty = (self.node_is_function_type(node)
            || self.node_is_object_literal_getter_declaration(node)
            || self.node_is_source_callable_declaration(node)
            || self.node_is_source_overload_declaration(node)
            || self.node_is_declared_callable_signature(node)
            || self.node_is_global_interface_method(node)
            || self.node_is_interface_method(node)
            || self.node_is_type_literal_method(node))
            && published
            && changed;
        self.links.signature.replace_key(node, links);
        if changed {
            self.invalidate_inferred_return_cycles_for_node(node, None);
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if dirty {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub(super) fn try_reserve_signature_links(&mut self, additional: usize) -> bool {
        self.links.signature.try_reserve(additional)
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
        self.observe_relation_symbol_read(symbol);
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
        let (changed, published) = self
            .value_symbol_links(symbol)
            .map_or((true, false), |current| {
                (current != &links, current != &ValueSymbolLinks::default())
            });
        let relation_dirty = self.relation_observable_symbols.contains(&symbol) && changed;
        let dirty = (self.symbol_is_callable_parameter(symbol)
            || self.symbol_is_source_callable_owner(symbol)
            || self.object_literal_getter_origins.contains_key(&symbol))
            && published
            && changed;
        let published_type = links.resolved_type.filter(|type_| {
            links
                == (ValueSymbolLinks {
                    resolved_type: Some(*type_),
                    ..ValueSymbolLinks::default()
                })
        });
        self.links.value_symbol.replace_key(symbol, links);
        let mut recovery_invalidated = false;
        for recovery in self.instantiated_property_recoveries.values_mut() {
            recovery_invalidated |= recovery.invalidate_for_raw_write(symbol);
        }
        for recovery in self.published_interface_method_recoveries.values_mut() {
            recovery_invalidated |= recovery.invalidate_for_raw_write(symbol);
        }
        for recovery in self.instantiated_index_recoveries.values_mut() {
            recovery_invalidated |= recovery.invalidate_for_raw_write(symbol);
        }
        for recovery in self.mapped_property_recoveries.values_mut() {
            recovery_invalidated |= recovery.invalidate_for_raw_write(symbol);
        }
        for recovery in self.mapped_index_recoveries.values_mut() {
            recovery_invalidated |= recovery.invalidate_for_raw_write(symbol);
        }
        if let Some(type_) = published_type
            && let Some(identity) = self.module_value_identities.get_mut(&symbol)
            && identity.type_() == type_
        {
            identity.mark_published();
        }
        if changed {
            self.invalidate_inferred_return_cycles_for_symbol(symbol, published_type);
        }
        if relation_dirty || recovery_invalidated {
            self.mark_relation_inputs_dirty();
        }
        if dirty || recovery_invalidated {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub(super) fn instantiated_property_recovery(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&InstantiatedPropertyRecovery> {
        self.observe_relation_symbol_read(symbol);
        self.instantiated_property_recoveries.get(&symbol)
    }

    pub(super) fn instantiated_index_recovery(
        &self,
        index: IndexInfoId,
    ) -> Option<&InstantiatedIndexRecovery> {
        self.instantiated_index_recoveries.get(&index)
    }

    pub(super) fn property_object_alias_recovery(
        &self,
        type_: TypeId,
    ) -> Option<&PropertyObjectAliasRecovery> {
        self.observe_relation_type_read(type_);
        self.property_object_alias_recoveries.get(&type_)
    }

    pub(super) fn try_reserve_property_object_alias_recoveries(&mut self) -> bool {
        self.property_object_alias_recoveries.try_reserve(1).is_ok()
    }

    pub(super) fn inline_property_object_recovery(
        &self,
        type_: TypeId,
    ) -> Option<&InlinePropertyObjectRecovery> {
        self.observe_relation_type_read(type_);
        self.inline_property_object_recoveries.get(&type_)
    }

    pub(super) fn try_reserve_inline_property_object_recoveries(&mut self) -> bool {
        self.inline_property_object_recoveries
            .try_reserve(1)
            .is_ok()
    }

    pub(super) fn property_object_alias_request_recovery(
        &self,
        symbol: SemanticSymbolId,
        key: CacheHashKey,
    ) -> Option<&PropertyObjectAliasRequestRecovery> {
        self.observe_relation_symbol_read(symbol);
        self.property_object_alias_request_recoveries
            .get(&(symbol, key))
    }

    pub(super) fn try_reserve_property_object_alias_request_recoveries(&mut self) -> bool {
        self.property_object_alias_request_recoveries
            .try_reserve(1)
            .is_ok()
    }

    pub(super) fn ordinary_intersection_alias_request_recovery(
        &self,
        symbol: SemanticSymbolId,
        key: CacheHashKey,
    ) -> Option<&OrdinaryIntersectionAliasRequestRecovery> {
        self.observe_relation_symbol_read(symbol);
        self.ordinary_intersection_alias_request_recoveries
            .get(&(symbol, key))
    }

    pub(super) fn try_reserve_ordinary_intersection_alias_request_recoveries(&mut self) -> bool {
        self.ordinary_intersection_alias_request_recoveries
            .try_reserve(1)
            .is_ok()
    }

    pub(super) fn try_reserve_instantiated_index_recoveries(&mut self, additional: usize) -> bool {
        self.instantiated_index_recoveries
            .try_reserve(additional)
            .is_ok()
    }

    /// Only generic index evaluation can create this recovery evidence.
    pub(super) fn publish_instantiated_index_recovery(
        &mut self,
        recovery: InstantiatedIndexRecovery,
    ) -> bool {
        let index = recovery.index();
        if self.instantiated_index_recoveries.contains_key(&index)
            || !recovery.matches_published_info(self.index_info(index))
        {
            return false;
        }
        self.instantiated_index_recoveries.insert(index, recovery);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    pub(super) fn mapped_property_recovery(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&MappedPropertyRecovery> {
        self.observe_relation_symbol_read(symbol);
        self.mapped_property_recoveries.get(&symbol)
    }

    pub(super) fn try_reserve_mapped_property_recoveries(&mut self) -> bool {
        self.mapped_property_recoveries.try_reserve(1).is_ok()
    }

    /// Only mapped property evaluation can create this recovery evidence.
    pub(super) fn publish_mapped_property_recovery(
        &mut self,
        recovery: MappedPropertyRecovery,
    ) -> bool {
        let symbol = recovery.symbol();
        if self.mapped_property_recoveries.contains_key(&symbol)
            || !recovery.matches_published_links(self.value_symbol_links(symbol))
        {
            return false;
        }
        self.mapped_property_recoveries.insert(symbol, recovery);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    pub(super) fn mapped_index_recovery(&self, index: IndexInfoId) -> Option<&MappedIndexRecovery> {
        self.mapped_index_recoveries.get(&index)
    }

    pub(super) fn try_reserve_mapped_index_recoveries(&mut self, additional: usize) -> bool {
        self.mapped_index_recoveries.try_reserve(additional).is_ok()
    }

    /// Only mapped index evaluation can create this recovery evidence.
    pub(super) fn publish_mapped_index_recovery(&mut self, recovery: MappedIndexRecovery) -> bool {
        let index = recovery.index();
        if self.mapped_index_recoveries.contains_key(&index)
            || !recovery.matches_published_info(self.index_info(index))
        {
            return false;
        }
        self.mapped_index_recoveries.insert(index, recovery);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    pub(super) fn instantiated_property_method_recovery(
        &self,
        type_: TypeId,
    ) -> Option<&InstantiatedPropertyRecovery> {
        self.instantiated_property_recoveries
            .values()
            .find(|recovery| recovery.is_method_result(type_))
    }

    pub(super) fn try_reserve_instantiated_property_recoveries(&mut self) -> bool {
        self.instantiated_property_recoveries.try_reserve(1).is_ok()
    }

    /// Only the checked property producer can construct this evidence.
    pub(super) fn publish_instantiated_property_recovery(
        &mut self,
        recovery: InstantiatedPropertyRecovery,
    ) -> bool {
        let symbol = recovery.symbol();
        if self.instantiated_property_recoveries.contains_key(&symbol)
            || !recovery.matches_published_links(self.value_symbol_links(symbol))
        {
            return false;
        }
        self.instantiated_property_recoveries
            .insert(symbol, recovery);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    #[must_use]
    pub fn alias_symbol_links(&self, symbol: SemanticSymbolId) -> Option<&AliasSymbolLinks> {
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.alias_symbol.try_get(&symbol))
            .flatten()
    }

    pub(super) fn checkpoint_alias_symbol_links(
        &self,
    ) -> super::links::LinkStoreCheckpoint<SemanticSymbolId, AliasSymbolLinks> {
        self.links.alias_symbol.checkpoint()
    }

    pub(super) fn restore_alias_symbol_links(
        &mut self,
        checkpoint: super::links::LinkStoreCheckpoint<SemanticSymbolId, AliasSymbolLinks>,
    ) -> bool {
        self.links.alias_symbol.restore_checkpoint(checkpoint)
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
        self.observe_relation_symbol_read(symbol);
        self.symbols
            .contains_symbol(symbol)
            .then(|| self.links.type_alias.try_get(&symbol))
            .flatten()
    }

    /// Finds the authenticated cached alias that owns one source declaration.
    pub(super) fn cached_type_alias_symbol_for_declaration(
        &self,
        declaration: NodeRef,
    ) -> Option<SemanticSymbolId> {
        if !matches!(
            self.source_node_kind(declaration),
            Some(SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration)
        ) {
            return None;
        }
        self.links
            .type_alias
            .find_key(|symbol| {
                self.get_merged_symbol(*symbol) == Some(*symbol)
                    && self.symbol(*symbol).is_some_and(|alias| {
                        alias.flags() == SymbolFlags::TYPE_ALIAS
                            && alias.check_flags() == CheckFlags::NONE
                            && alias.declarations() == Some(&[declaration][..])
                    })
            })
            .copied()
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
        let previous = self
            .links
            .type_alias
            .try_get(&symbol)
            .and_then(|links| links.declared_type);
        let declared_type = links.declared_type;
        let relation_dirty = (self.relation_observable_symbols.contains(&symbol)
            && self
                .type_alias_links(symbol)
                .is_none_or(|current| current != &links))
            || (previous != declared_type
                && [previous, declared_type]
                    .into_iter()
                    .flatten()
                    .any(|type_| self.relation_type_is_observable(type_)));
        let dirty = self.type_alias_links(symbol).is_some_and(|current| {
            current != &TypeAliasLinks::default()
                && current != &links
                && [current.declared_type, links.declared_type]
                    .into_iter()
                    .flatten()
                    .any(|type_| self.function_type_provenance.contains(&type_))
        });
        self.links.type_alias.replace_key(symbol, links);
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
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
        self.observe_relation_type_read(type_);
        self.type_alias_declared_type_owners.get(&type_)
    }

    #[must_use]
    pub fn declared_type_links(&self, symbol: SemanticSymbolId) -> Option<&DeclaredTypeLinks> {
        self.observe_relation_symbol_read(symbol);
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
        let relation_dirty = self.relation_observable_symbols.contains(&symbol)
            && self
                .declared_type_links(symbol)
                .is_none_or(|current| current != &links);
        self.links.declared_type.replace_key(symbol, links);
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    pub(super) fn try_reserve_declared_type_links(&mut self, additional: usize) -> bool {
        self.links.declared_type.try_reserve(additional)
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
        self.observe_relation_symbol_read(symbol);
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
        let relation_dirty = self.relation_observable_symbols.contains(&symbol)
            && self
                .members_and_exports_links(symbol)
                .is_none_or(|current| current != &links);
        self.links.members_and_exports.replace_key(symbol, links);
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
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

    /// Makes every retained relation result logically stale after a semantic
    /// write that can change assignability. Physical entries stay untouched
    /// until the next successful relation publication so failed queries remain
    /// transactionally read-only.
    pub(super) fn mark_relation_inputs_dirty(&mut self) {
        if !self.relation_cache_is_current() || self.relations.snapshot().is_pristine() {
            return;
        }
        let Some(next) = self.relation_inputs_generation.checked_add(1) else {
            self.relations = RelationCaches::default();
            self.clear_relation_observations();
            self.relation_inputs_generation = 0;
            self.relation_cache_generation = 0;
            return;
        };
        self.relation_inputs_generation = next;
    }

    pub(super) fn relation_type_is_observable(&self, type_: TypeId) -> bool {
        self.relation_observable_types.contains(&type_)
    }

    #[inline]
    pub(super) fn relation_read_observation_is_active(&self) -> bool {
        self.relation_read_observation_active
            .load(Ordering::Relaxed)
    }

    pub(super) fn begin_relation_read_observation(&mut self) -> Option<RelationObservationToken> {
        let active = self
            .active_relation_read_observations
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if self
            .relation_read_observation_active
            .load(Ordering::Relaxed)
            || active.is_some()
        {
            return None;
        }
        self.next_relation_observation_token = self
            .next_relation_observation_token
            .checked_add(1)
            .unwrap_or(1);
        let token = RelationObservationToken(self.next_relation_observation_token);
        *active = Some(ActiveRelationReadObservations {
            token,
            observations: RelationReadObservations::default(),
        });
        self.relation_read_observation_active
            .store(true, Ordering::Release);
        Some(token)
    }

    pub(super) fn discard_relation_read_observation(
        &mut self,
        token: RelationObservationToken,
    ) -> bool {
        if !self
            .relation_read_observation_active
            .load(Ordering::Acquire)
        {
            return false;
        }
        let active = self
            .active_relation_read_observations
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if active.as_ref().is_none_or(|active| active.token != token) {
            return false;
        }
        *active = None;
        self.relation_read_observation_active
            .store(false, Ordering::Release);
        true
    }

    fn take_relation_read_observations(
        &mut self,
        token: RelationObservationToken,
    ) -> Option<RelationReadObservations> {
        if !self
            .relation_read_observation_active
            .load(Ordering::Acquire)
        {
            return None;
        }
        let active = self
            .active_relation_read_observations
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if active.as_ref().is_none_or(|active| active.token != token) {
            return None;
        }
        let observations = active.take()?.observations;
        self.relation_read_observation_active
            .store(false, Ordering::Release);
        Some(observations)
    }

    #[inline]
    fn with_relation_read_observations(&self, observe: impl FnOnce(&mut RelationReadObservations)) {
        if !self
            .relation_read_observation_active
            .load(Ordering::Relaxed)
        {
            return;
        }
        let mut active = self
            .active_relation_read_observations
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let Some(active) = active.as_mut() else {
            debug_assert!(false, "active relation observation lost its recorder");
            return;
        };
        observe(&mut active.observations);
    }

    #[inline]
    pub(super) fn observe_relation_type_read(&self, type_: TypeId) {
        self.with_relation_read_observations(|observed| {
            observed.types.insert(type_);
        });
    }

    #[inline]
    pub(super) fn observe_relation_type_alias_read(&self, alias: TypeAliasId) {
        self.with_relation_read_observations(|observed| {
            observed.type_aliases.insert(alias);
        });
    }

    #[inline]
    pub(super) fn observe_relation_signature_read(&self, signature: SignatureId) {
        self.with_relation_read_observations(|observed| {
            observed.signatures.insert(signature);
        });
    }

    #[inline]
    pub(super) fn observe_relation_symbol_read(&self, symbol: SemanticSymbolId) {
        self.with_relation_read_observations(|observed| {
            observed.symbols.insert(symbol);
        });
    }

    #[inline]
    pub(super) fn observe_relation_symbol_table_read(&self, table: SymbolTableId) {
        self.with_relation_read_observations(|observed| {
            observed.symbol_tables.insert(table);
        });
    }

    #[inline]
    pub(super) fn observe_relation_node_read(&self, node: NodeRef) {
        self.with_relation_read_observations(|observed| {
            observed.nodes.insert(node);
        });
    }

    #[inline]
    pub(super) fn observe_relation_object_instantiation_map_read(&self, type_: TypeId) {
        self.with_relation_read_observations(|observed| {
            observed.object_instantiation_maps.insert(type_);
        });
    }

    #[inline]
    pub(super) fn observe_relation_object_instantiation_read(
        &self,
        type_: TypeId,
        key: CacheHashKey,
    ) {
        self.with_relation_read_observations(|observed| {
            observed.object_instantiations.insert((type_, key));
        });
    }

    #[inline]
    pub(super) fn observe_relation_derived_cache_source_read(&self, type_: TypeId) {
        self.with_relation_read_observations(|observed| {
            observed.derived_cache_sources.insert(type_);
        });
    }

    #[inline]
    pub(super) fn observe_relation_derived_cache_target_read(&self, type_: TypeId) {
        self.with_relation_read_observations(|observed| {
            observed.derived_cache_targets.insert(type_);
        });
    }

    #[inline]
    fn observe_relation_enum_pair_read(&self, source: SemanticSymbolId, target: SemanticSymbolId) {
        self.with_relation_read_observations(|observed| {
            observed.enum_pairs.insert((source, target));
        });
    }

    pub(super) fn relation_type_alias_is_observable(&self, alias: TypeAliasId) -> bool {
        self.relation_observable_type_aliases.contains(&alias)
    }

    pub(super) fn relation_signature_is_observable(&self, signature: SignatureId) -> bool {
        self.relation_observable_signatures.contains(&signature)
    }

    pub(super) fn relation_object_instantiation_is_observable(
        &self,
        type_: TypeId,
        key: CacheHashKey,
    ) -> bool {
        self.relation_observable_object_instantiations
            .contains(&(type_, key))
    }

    pub(super) fn relation_object_instantiation_map_is_observable(&self, type_: TypeId) -> bool {
        self.relation_observable_object_instantiation_maps
            .contains(&type_)
    }

    pub(super) fn relation_derived_cache_source_is_observable(&self, type_: TypeId) -> bool {
        self.relation_observable_derived_cache_sources
            .contains(&type_)
    }

    pub(super) fn relation_derived_cache_target_is_observable(&self, type_: TypeId) -> bool {
        self.relation_observable_derived_cache_targets
            .contains(&type_)
    }

    pub(super) fn relation_observes_object_instantiation_change(
        &self,
        type_: TypeId,
        current: &TypeCacheState,
        candidate: &TypeCacheState,
    ) -> bool {
        if self.relation_object_instantiation_map_is_observable(type_) && current != candidate {
            return true;
        }
        let lookup = |state: &TypeCacheState, key: CacheHashKey| match state {
            TypeCacheState::Unallocated => None,
            TypeCacheState::Allocated(instantiations) => instantiations.get(&key).copied(),
        };
        self.relation_observable_object_instantiations
            .iter()
            .filter_map(|(owner, key)| (*owner == type_).then_some(*key))
            .any(|key| lookup(current, key) != lookup(candidate, key))
    }

    fn mark_relation_inputs_observable(&mut self, observed: RelationReadObservations) {
        self.relation_observable_types.extend(observed.types);
        self.relation_observable_type_aliases
            .extend(observed.type_aliases);
        self.relation_observable_signatures
            .extend(observed.signatures);
        self.relation_observable_symbols.extend(observed.symbols);
        self.relation_observable_symbol_tables
            .extend(observed.symbol_tables);
        self.relation_observable_object_instantiation_maps
            .extend(observed.object_instantiation_maps);
        self.relation_observable_object_instantiations
            .extend(observed.object_instantiations);
        self.relation_observable_nodes.extend(observed.nodes);
        self.relation_observable_derived_cache_sources
            .extend(observed.derived_cache_sources);
        self.relation_observable_derived_cache_targets
            .extend(observed.derived_cache_targets);
        self.relation_observable_enum_pairs
            .extend(observed.enum_pairs);
    }

    fn clear_relation_observations(&mut self) {
        self.relation_observable_types.clear();
        self.relation_observable_type_aliases.clear();
        self.relation_observable_signatures.clear();
        self.relation_observable_symbols.clear();
        self.relation_observable_symbol_tables.clear();
        self.relation_observable_object_instantiation_maps.clear();
        self.relation_observable_object_instantiations.clear();
        self.relation_observable_nodes.clear();
        self.relation_observable_derived_cache_sources.clear();
        self.relation_observable_derived_cache_targets.clear();
        self.relation_observable_enum_pairs.clear();
    }

    fn relation_cache_is_current(&self) -> bool {
        self.relation_cache_generation == self.relation_inputs_generation
    }

    fn prepare_relation_cache_write(&mut self) {
        if !self.relation_cache_is_current() {
            self.relations = RelationCaches::default();
            self.clear_relation_observations();
            self.relation_cache_generation = self.relation_inputs_generation;
        }
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
        if self.relation_cache_is_current() {
            self.relations.get(relation, key)
        } else {
            RelationComparisonResult::NONE
        }
    }

    /// Test-only raw `Relation.set` substrate. Production writes must use
    /// [`Self::commit_relation_cache_writes`] so every physical entry is
    /// published atomically with the semantic inputs that back it.
    #[cfg(test)]
    pub(crate) fn relation_cache_set(
        &mut self,
        relation: RelationKind,
        key: CacheHashKey,
        result: RelationComparisonResult,
    ) {
        self.prepare_relation_cache_write();
        self.relations.set(relation, key, result);
    }

    pub(super) fn commit_relation_cache_writes(
        &mut self,
        observation: RelationObservationToken,
        relation: RelationKind,
        writes: impl IntoIterator<Item = (CacheHashKey, RelationComparisonResult)>,
    ) -> bool {
        let mut writes = writes.into_iter().peekable();
        if writes.peek().is_none() {
            return false;
        }
        let Some(observed) = self.take_relation_read_observations(observation) else {
            return false;
        };
        self.prepare_relation_cache_write();
        for (key, result) in writes {
            self.relations.set(relation, key, result);
        }
        self.mark_relation_inputs_observable(observed);
        true
    }

    #[must_use]
    pub fn relation_cache_size(&self, relation: RelationKind) -> usize {
        if self.relation_cache_is_current() {
            self.relations.size(relation)
        } else {
            0
        }
    }

    /// Distinguishes upstream's nil result map from an allocated map.
    #[must_use]
    pub fn relation_cache_is_allocated(&self, relation: RelationKind) -> bool {
        self.relation_cache_is_current() && self.relations.is_allocated(relation)
    }

    /// Exact initial work budget used by `checkTypeRelatedToEx` for this cache.
    #[must_use]
    pub fn relation_comparison_budget(&self, relation: RelationKind) -> isize {
        if self.relation_cache_is_current() {
            self.relations.comparison_budget(relation)
        } else {
            RelationCaches::default().comparison_budget(relation)
        }
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
        self.observe_relation_enum_pair_read(source, target);
        Some(if self.relation_cache_is_current() {
            self.relations.enum_get(source_id, target_id)
        } else {
            RelationComparisonResult::NONE
        })
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
        let pair = (source, target);
        let relation_dirty = self.relation_cache_is_current()
            && self.relation_observable_enum_pairs.contains(&pair)
            && self.relations.enum_get(source_id, target_id) != result;
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        self.prepare_relation_cache_write();
        self.relations.enum_set(source_id, target_id, result);
        self.relation_observable_symbols.extend([source, target]);
        true
    }

    #[must_use]
    pub fn enum_relation_cache_size(&self) -> usize {
        if self.relation_cache_is_current() {
            self.relations.enum_size()
        } else {
            0
        }
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
        self.observe_relation_signature_read(id);
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

    pub(super) fn try_reserve_declared_value_provenance(&mut self, additional: usize) -> bool {
        self.declared_value_provenance
            .try_reserve(additional)
            .is_ok()
    }

    pub(super) fn declared_value_provenance(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<DeclaredValueProvenance> {
        self.declared_value_provenance.get(&symbol).copied()
    }

    pub(super) fn publish_declared_value_provenance(
        &mut self,
        symbol: SemanticSymbolId,
        provenance: DeclaredValueProvenance,
    ) -> bool {
        if self.symbol(symbol).is_none()
            || self.type_payload(provenance.type_).is_none()
            || !self.contains_node_ref(provenance.annotation)
            || self
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                != Some(provenance.type_)
            || !self.source_direct_type_annotation_is_exact(provenance.annotation, provenance.type_)
        {
            return false;
        }
        match self.declared_value_provenance.entry(symbol) {
            std::collections::hash_map::Entry::Occupied(entry) => *entry.get() == provenance,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(provenance);
                true
            }
        }
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
            || self.node_is_declared_callable_signature(declaration)
            || self.node_is_global_interface_method(declaration)
            || self.interface_method_linked_type(id).is_some()
            || self.type_literal_method_linked_type(id).is_some()
            || self
                .source_callable_type_for_signature(id)
                .and_then(|type_| self.source_callable_provenance(type_))
                .is_some_and(|provenance| provenance.declaration == declaration)
            || self
                .source_overload_type_for_signature(id)
                .and_then(|type_| self.source_overload_provenance(type_))
                .is_some_and(|provenance| {
                    provenance
                        .signatures
                        .iter()
                        .any(|row| row.declaration == declaration && row.signature == id)
                });
        let valid_interface_method_annotation = if self.node_is_global_interface_method(declaration)
        {
            self.source_primitive_type_annotation(declaration) == Some(annotation)
                && self.source_node_kind(annotation) == Some(SyntaxKind::StringKeyword)
                && !null_literal_identity
                && self.intrinsic_bootstrap.as_ref().is_some_and(|bootstrap| {
                    self.signature(id).and_then(Signature::resolved_return_type)
                        == Some(bootstrap.string_type)
                })
        } else if self.node_is_interface_method(declaration)
            || self.node_is_type_literal_method(declaration)
        {
            self.source_direct_type_annotation(declaration) == Some(annotation)
                && !null_literal_identity
                && self
                    .signature(id)
                    .and_then(Signature::resolved_return_type)
                    .is_some_and(|return_type| {
                        self.source_direct_type_annotation_is_exact(annotation, return_type)
                    })
        } else {
            true
        };
        if !valid_callable
            || !valid_interface_method_annotation
            || self.function_signature_return_annotations.contains_key(&id)
        {
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
        if self.relation_signature_is_observable(id) {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    pub(super) fn function_signature_return_annotation(
        &self,
        id: SignatureId,
    ) -> Option<(NodeRef, bool)> {
        self.observe_relation_signature_read(id);
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
                || self.signature(*signature).is_some_and(|record| {
                    record.declaration().is_some_and(|declaration| {
                        self.node_is_global_interface_method(declaration)
                            || self.node_is_interface_method(declaration)
                            || self.node_is_type_literal_method(declaration)
                    }) && record.parameters().iter().copied().zip(types).any(
                        |(parameter, type_)| {
                            self.value_symbol_links(parameter)
                                != Some(&ValueSymbolLinks {
                                    resolved_type: Some(*type_),
                                    ..ValueSymbolLinks::default()
                                })
                        },
                    )
                })
                || !self.valid_optional_types(Some(types))
        }) {
            return false;
        }
        let relation_dirty = parameter_types
            .iter()
            .any(|(signature, _)| self.relation_signature_is_observable(*signature));
        for (signature, types) in parameter_types {
            let previous = self
                .callable_signature_parameter_types
                .insert(signature, types);
            assert!(
                previous.is_none(),
                "callable parameter provenance was prevalidated absent"
            );
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    pub(super) fn callable_signature_parameter_types(
        &self,
        signature: SignatureId,
    ) -> Option<&[TypeId]> {
        self.observe_relation_signature_read(signature);
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
        let relation_dirty = self.relation_signature_is_observable(id)
            && self
                .signature(id)
                .is_some_and(|signature| signature.resolved_min_argument_count() != count);
        if !self.signatures.set_resolved_min_argument_count(id, count) {
            return false;
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
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
        let relation_observable = self.relation_signature_is_observable(id);
        let had_circular_provenance = self.signature_has_circular_return_type(id);
        let relation_dirty = relation_observable
            && (had_circular_provenance
                || self
                    .signature(id)
                    .is_some_and(|signature| signature.resolved_return_type() != type_id));
        if !self.signatures.set_resolved_return_type(id, type_id) {
            return false;
        }
        let cleared_circular_provenance = match self.signature_return_provenance.get(&id).copied() {
            Some(SignatureReturnProvenance::Annotation(_)) => {
                self.signature_return_provenance.remove(&id);
                true
            }
            Some(SignatureReturnProvenance::RecoveredInferred(cycle)) => {
                self.signature_return_provenance
                    .insert(id, SignatureReturnProvenance::InvalidatedRecovery(cycle));
                true
            }
            _ => false,
        };
        debug_assert_eq!(cleared_circular_provenance, had_circular_provenance);
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        if dirty || cleared_circular_provenance {
            self.mark_union_cache_validation_dirty();
        }
        true
    }

    pub(super) fn try_reserve_circular_return_signatures(&mut self, additional: usize) -> bool {
        self.signature_return_provenance
            .try_reserve(additional)
            .is_ok()
            && self
                .checked_source_callable_returns
                .try_reserve(additional)
                .is_ok()
    }

    pub(super) fn signature_has_circular_return_type(&self, id: SignatureId) -> bool {
        self.observe_relation_signature_read(id);
        matches!(
            self.signature_return_provenance.get(&id),
            Some(
                SignatureReturnProvenance::Annotation(_)
                    | SignatureReturnProvenance::RecoveredInferred(_)
            )
        )
    }

    pub(super) fn circular_return_annotation_type(&self, id: SignatureId) -> Option<TypeId> {
        self.observe_relation_signature_read(id);
        match self.signature_return_provenance.get(&id)? {
            SignatureReturnProvenance::Annotation(type_) => Some(*type_),
            _ => None,
        }
    }

    pub(super) fn inferred_source_return_cycle(
        &self,
        id: SignatureId,
    ) -> Option<SourceCallableInferredReturnCycle> {
        self.observe_relation_signature_read(id);
        match self.signature_return_provenance.get(&id)? {
            SignatureReturnProvenance::RecoveredInferred(cycle) => Some(*cycle),
            _ => None,
        }
    }

    /// Returns the checked identity, independently of mutable signature caches.
    pub(super) fn checked_source_callable_return_type(&self, id: SignatureId) -> Option<TypeId> {
        self.observe_relation_signature_read(id);
        self.checked_source_callable_returns.get(&id).copied()
    }

    pub(super) fn source_callable_return_was_recovered(&self, id: SignatureId) -> bool {
        self.observe_relation_signature_read(id);
        matches!(
            self.signature_return_provenance.get(&id),
            Some(
                SignatureReturnProvenance::RecoveredInferred(_)
                    | SignatureReturnProvenance::InvalidatedRecovery(_)
            )
        )
    }

    /// Publishes the checked return once. Raw cache writes cannot replace this identity.
    pub(super) fn set_source_callable_inferred_return_type(
        &mut self,
        id: SignatureId,
        type_: TypeId,
    ) -> bool {
        let provenance = self
            .source_callable_types_by_signature
            .get(&id)
            .and_then(|callable| self.source_callable_provenance.get(callable));
        if self.types.get(type_).is_none()
            || provenance.is_none_or(|provenance| {
                provenance.return_provenance != SourceCallableReturnProvenance::Inferred
            })
            || self.function_signature_return_annotations.contains_key(&id)
        {
            return false;
        }
        let Some(signature) = self.signatures.get(id) else {
            return false;
        };
        if self.signature_return_provenance.contains_key(&id) {
            return false;
        }
        if let Some(existing) = self.checked_source_callable_returns.get(&id) {
            return *existing == type_ && signature.resolved_return_type() == Some(type_);
        }
        if signature
            .resolved_return_type()
            .is_some_and(|existing| existing != type_)
            || self.checked_source_callable_returns.try_reserve(1).is_err()
        {
            return false;
        }
        self.checked_source_callable_returns.insert(id, type_);
        let published = self.signatures.set_resolved_return_type(id, Some(type_));
        debug_assert!(published, "the inferred return signature was validated");
        if self.relation_signature_is_observable(id) {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
        true
    }

    fn invalidate_inferred_return_cycles_for_node(
        &mut self,
        node: NodeRef,
        published_type: Option<TypeId>,
    ) {
        let signatures = self
            .signature_return_provenance
            .iter()
            .filter_map(|(signature, provenance)| {
                let (SignatureReturnProvenance::RecoveredInferred(cycle)
                | SignatureReturnProvenance::InvalidatedRecovery(cycle)) = provenance
                else {
                    return None;
                };
                if node == cycle.declaration && published_type == Some(cycle.callable) {
                    return None;
                }
                let mut current = Some(node);
                while let Some(candidate) = current {
                    if candidate == cycle.declaration {
                        return Some(*signature);
                    }
                    current = match self.source_node_parent(candidate) {
                        Some(SourceNodeParent::Parent(parent)) => Some(parent),
                        _ => None,
                    };
                }
                None
            })
            .collect::<Vec<_>>();
        self.invalidate_inferred_return_cycles(&signatures);
    }

    fn invalidate_inferred_return_cycles(&mut self, signatures: &[SignatureId]) {
        for signature in signatures {
            self.signature_return_provenance.remove(signature);
            self.checked_source_callable_returns.remove(signature);
            let cleared = self.signatures.set_resolved_return_type(*signature, None);
            debug_assert!(cleared, "a retained cycle owns its signature");
        }
        if !signatures.is_empty() {
            self.mark_relation_inputs_dirty();
            self.mark_union_cache_validation_dirty();
        }
    }

    fn invalidate_inferred_return_cycles_for_symbol(
        &mut self,
        symbol: SemanticSymbolId,
        published_type: Option<TypeId>,
    ) {
        let signatures = self
            .signature_return_provenance
            .iter()
            .filter_map(|(signature, provenance)| {
                let (SignatureReturnProvenance::RecoveredInferred(cycle)
                | SignatureReturnProvenance::InvalidatedRecovery(cycle)) = provenance
                else {
                    return None;
                };
                let owner = self
                    .source_callable_provenance
                    .get(&cycle.callable)
                    .map(|provenance| provenance.owner_symbol);
                ((cycle.variable == symbol || owner == Some(symbol))
                    && published_type != Some(cycle.callable))
                .then_some(*signature)
            })
            .collect::<Vec<_>>();
        self.invalidate_inferred_return_cycles(&signatures);
    }

    pub(super) fn set_source_callable_circular_inferred_return_type(
        &mut self,
        id: SignatureId,
        cycle: SourceCallableInferredReturnCycle,
    ) -> bool {
        let Some(any) = self
            .intrinsic_bootstrap
            .as_ref()
            .map(|bootstrap| bootstrap.any_type)
        else {
            return false;
        };
        let valid = self.signature_is_callable(id)
            && !self.function_signature_return_annotations.contains_key(&id)
            && self.types.get(cycle.body_type).is_some()
            && self
                .source_callable_provenance
                .get(&cycle.callable)
                .is_some_and(|provenance| {
                    provenance.signature == id
                        && provenance.declaration == cycle.declaration
                        && provenance.return_provenance == SourceCallableReturnProvenance::Inferred
                })
            && self
                .signature(id)
                .is_some_and(|signature| signature.resolved_return_type().is_none())
            && !self.signature_return_provenance.contains_key(&id)
            && !self.checked_source_callable_returns.contains_key(&id);
        if !valid {
            return false;
        }
        self.signature_return_provenance
            .insert(id, SignatureReturnProvenance::RecoveredInferred(cycle));
        self.checked_source_callable_returns.insert(id, any);
        let published = self.signatures.set_resolved_return_type(id, Some(any));
        debug_assert!(published, "the inferred source signature was validated");
        if self.relation_signature_is_observable(id) {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
        true
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
            && !self.signature_return_provenance.contains_key(&id);
        if !valid {
            return false;
        }
        let previous = self
            .signature_return_provenance
            .insert(id, SignatureReturnProvenance::Annotation(annotation_type));
        assert!(
            previous.is_none(),
            "the circular-return marker was checked absent"
        );
        let published = self.signatures.set_resolved_return_type(id, Some(type_id));
        assert!(published, "the local function signature was prevalidated");
        if self.relation_signature_is_observable(id) {
            self.mark_relation_inputs_dirty();
        }
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
        let relation_dirty = self.relation_signature_is_observable(id)
            && self
                .signature(id)
                .is_some_and(|signature| signature.resolved_type_predicate() != predicate);
        if !self.signatures.set_resolved_type_predicate(id, predicate) {
            return false;
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
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
        let relation_dirty = self.relation_signature_is_observable(id)
            && self
                .signature(id)
                .is_some_and(|signature| signature.isolated_signature_type() != type_id);
        if !self.signatures.set_isolated_signature_type(id, type_id) {
            return false;
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
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
        let relation_dirty = self.relation_signature_is_observable(id)
            && self.signature(id).is_some_and(|signature| {
                signature.target() != target || signature.mapper() != mapper
            });
        if !self.signatures.set_target_and_mapper(id, target, mapper) {
            return false;
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
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
        let relation_dirty = self.relation_signature_is_observable(id)
            && self
                .signature(id)
                .is_some_and(|signature| signature.composite() != composite.as_ref());
        if !self.signatures.set_composite(id, composite) {
            return false;
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
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
        let relation_dirty = self.relation_signature_is_observable(id)
            && self
                .signature(id)
                .is_some_and(|signature| signature.flags() != flags);
        if !self.signatures.set_flags(id, flags) {
            return false;
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
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
        let relation_dirty = self.relation_signature_is_observable(id)
            && self
                .signature(id)
                .is_some_and(|signature| signature.type_parameters() != type_parameters.as_slice());
        if !self.signatures.set_type_parameters(id, type_parameters) {
            return false;
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
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
        let relation_dirty = self.relation_signature_is_observable(id)
            && self
                .signature(id)
                .is_some_and(|signature| signature.this_parameter() != this_parameter);
        if !self.signatures.set_this_parameter(id, this_parameter) {
            return false;
        }
        if relation_dirty {
            self.mark_relation_inputs_dirty();
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
        let relation_dirty = self
            .index_info(id)
            .is_some_and(|index| index.index_symbol().is_some() && index.index_symbol() != symbol);
        if !self.index_infos.set_index_symbol(id, symbol) {
            return false;
        }
        let mut recovery_invalidated = self
            .mapped_index_recoveries
            .get_mut(&id)
            .is_some_and(MappedIndexRecovery::invalidate_for_index_write);
        for recovery in self.instantiated_index_recoveries.values_mut() {
            recovery_invalidated |= recovery.invalidate_for_index_write(id);
        }
        if relation_dirty || recovery_invalidated {
            self.mark_relation_inputs_dirty();
        }
        if recovery_invalidated {
            self.mark_union_cache_validation_dirty();
        }
        true
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

    /// Ordinary arrow parameters are inside the arrow, unlike reparsed `JSDoc` parameters.
    pub(super) fn source_arrow_has_ordinary_type_parameters(&self, node: NodeRef) -> bool {
        self.source_node_fact(node)
            .is_some_and(|facts| facts.ordinary_arrow_type_parameters)
    }

    /// Returns the registered source offset used to order declarations.
    #[must_use]
    pub(super) fn source_node_start(&self, node: NodeRef) -> Option<u32> {
        self.source_node_fact(node).map(|facts| facts.start)
    }

    /// Returns identifier text from the registered source, not checker caches.
    #[must_use]
    pub(super) fn source_identifier_text(&self, node: NodeRef) -> Option<&str> {
        let facts = self.source_node_fact(node)?;
        if facts.kind != SyntaxKind::Identifier {
            return None;
        }
        facts.identifier_text.as_deref()
    }

    pub(super) fn source_type_operator(&self, node: NodeRef) -> Option<SyntaxKind> {
        self.source_node_fact(node)?.type_operator
    }

    /// Returns exact source roles, not mutable heritage or type-query caches.
    pub(super) fn source_plain_interface_heritage(
        &self,
        node: NodeRef,
    ) -> Option<&PlainInterfaceHeritageFacts> {
        self.source_node_fact(node)?
            .plain_interface_heritage
            .as_deref()
    }

    pub(super) fn source_mapped_type_modifiers(
        &self,
        node: NodeRef,
    ) -> Option<MappedTypeModifiers> {
        self.source_node_fact(node)?
            .mapped_type
            .as_deref()?
            .modifiers
    }

    /// Mapped parameters are allocated after their template, so adjacency is not a role proof.
    pub(super) fn source_mapped_type_operands(
        &self,
        node: NodeRef,
    ) -> Option<SourceMappedTypeOperands> {
        let syntax = self.source_node_fact(node)?.mapped_type.as_deref()?;
        let reference = |child| NodeRef::new(node.arena, node.file, child);
        let operands = SourceMappedTypeOperands {
            type_parameter: reference(syntax.type_parameter),
            constraint: reference(syntax.constraint?),
            name_type: syntax.name_type.map(reference),
            template: syntax.template.map(reference),
        };
        let is_type = |child| {
            self.source_node_kind(child).is_some_and(|kind| {
                kind.is_keyword_type()
                    || (SyntaxKind::FIRST_TYPE_NODE as u16..=SyntaxKind::LAST_TYPE_NODE as u16)
                        .contains(&(kind as u16))
            })
        };
        (self.source_node_kind(operands.type_parameter) == Some(SyntaxKind::TypeParameter)
            && self.source_node_parent(operands.type_parameter)
                == Some(SourceNodeParent::Parent(node))
            && self.source_node_parent(operands.constraint)
                == Some(SourceNodeParent::Parent(operands.type_parameter))
            && is_type(operands.constraint)
            && operands
                .name_type
                .into_iter()
                .chain(operands.template)
                .all(|child| {
                    self.source_node_parent(child) == Some(SourceNodeParent::Parent(node))
                        && is_type(child)
                }))
        .then_some(operands)
    }

    /// Returns registered children in ascending node-ID order.
    pub(super) fn source_direct_children(&self, parent: NodeRef) -> Option<Vec<NodeRef>> {
        self.source_node_fact(parent)?;
        Some(
            self.source_node_children
                .get(&parent.arena)?
                .get(parent.node.index())?
                .iter()
                .map(|&node| NodeRef::new(parent.arena, parent.file, node))
                .collect(),
        )
    }

    /// Returns the registered name of an exact named default-function declaration.
    pub(super) fn source_default_function_name(&self, declaration: NodeRef) -> Option<NodeRef> {
        let name = self.source_node_fact(declaration)?.default_function_name?;
        Some(NodeRef::new(declaration.arena, declaration.file, name))
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

    /// Returns one direct source child of the requested kind, if it is unique.
    pub(super) fn source_child_with_kind(
        &self,
        parent: NodeRef,
        kind: SyntaxKind,
    ) -> Option<NodeRef> {
        let mut children = self
            .source_direct_children(parent)?
            .into_iter()
            .filter(|&child| self.source_node_kind(child) == Some(kind));
        let child = children.next()?;
        children.next().is_none().then_some(child)
    }

    /// Proves when computed members can leave the binder's member table absent.
    pub(super) fn source_symbol_has_only_computed_members(&self, owner: SemanticSymbolId) -> bool {
        let Some(declarations) = self.symbol(owner).and_then(Symbol::declarations) else {
            return false;
        };
        let mut saw_member = false;
        for declaration in declarations {
            let Some(facts) = self.source_node_facts.get(&declaration.arena) else {
                return false;
            };
            if !matches!(
                self.source_node_kind(*declaration),
                Some(SyntaxKind::InterfaceDeclaration | SyntaxKind::TypeLiteral)
            ) {
                return false;
            }
            for (index, facts) in facts.iter().enumerate() {
                let Some(facts) = facts
                    .as_ref()
                    .filter(|facts| facts.parent == Some(declaration.node))
                else {
                    continue;
                };
                match facts.kind {
                    SyntaxKind::MethodSignature
                    | SyntaxKind::PropertyDeclaration
                    | SyntaxKind::PropertySignature => {
                        let Ok(index) = u32::try_from(index) else {
                            return false;
                        };
                        let member =
                            NodeRef::new(declaration.arena, declaration.file, NodeId::new(index));
                        if !self.source_member_has_dynamic_name(member) {
                            return false;
                        }
                        saw_member = true;
                    }
                    SyntaxKind::TypeParameter
                    | SyntaxKind::CallSignature
                    | SyntaxKind::ConstructSignature
                    | SyntaxKind::IndexSignature => return false,
                    _ => {}
                }
            }
        }
        saw_member
    }

    pub(super) fn source_computed_member_count(&self, owner: SemanticSymbolId) -> Option<usize> {
        let declarations = self.symbol(owner)?.declarations()?;
        let mut count = 0usize;
        for declaration in declarations {
            if !matches!(
                self.source_node_kind(*declaration),
                Some(SyntaxKind::InterfaceDeclaration | SyntaxKind::TypeLiteral)
            ) {
                continue;
            }
            let nodes = self.source_node_facts.get(&declaration.arena)?;
            let owns_name = |name: NodeId| {
                nodes
                    .get(name.index())
                    .and_then(Option::as_ref)
                    .filter(|facts| facts.kind == SyntaxKind::ComputedPropertyName)
                    .and_then(|facts| nodes.get(facts.parent?.index()).and_then(Option::as_ref))
                    .is_some_and(|member| {
                        member.parent == Some(declaration.node)
                            && matches!(
                                member.kind,
                                SyntaxKind::MethodSignature
                                    | SyntaxKind::PropertyDeclaration
                                    | SyntaxKind::PropertySignature
                                    | SyntaxKind::GetAccessor
                                    | SyntaxKind::SetAccessor
                            )
                    })
            };
            let mut names = 0usize;
            let mut static_names = HashSet::new();
            for (index, facts) in nodes.iter().enumerate() {
                let Some(facts) = facts else {
                    continue;
                };
                let node = NodeId::new(u32::try_from(index).ok()?);
                if facts.kind == SyntaxKind::ComputedPropertyName && owns_name(node) {
                    names = names.checked_add(1)?;
                }
                if matches!(
                    facts.kind,
                    SyntaxKind::StringLiteral
                        | SyntaxKind::NumericLiteral
                        | SyntaxKind::NoSubstitutionTemplateLiteral
                ) && let Some(parent) = facts.parent
                {
                    if owns_name(parent) {
                        static_names.insert(parent);
                    } else if facts.kind == SyntaxKind::NumericLiteral
                        && let Some(unary) = nodes.get(parent.index()).and_then(Option::as_ref)
                        && unary.kind == SyntaxKind::PrefixUnaryExpression
                        && unary.prefix_unary_operator == Some(SyntaxKind::MinusToken)
                        && let Some(name) = unary.parent.filter(|name| owns_name(*name))
                    {
                        static_names.insert(name);
                    }
                }
            }
            count = count.checked_add(names.checked_sub(static_names.len())?)?;
        }
        Some(count)
    }

    fn source_member_has_dynamic_name(&self, member: NodeRef) -> bool {
        let Some(name) = self.source_child_with_kind(member, SyntaxKind::ComputedPropertyName)
        else {
            return false;
        };
        self.source_computed_name_is_dynamic(name)
    }

    fn source_computed_name_is_dynamic(&self, name: NodeRef) -> bool {
        if [
            SyntaxKind::StringLiteral,
            SyntaxKind::NumericLiteral,
            SyntaxKind::NoSubstitutionTemplateLiteral,
        ]
        .into_iter()
        .any(|kind| self.source_child_with_kind(name, kind).is_some())
        {
            return false;
        }
        !self
            .source_child_with_kind(name, SyntaxKind::PrefixUnaryExpression)
            .is_some_and(|unary| {
                self.source_node_fact(unary).is_some_and(|facts| {
                    facts.prefix_unary_operator == Some(SyntaxKind::MinusToken)
                }) && self
                    .source_child_with_kind(unary, SyntaxKind::NumericLiteral)
                    .is_some()
            })
    }

    pub(super) fn source_alias_type_parameter_annotations(
        &self,
        declaration: NodeRef,
    ) -> Option<SourceAliasTypeParameterAnnotations> {
        let facts = self.source_node_fact(declaration)?;
        let parent = NodeRef::new(declaration.arena, declaration.file, facts.parent?);
        if facts.kind != SyntaxKind::TypeParameter
            || self.source_node_kind(parent) != Some(SyntaxKind::TypeAliasDeclaration)
        {
            return None;
        }
        let annotations = facts.alias_type_parameter.as_deref()?;
        let child = |node| {
            let node = NodeRef::new(declaration.arena, declaration.file, node);
            (self.source_node_parent(node) == Some(SourceNodeParent::Parent(declaration)))
                .then_some(node)
        };
        Some(SourceAliasTypeParameterAnnotations {
            constraint: match annotations.constraint {
                Some(node) => Some(child(node)?),
                None => None,
            },
            default_type: match annotations.default_type {
                Some(node) => Some(child(node)?),
                None => None,
            },
        })
    }

    /// Returns the final direct type annotation on a registered declaration.
    #[must_use]
    pub(super) fn source_direct_type_annotation(&self, declaration: NodeRef) -> Option<NodeRef> {
        if !self.contains_node_ref(declaration) {
            return None;
        }
        let annotation = declaration.node.index().checked_sub(1)?;
        let fact = self
            .source_node_facts
            .get(&declaration.arena)
            .and_then(|facts| facts.get(annotation))
            .and_then(Option::as_ref)?;
        let is_type = fact.kind.is_keyword_type()
            || (SyntaxKind::FIRST_TYPE_NODE as u16..=SyntaxKind::LAST_TYPE_NODE as u16)
                .contains(&(fact.kind as u16));
        if fact.parent != Some(declaration.node) || !is_type {
            return None;
        }
        let node = NodeId::new(u32::try_from(annotation).ok()?);
        Some(NodeRef::new(declaration.arena, declaration.file, node))
    }

    /// Primitive annotations and null literals may resolve without node links.
    /// Other composite annotations must retain their exact published identity.
    pub(super) fn source_direct_type_annotation_is_exact(
        &self,
        annotation: NodeRef,
        type_: TypeId,
    ) -> bool {
        let Some(bootstrap) = self.intrinsic_bootstrap.as_ref() else {
            return false;
        };
        let intrinsic = match self.source_node_kind(annotation) {
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
            Some(SyntaxKind::LiteralType)
                if annotation
                    .node
                    .index()
                    .checked_sub(1)
                    .and_then(|index| u32::try_from(index).ok())
                    .map(|index| {
                        NodeRef::new(annotation.arena, annotation.file, NodeId::new(index))
                    })
                    .is_some_and(|literal| {
                        self.source_node_kind(literal) == Some(SyntaxKind::NullKeyword)
                            && self.source_node_parent(literal)
                                == Some(SourceNodeParent::Parent(annotation))
                    }) =>
            {
                Some(bootstrap.null_type)
            }
            Some(SyntaxKind::NeverKeyword) => Some(bootstrap.never_type),
            Some(SyntaxKind::ObjectKeyword) => Some(bootstrap.non_primitive_type),
            Some(SyntaxKind::IntrinsicKeyword) => Some(bootstrap.intrinsic_marker_type),
            _ => None,
        };
        let exact_links = TypeNodeLinks {
            resolved_type: Some(type_),
            outer_type_parameters: None,
        };
        match intrinsic {
            Some(intrinsic) => {
                type_ == intrinsic
                    && self.type_node_links(annotation).is_none_or(|links| {
                        links == &TypeNodeLinks::default() || links == &exact_links
                    })
                    && self
                        .symbol_node_links(annotation)
                        .is_none_or(|links| links == &SymbolNodeLinks::default())
            }
            None => self.type_node_links(annotation) == Some(&exact_links),
        }
    }

    /// Returns the sole direct primitive annotation on a registered declaration.
    #[must_use]
    pub(super) fn source_primitive_type_annotation(&self, declaration: NodeRef) -> Option<NodeRef> {
        self.source_direct_type_annotation(declaration)
            .filter(|annotation| {
                self.source_node_kind(*annotation)
                    .is_some_and(SyntaxKind::is_keyword_type)
            })
    }

    #[must_use]
    pub(super) fn source_node_is_exported(&self, node: NodeRef) -> Option<bool> {
        self.source_node_fact(node).map(|facts| facts.exported)
    }

    fn source_node_fact(&self, node: NodeRef) -> Option<&SourceNodeFacts> {
        if !self.contains_node_ref(node) {
            return None;
        }
        self.source_node_facts
            .get(&node.arena)
            .and_then(|facts| facts.get(node.node.index()))
            .and_then(Option::as_ref)
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
                ordinary_arrow_type_parameters: matches!(
                    &node.data,
                    NodeData::ArrowFunction(function)
                        if function.type_parameters.as_ref().is_some_and(|parameters| {
                            !parameters.nodes.is_empty()
                                && parameters.range.start >= node.range.start
                        })
                ),
                parent: node.parent,
                start: node.range.start.get(),
                identifier_text: match &node.data {
                    NodeData::Identifier(identifier) if node.kind == SyntaxKind::Identifier => {
                        Some(identifier.text.clone().into_boxed_str())
                    }
                    _ => None,
                },
                default_function_name: Self::named_default_function_name(arena, node_id, node),
                prefix_unary_operator: match &node.data {
                    NodeData::PrefixUnaryExpression(prefix) => Some(prefix.operator),
                    _ => None,
                },
                type_operator: match &node.data {
                    NodeData::TypeOperatorNode(operator) => Some(operator.operator),
                    _ => None,
                },
                alias_type_parameter: match &node.data {
                    NodeData::TypeParameterDeclaration(parameter)
                        if node
                            .parent
                            .and_then(|parent| arena.get(parent))
                            .is_some_and(|parent| {
                                parent.kind == SyntaxKind::TypeAliasDeclaration
                            }) =>
                    {
                        Some(Box::new(AliasTypeParameterSyntaxFacts {
                            constraint: parameter.constraint,
                            default_type: parameter.default_type,
                        }))
                    }
                    _ => None,
                },
                mapped_type: match &node.data {
                    NodeData::MappedTypeNode(mapped) => Some(Box::new(MappedTypeSyntaxFacts {
                        type_parameter: mapped.type_parameter,
                        constraint: arena.get(mapped.type_parameter).and_then(|parameter| {
                            match &parameter.data {
                                NodeData::TypeParameterDeclaration(parameter) => {
                                    parameter.constraint
                                }
                                _ => None,
                            }
                        }),
                        name_type: mapped.name_type,
                        template: mapped.type_,
                        modifiers: MappedTypeModifiers::from_token_kinds(
                            mapped
                                .readonly_token
                                .and_then(|token| arena.get(token))
                                .map(|token| token.kind),
                            mapped
                                .question_token
                                .and_then(|token| arena.get(token))
                                .map(|token| token.kind),
                        ),
                    })),
                    _ => None,
                },
                plain_interface_heritage: matches!(&node.data, NodeData::InterfaceDeclaration(_))
                    .then(|| {
                        Box::new(
                            Self::plain_interface_heritage_facts(arena, node_id, node)
                                .unwrap_or(PlainInterfaceHeritageFacts::Unsupported),
                        )
                    }),
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

    fn index_source_node_children(facts: &[Option<SourceNodeFacts>]) -> Option<Vec<Box<[NodeId]>>> {
        let mut children = vec![Vec::new(); facts.len()];
        for (index, facts) in facts.iter().enumerate() {
            if let Some(parent) = facts.as_ref().and_then(|facts| facts.parent) {
                children
                    .get_mut(parent.index())?
                    .push(NodeId::new(u32::try_from(index).ok()?));
            }
        }
        Some(children.into_iter().map(Vec::into_boxed_slice).collect())
    }

    fn plain_interface_heritage_facts(
        arena: &NodeArena,
        declaration: NodeId,
        record: &ts_ast::Node,
    ) -> Option<PlainInterfaceHeritageFacts> {
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return None;
        };
        let identifier = |id, parent| {
            let node = arena.get(id)?;
            let NodeData::Identifier(identifier) = &node.data else {
                return None;
            };
            (node.kind == SyntaxKind::Identifier
                && node.flags.0 == 0
                && node.parent == Some(parent)
                && node.range.start < node.range.end
                && !identifier.text.is_empty()
                && identifier.flow_node.is_none())
            .then_some(node)
        };
        let name = identifier(interface.name, declaration)?;
        let parent = arena.get(record.parent?)?;
        if record.kind != SyntaxKind::InterfaceDeclaration
            || record.flags.0 != 0
            || interface.type_parameters.is_some()
            || interface.flow_node.is_some()
            || interface.local_symbol.is_some()
            || interface.symbol.is_some()
            || parent.range.start > record.range.start
            || record.range.start >= name.range.start
            || name.range.end > interface.members.range.start
            || interface.members.range.start >= interface.members.range.end
            || interface.members.range.end != record.range.end
            || record.range.end > parent.range.end
            || interface.members.has_trailing_comma
        {
            return None;
        }
        let Some(clauses) = &interface.heritage_clauses else {
            return Some(PlainInterfaceHeritageFacts::NoHeritage);
        };
        let [clause] = clauses.nodes.as_slice() else {
            return None;
        };
        let clause_record = arena.get(*clause)?;
        let NodeData::HeritageClause(heritage) = &clause_record.data else {
            return None;
        };
        if clauses.has_trailing_comma
            || clauses.range != clause_record.range
            || clause_record.kind != SyntaxKind::HeritageClause
            || clause_record.flags.0 != 0
            || clause_record.parent != Some(declaration)
            || clause_record.range.start < name.range.end
            || clause_record.range.end > interface.members.range.start
            || heritage.token != SyntaxKind::ExtendsKeyword
            || heritage.facts != 0
            || heritage.types.nodes.is_empty()
            || heritage.types.has_trailing_comma
            || heritage.types.range.start <= clause_record.range.start
            || heritage.types.range.start >= heritage.types.range.end
            || heritage.types.range.end != clause_record.range.end
            || arena.source_text()?.get(
                usize::try_from(clause_record.range.start.get()).ok()?
                    ..usize::try_from(heritage.types.range.start.get()).ok()?,
            ) != Some("extends")
        {
            return None;
        }
        let mut bases = Vec::with_capacity(heritage.types.nodes.len());
        let mut previous_end = heritage.types.range.start;
        for &expression in &heritage.types.nodes {
            let base_record = arena.get(expression)?;
            let NodeData::ExpressionWithTypeArguments(base) = &base_record.data else {
                return None;
            };
            let name = identifier(base.expression, expression)?;
            if base_record.kind != SyntaxKind::ExpressionWithTypeArguments
                || base_record.flags.0 != 0
                || base_record.parent != Some(*clause)
                || base_record.range.start < previous_end
                || base_record.range.end > heritage.types.range.end
                || base_record.range != name.range
                || base.facts != 0
                || base.type_arguments.is_some()
            {
                return None;
            }
            previous_end = base_record.range.end;
            bases.push(PlainInterfaceBaseFacts {
                expression,
                name: base.expression,
            });
        }
        (previous_end == heritage.types.range.end).then(|| PlainInterfaceHeritageFacts::Plain {
            clause: *clause,
            bases: bases.into_boxed_slice(),
        })
    }

    fn named_default_function_name(
        arena: &NodeArena,
        declaration: NodeId,
        record: &ts_ast::Node,
    ) -> Option<NodeId> {
        let NodeData::FunctionDeclaration(function) = &record.data else {
            return None;
        };
        let modifiers = function.modifiers.as_ref()?;
        let [export, default] = modifiers.list.nodes.as_slice() else {
            return None;
        };
        let name = function.name?;
        let name_record = arena.get(name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return None;
        };
        if record.kind != SyntaxKind::FunctionDeclaration
            || record.flags.0 != 0
            || modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifiers.list.range.start != record.range.start
            || modifiers.list.range.end > name_record.range.start
            || name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(declaration)
            || identifier.text.is_empty()
            || identifier.flow_node.is_some()
        {
            return None;
        }
        let text = arena.source_text()?;
        let mut previous_end = record.range.start;
        for (index, (&modifier, kind, spelling)) in [
            (export, SyntaxKind::ExportKeyword, "export"),
            (default, SyntaxKind::DefaultKeyword, "default"),
        ]
        .into_iter()
        .enumerate()
        {
            let modifier = arena.get(modifier)?;
            if modifier.kind != kind
                || modifier.flags.0 != 0
                || !matches!(modifier.data, NodeData::Token(_))
                || modifier.parent != Some(declaration)
                || modifier.range.start < previous_end
                || index == 0 && modifier.range.start != record.range.start
                || modifier.range.end > modifiers.list.range.end
                || text.get(
                    usize::try_from(modifier.range.start.get()).ok()?
                        ..usize::try_from(modifier.range.end.get()).ok()?,
                ) != Some(spelling)
            {
                return None;
            }
            previous_end = modifier.range.end;
        }
        Some(name)
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
    fn validate_unresolved_symbol_request(
        &self,
        names: &[EscapedName],
    ) -> Result<(), UnresolvedTypeError> {
        if self.intrinsic_bootstrap.is_none() {
            return Err(UnresolvedTypeError::MissingBootstrap);
        }
        if names.is_empty()
            || names
                .iter()
                .any(|name| name.as_ref().is_internal() || name.as_utf8().is_none_or(str::is_empty))
        {
            return Err(UnresolvedTypeError::InvalidName);
        }
        Ok(())
    }

    fn unresolved_symbol_matches_key(
        &self,
        symbol: SemanticSymbolId,
        key: &UnresolvedSymbolKey,
    ) -> bool {
        let Some(bootstrap) = self.intrinsic_bootstrap.as_ref() else {
            return false;
        };
        let Some(record) = self.symbol(symbol) else {
            return false;
        };
        self.unresolved_symbols.get(key) == Some(&symbol)
            && self.unresolved_symbol_keys.get(&symbol) == Some(key)
            && self.get_merged_symbol(symbol) == Some(symbol)
            && record.flags() == SymbolFlags::TYPE_ALIAS | SymbolFlags::TRANSIENT
            && record.check_flags() == CheckFlags::UNRESOLVED
            && record.name() == key.name.as_ref()
            && record.parent() == key.parent
            && record.declarations().is_none()
            && record.value_declaration().is_none()
            && record.members().is_none()
            && record.exports().is_none()
            && record.export_symbol().is_none()
            && self.type_alias_links(symbol)
                == Some(&TypeAliasLinks {
                    declared_type: Some(bootstrap.unresolved_type),
                    ..TypeAliasLinks::default()
                })
    }

    fn unresolved_path_prefix(
        &self,
        names: &[EscapedName],
    ) -> Result<(Option<SemanticSymbolId>, usize), UnresolvedTypeError> {
        let mut parent = None;
        for (index, name) in names.iter().enumerate() {
            let key = UnresolvedSymbolKey {
                parent,
                name: name.clone(),
            };
            let Some(symbol) = self.unresolved_symbols.get(&key).copied() else {
                return Ok((parent, index));
            };
            if !self.unresolved_symbol_matches_key(symbol, &key) {
                return Err(UnresolvedTypeError::InvalidSymbol(symbol));
            }
            parent = Some(symbol);
        }
        Ok((parent, names.len()))
    }

    /// Reads the exact symbol cache without allocating a type or repairing records.
    pub(super) fn unresolved_symbol_for_name_path(
        &self,
        names: &[EscapedName],
    ) -> Result<Option<SemanticSymbolId>, UnresolvedTypeError> {
        self.validate_unresolved_symbol_request(names)?;
        let (symbol, prefix) = self.unresolved_path_prefix(names)?;
        Ok((prefix == names.len()).then_some(symbol).flatten())
    }

    /// Creates only the missing symbols after validating and reserving the full path.
    pub(super) fn get_or_create_unresolved_symbol(
        &mut self,
        names: &[EscapedName],
    ) -> Result<SemanticSymbolId, UnresolvedTypeError> {
        if let Some(symbol) = self.unresolved_symbol_for_name_path(names)? {
            return Ok(symbol);
        }
        let (mut parent, prefix) = self.unresolved_path_prefix(names)?;
        let missing = names.len() - prefix;
        if !self.try_reserve_checker_symbol_allocations(missing, 0)
            || !self.links.type_alias.try_reserve(missing)
            || self.unresolved_symbols.try_reserve(missing).is_err()
            || self.unresolved_symbol_keys.try_reserve(missing).is_err()
        {
            return Err(UnresolvedTypeError::Capacity);
        }
        let unresolved = self
            .intrinsic_bootstrap
            .as_ref()
            .expect("validated symbol publication requires bootstrap")
            .unresolved_type;
        for name in &names[prefix..] {
            let key = UnresolvedSymbolKey {
                parent,
                name: name.clone(),
            };
            let mut data = SymbolData::new(
                SymbolFlags::TYPE_ALIAS | SymbolFlags::TRANSIENT,
                name.clone(),
            );
            data.check_flags = CheckFlags::UNRESOLVED;
            data.parent = parent;
            let symbol = self
                .alloc_symbol(data)
                .expect("reserved unresolved symbol allocation must succeed");
            assert!(self.set_type_alias_links(
                symbol,
                TypeAliasLinks {
                    declared_type: Some(unresolved),
                    ..TypeAliasLinks::default()
                }
            ));
            assert!(
                self.unresolved_symbols
                    .insert(key.clone(), symbol)
                    .is_none()
            );
            assert!(self.unresolved_symbol_keys.insert(symbol, key).is_none());
            parent = Some(symbol);
        }
        Ok(parent.expect("a nonempty unresolved path has a symbol"))
    }

    #[cfg(test)]
    pub(super) fn authenticated_unresolved_symbol_chain(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<Vec<SemanticSymbolId>, UnresolvedTypeError> {
        let mut chain = Vec::new();
        let mut seen = HashSet::new();
        let mut current = Some(symbol);
        while let Some(symbol) = current {
            let key = self
                .unresolved_symbol_keys
                .get(&symbol)
                .ok_or(UnresolvedTypeError::InvalidSymbol(symbol))?;
            if !seen.insert(symbol) || !self.unresolved_symbol_matches_key(symbol, key) {
                return Err(UnresolvedTypeError::InvalidSymbol(symbol));
            }
            chain.push(symbol);
            current = key.parent;
        }
        chain.reverse();
        Ok(chain)
    }

    pub(super) fn record_source_callable_alias_resolution(
        &mut self,
        annotation: NodeRef,
        resolution: SourceCallableAliasResolution,
    ) -> bool {
        if resolution.annotation() != annotation || !resolution.is_exact(self) {
            return false;
        }
        let Some((proof, recorded)) = self.source_callable_alias_annotations.get_mut(&annotation)
        else {
            return false;
        };
        if proof != resolution.proof() {
            return false;
        }
        if let Some(recorded) = recorded {
            return recorded == &resolution;
        }
        *recorded = Some(resolution);
        if self.relation_observable_nodes.contains(&annotation) {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    /// Publishes the canonical late-bound symbol for one computed property or method.
    ///
    /// The declaration must retain its binder-owned `__computed` property,
    /// while `key_type` must be the already-created unique-symbol identity.
    /// `members` must be a checker-owned table separate from the binder's
    /// original member table. Methods require a resolved key expression from
    /// the source key plan. Existing publication reuses the same symbol.
    ///
    /// # Panics
    ///
    /// Panics if the symbol identity space is exhausted or an already
    /// prevalidated publication step violates an internal store invariant.
    pub fn create_late_bound_property_symbol(
        &mut self,
        owner: SemanticSymbolId,
        early_symbol: SemanticSymbolId,
        key_type: TypeId,
        members: SymbolTableId,
    ) -> Option<SemanticSymbolId> {
        let owner_record = self.symbol(owner)?;
        let binder_members = owner_record.members();
        let early = self.symbol(early_symbol)?;
        let [declaration] = early.declarations()? else {
            return None;
        };
        let declaration = *declaration;
        let SourceNodeParent::Parent(owner_declaration) = self.source_node_parent(declaration)?
        else {
            return None;
        };
        let key_record = self.type_payload(key_type)?;
        let TypeData::UniqueEsSymbol(unique) = key_record.data() else {
            return None;
        };
        let key_symbol = key_record.symbol()?;
        let key = self.symbol(key_symbol)?;
        let method = early.flags().contains(SymbolFlags::METHOD);
        let member_flag = if method {
            SymbolFlags::METHOD
        } else {
            SymbolFlags::PROPERTY
        };
        let allowed_property_flags = member_flag | SymbolFlags::OPTIONAL;
        let key_property = key.flags() == SymbolFlags::PROPERTY;
        let valid_key = if key_property {
            let key_declaration = key.value_declaration()?;
            let key_owner = key.parent()?;
            let key_owner_record = self.symbol(key_owner)?;
            let key_annotation = self.source_direct_type_annotation(key_declaration)?;
            let key_facts = self.source_node_facts.get(&key_declaration.arena)?;
            let annotation_facts = key_facts.get(key_annotation.node.index())?.as_ref()?;
            let readonly = key_facts.iter().flatten().any(|facts| {
                facts.parent == Some(key_declaration.node)
                    && facts.kind == SyntaxKind::ReadonlyKeyword
            });
            let static_ = key_facts.iter().flatten().any(|facts| {
                facts.parent == Some(key_declaration.node)
                    && facts.kind == SyntaxKind::StaticKeyword
            });
            readonly
                && annotation_facts.kind == SyntaxKind::TypeOperator
                && annotation_facts.type_operator == Some(SyntaxKind::UniqueKeyword)
                && key.declarations() == Some(&[key_declaration][..])
                && (key_owner_record.flags().contains(SymbolFlags::INTERFACE)
                    || key_owner_record.flags().contains(SymbolFlags::TYPE_LITERAL)
                    || key_owner_record.flags().contains(SymbolFlags::CLASS) && static_)
                && key.check_flags().bits() & !CheckFlags::READONLY.bits() == 0
                && matches!(
                    self.source_node_kind(key_declaration),
                    Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
                )
                && self
                    .type_node_links(key_annotation)
                    .and_then(|links| links.resolved_type)
                    == Some(key_type)
                && [key_owner_record.members(), key_owner_record.exports()]
                    .into_iter()
                    .flatten()
                    .any(|table| {
                        self.symbol_table(table)
                            .and_then(|table| table.get(key.name()))
                            .and_then(|symbol| self.get_merged_symbol(symbol))
                            == Some(key_symbol)
                    })
        } else {
            key.flags().contains(SymbolFlags::BLOCK_SCOPED_VARIABLE)
                && key.check_flags() == CheckFlags::NONE
        };
        if !owner_record
            .flags()
            .intersects(SymbolFlags::LATE_BINDING_CONTAINER)
            || owner_record.check_flags() != CheckFlags::NONE
            || owner_record
                .declarations()
                .is_none_or(|declarations| !declarations.contains(&owner_declaration))
            || self.get_merged_symbol(owner) != Some(owner)
            || Some(members) == binder_members
            || binder_members.is_none() && !self.source_symbol_has_only_computed_members(owner)
            || self.symbol_table(members).is_none()
            || !early.flags().contains(member_flag)
            || early.flags().without(allowed_property_flags) != SymbolFlags::NONE
            || early.check_flags() != CheckFlags::NONE
            || early.name() != InternalSymbolName::Computed.as_ref()
            || early.value_declaration() != Some(declaration)
            || early.members().is_some()
            || early.exports().is_some()
            || early.export_symbol().is_some()
            || early
                .parent()
                .and_then(|parent| self.get_merged_symbol(parent))
                != Some(owner)
            || self.get_merged_symbol(early_symbol) != Some(early_symbol)
            || if method {
                self.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature)
            } else {
                !matches!(
                    self.source_node_kind(declaration),
                    Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
                )
            }
            || !matches!(
                self.source_node_kind(owner_declaration),
                Some(SyntaxKind::InterfaceDeclaration | SyntaxKind::TypeLiteral)
            )
            || key_record.flags() != TypeFlags::UNIQUE_ES_SYMBOL
            || key_record.object_flags() != ObjectFlags::NONE
            || key_record.alias().is_some()
            || !unique.name.as_ref().is_late_bound()
            || !valid_key
            || key.value_declaration().is_none()
            || self.get_merged_symbol(key_symbol) != Some(key_symbol)
            || self
                .symbol_store()
                .assigned_global_symbol_id(key_symbol)
                .is_none()
            || self.value_symbol_links(key_symbol).is_some_and(|links| {
                links != &ValueSymbolLinks::default()
                    && links
                        != &(ValueSymbolLinks {
                            resolved_type: Some(key_type),
                            ..ValueSymbolLinks::default()
                        })
            })
        {
            return None;
        }

        if method
            && binder_members.is_some_and(|raw| {
                self.symbol_table(raw).is_none_or(|raw| {
                    raw.iter().any(|(name, symbol)| {
                        self.symbol_table(members)
                            .and_then(|members| members.get(name))
                            .and_then(|symbol| self.get_merged_symbol(symbol))
                            != self.get_merged_symbol(symbol)
                    })
                })
            })
        {
            return None;
        }

        let optional = early.flags().contains(SymbolFlags::OPTIONAL);
        let facts = self.source_node_facts.get(&declaration.arena)?;
        let mut computed = None;
        let mut optional_count = 0usize;
        for (index, facts) in facts.iter().enumerate() {
            let Some(facts) = facts else {
                continue;
            };
            if facts.parent != Some(declaration.node) {
                continue;
            }
            match facts.kind {
                SyntaxKind::ComputedPropertyName => {
                    if computed.is_some() {
                        return None;
                    }
                    computed = Some(NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        NodeId::new(u32::try_from(index).ok()?),
                    ));
                }
                SyntaxKind::QuestionToken => optional_count = optional_count.checked_add(1)?,
                _ => {}
            }
        }
        let computed = computed?;
        if optional_count != usize::from(optional) {
            return None;
        }
        let mut key_expression = None;
        for (index, facts) in facts.iter().enumerate() {
            let Some(facts) = facts else {
                continue;
            };
            if facts.parent == Some(computed.node)
                && matches!(
                    facts.kind,
                    SyntaxKind::Identifier | SyntaxKind::PropertyAccessExpression
                )
            {
                if key_expression.is_some() {
                    return None;
                }
                key_expression = Some(NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    NodeId::new(u32::try_from(index).ok()?),
                ));
            }
        }
        let key_expression = key_expression?;
        if (method
            || key_property
            || self.source_node_kind(key_expression) == Some(SyntaxKind::PropertyAccessExpression))
            && (self
                .symbol_node_links(key_expression)
                .and_then(|links| links.resolved_symbol)
                != Some(key_symbol)
                || self
                    .type_node_links(key_expression)
                    .and_then(|links| links.resolved_type)
                    != Some(key_type))
        {
            return None;
        }
        if self.symbol_node_links(key_expression).is_some_and(|links| {
            links != &SymbolNodeLinks::default()
                && links
                    != &(SymbolNodeLinks {
                        resolved_symbol: Some(key_symbol),
                    })
        }) {
            return None;
        }

        let expected_name = unique.name.clone();
        let original_flags = early.flags();
        let canonical_name = self.unique_symbol_name(key_symbol)?;
        if canonical_name != expected_name {
            return None;
        }

        let current_late = self
            .late_bound_links(early_symbol)
            .and_then(|links| links.late_symbol);
        if let Some(late) = current_late {
            let late_record = self.symbol(late)?;
            let value_links = self.value_symbol_links(late)?;
            if late_record.flags() != (original_flags | SymbolFlags::TRANSIENT)
                || late_record.check_flags() != CheckFlags::LATE
                || late_record.name() != expected_name.as_ref()
                || late_record.declarations() != Some(&[declaration])
                || late_record.value_declaration() != Some(declaration)
                || late_record.members().is_some()
                || late_record.exports().is_some()
                || late_record.parent() != Some(owner)
                || late_record.export_symbol().is_some()
                || self.get_merged_symbol(late) != Some(late)
                || value_links
                    != &(ValueSymbolLinks {
                        resolved_type: value_links.resolved_type,
                        name_type: Some(key_type),
                        ..ValueSymbolLinks::default()
                    })
                || !self.valid_optional_type(value_links.resolved_type)
                || self.symbol_node_links(declaration)
                    != Some(&SymbolNodeLinks {
                        resolved_symbol: Some(late),
                    })
                || self.symbol_table(members)?.get(expected_name.as_ref()) != Some(late)
            {
                return None;
            }
            return Some(late);
        }
        if self
            .late_bound_links(early_symbol)
            .is_some_and(|links| links != &LateBoundLinks::default())
            || self
                .symbol_node_links(declaration)
                .is_some_and(|links| links != &SymbolNodeLinks::default())
            || self
                .symbol_table(members)?
                .get(expected_name.as_ref())
                .is_some()
        {
            return None;
        }

        let missing_late_links = usize::from(self.late_bound_links(early_symbol).is_none());
        let missing_node_links = usize::from(self.symbol_node_links(declaration).is_none());
        if !self.try_reserve_checker_symbol_allocations(1, 0)
            || !self.links.late_bound.try_reserve(missing_late_links)
            || !self.links.symbol_node.try_reserve(missing_node_links)
            || !self.links.value_symbol.try_reserve(1)
        {
            return None;
        }
        let mut declarations = Vec::new();
        declarations.try_reserve_exact(1).ok()?;
        declarations.push(declaration);

        let late =
            self.alloc_transient_symbol(original_flags, canonical_name.clone(), CheckFlags::LATE);
        assert!(self.set_symbol_declarations(late, Some(declarations), Some(declaration)));
        assert!(self.set_symbol_relationships(late, None, None, Some(owner), None));
        assert!(self.set_value_symbol_links(
            late,
            ValueSymbolLinks {
                name_type: Some(key_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(self.set_late_bound_links(
            early_symbol,
            LateBoundLinks {
                late_symbol: Some(late),
            },
        ));
        assert!(self.set_symbol_node_links(
            declaration,
            SymbolNodeLinks {
                resolved_symbol: Some(late),
            },
        ));
        assert_eq!(
            self.insert_symbol(members, canonical_name, late),
            Some(None)
        );
        Some(late)
    }

    /// Returns a published global interface method only when its callable
    /// object, signature, and binder-owned parameter graph remain authentic.
    pub(super) fn global_interface_method_callable_type(
        &self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        let type_ = self.global_interface_method_linked_type(signature)?;
        let declaration = self.signature(signature)?.declaration()?;
        let method = self.global_interface_method_for_declaration(declaration)?;
        let record = self.type_payload(type_)?;
        let TypeData::Object(object) = record.data() else {
            return None;
        };
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
            || record.symbol() != Some(method)
            || record.alias().is_some()
            || object.target.is_some()
            || object.mapper.is_some()
            || object.instantiations != TypeCacheState::Unallocated
            || object.structured.constrained != ConstrainedTypeData::default()
            || object.structured.members.is_some()
            || object.structured.properties.is_some()
            || object.structured.signatures.as_deref() != Some([signature].as_slice())
            || object.structured.call_signature_count != 1
            || object.structured.index_infos.is_some()
            || object
                .structured
                .object_type_without_abstract_construct_signatures
                .is_some()
        {
            return None;
        }
        Some(type_)
    }

    /// Publishes a dependency-closed batch of local ambient overload groups.
    ///
    /// Every source, binder, cache, and capacity edge is checked before the
    /// first callable identity is allocated. Once allocation begins, all
    /// reverse-map and link writes are infallible assertions over the reserved
    /// batch.
    pub(super) fn publish_source_overload_batch(
        &mut self,
        prepared: Vec<PreparedSourceOverloadPublication>,
    ) -> Option<Vec<(TypeId, Box<[SignatureId]>)>> {
        let group_count = prepared.len();
        let signature_count = prepared.iter().try_fold(0usize, |count, group| {
            count.checked_add(group.signatures.len())
        })?;
        let parameter_count = prepared.iter().try_fold(0usize, |count, group| {
            group.signatures.iter().try_fold(count, |count, signature| {
                count.checked_add(signature.parameters.len())
            })
        })?;
        let mut owners = HashSet::with_capacity(group_count);
        let mut declarations = HashSet::with_capacity(signature_count);
        let mut parameter_declarations = HashSet::with_capacity(parameter_count);
        let mut parameter_symbols = HashSet::with_capacity(parameter_count);

        for group in &prepared {
            let owner = self.symbol(group.owner_symbol)?;
            let declaration_order = group
                .signatures
                .iter()
                .map(|signature| signature.declaration)
                .collect::<Vec<_>>();
            let common_parent = declaration_order
                .first()
                .and_then(|declaration| self.source_node_parent(*declaration));
            if group.signatures.len() < 2
                || !owners.insert(group.owner_symbol)
                || owner.flags() != SymbolFlags::FUNCTION
                || owner.check_flags() != CheckFlags::NONE
                || owner.declarations() != Some(declaration_order.as_slice())
                || owner.value_declaration() != declaration_order.first().copied()
                || owner.members().is_some()
                || owner.exports().is_some()
                || owner.parent().is_some()
                || owner.export_symbol().is_some()
                || self.get_merged_symbol(group.owner_symbol) != Some(group.owner_symbol)
                || common_parent.is_none()
                || common_parent.and_then(|parent| match parent {
                    SourceNodeParent::Parent(parent) => self.source_node_kind(parent),
                    SourceNodeParent::Root => None,
                }) != Some(SyntaxKind::SourceFile)
                || self
                    .value_symbol_links(group.owner_symbol)
                    .is_some_and(|links| links != &ValueSymbolLinks::default())
                || self
                    .source_callable_types_by_owner
                    .contains_key(&group.owner_symbol)
                || self
                    .source_overload_types_by_owner
                    .contains_key(&group.owner_symbol)
                || self.source_overload_provenance_claims(
                    group.owner_symbol,
                    declaration_order.as_slice(),
                )
                || group.array_targets.is_some_and(|targets| {
                    self.type_payload(targets.array_type()).is_none()
                        || self.type_payload(targets.readonly_array_type()).is_none()
                })
            {
                return None;
            }
            for signature in &group.signatures {
                if !declarations.insert(signature.declaration)
                    || self.source_node_kind(signature.declaration)
                        != Some(SyntaxKind::FunctionDeclaration)
                    || self.source_node_parent(signature.declaration) != common_parent
                    || self
                        .signature_links(signature.declaration)
                        .is_some_and(|links| links != &SignatureLinks::default())
                    || self
                        .source_callable_types_by_declaration
                        .contains_key(&signature.declaration)
                    || self
                        .source_overload_types_by_declaration
                        .contains_key(&signature.declaration)
                    || signature.flags.bits() & !SignatureFlags::HAS_LITERAL_TYPES.bits() != 0
                    || signature.min_argument_count < 0
                    || usize::try_from(signature.min_argument_count)
                        .map_or(true, |minimum| minimum > signature.parameters.len())
                    || self.type_payload(signature.return_type).is_none()
                    || !self.contains_node_ref(signature.return_annotation)
                {
                    return None;
                }
                let mut optional_seen = false;
                for parameter in &signature.parameters {
                    let symbol = self.symbol(parameter.symbol)?;
                    if !parameter_declarations.insert(parameter.declaration)
                        || !parameter_symbols.insert(parameter.symbol)
                        || self.source_node_kind(parameter.declaration)
                            != Some(SyntaxKind::Parameter)
                        || self.source_node_parent(parameter.declaration)
                            != Some(SourceNodeParent::Parent(signature.declaration))
                        || symbol.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                        || symbol.check_flags() != CheckFlags::NONE
                        || symbol.declarations() != Some(&[parameter.declaration])
                        || symbol.value_declaration() != Some(parameter.declaration)
                        || symbol.members().is_some()
                        || symbol.exports().is_some()
                        || symbol.parent().is_some()
                        || symbol.export_symbol().is_some()
                        || self.get_merged_symbol(parameter.symbol) != Some(parameter.symbol)
                        || self
                            .value_symbol_links(parameter.symbol)
                            .is_some_and(|links| links != &ValueSymbolLinks::default())
                        || !self.contains_node_ref(parameter.annotation)
                        || self.type_payload(parameter.base_type).is_none()
                        || self.type_payload(parameter.call_type).is_none()
                        || optional_seen && !parameter.optional
                    {
                        return None;
                    }
                    optional_seen |= parameter.optional;
                }
            }
        }

        let value_link_count = group_count.checked_add(parameter_count)?;
        if !self.try_reserve_types(group_count)
            || !self.try_reserve_signatures(signature_count)
            || !self.try_reserve_source_overload_provenance(
                group_count,
                signature_count,
                signature_count,
            )
            || !self.try_reserve_function_signature_return_annotations(signature_count)
            || !self.try_reserve_callable_signature_parameter_types(signature_count)
            || !self.links.signature.try_reserve(signature_count)
            || !self.links.value_symbol.try_reserve(value_link_count)
        {
            return None;
        }

        let mut published = Vec::with_capacity(group_count);
        for group in prepared {
            let type_ = self
                .alloc_plain_object_type(
                    super::types::ObjectFlags::ANONYMOUS,
                    Some(group.owner_symbol),
                )
                .expect("source overload owner was prevalidated");
            let mut signature_ids = Vec::with_capacity(group.signatures.len());
            for signature in &group.signatures {
                let signature_id = self
                    .alloc_signature(
                        signature.flags,
                        Some(signature.declaration),
                        Vec::new(),
                        None,
                        signature
                            .parameters
                            .iter()
                            .map(|parameter| parameter.symbol)
                            .collect(),
                        Some(signature.return_type),
                        None,
                        signature.min_argument_count,
                    )
                    .expect("source overload signature was prevalidated");
                signature_ids.push(signature_id);
            }
            let provenance_rows = group
                .signatures
                .iter()
                .zip(&signature_ids)
                .map(
                    |(signature, signature_id)| SourceOverloadSignatureProvenance {
                        declaration: signature.declaration,
                        signature: *signature_id,
                        flags: signature.flags,
                        parameters: signature
                            .parameters
                            .iter()
                            .map(|parameter| SourceOverloadParameterProvenance {
                                declaration: parameter.declaration,
                                symbol: parameter.symbol,
                                annotation: parameter.annotation,
                                annotation_null_literal_identity: parameter
                                    .annotation_null_literal_identity,
                                base_type: parameter.base_type,
                                call_type: parameter.call_type,
                                optional: parameter.optional,
                            })
                            .collect(),
                        return_annotation: signature.return_annotation,
                        return_annotation_null_literal_identity: signature
                            .return_annotation_null_literal_identity,
                        return_type: signature.return_type,
                    },
                )
                .collect::<Box<[_]>>();
            assert!(
                self.source_overload_provenance
                    .insert(
                        type_,
                        SourceOverloadProvenance {
                            owner_symbol: group.owner_symbol,
                            signatures: provenance_rows,
                            array_targets: group.array_targets,
                        },
                    )
                    .is_none()
            );
            assert!(
                self.source_overload_types_by_owner
                    .insert(group.owner_symbol, type_)
                    .is_none()
            );
            for (signature, signature_id) in group.signatures.iter().zip(&signature_ids) {
                assert!(
                    self.source_overload_types_by_declaration
                        .insert(signature.declaration, type_)
                        .is_none()
                );
                assert!(
                    self.source_overload_types_by_signature
                        .insert(*signature_id, type_)
                        .is_none()
                );
            }
            assert!(self.set_value_symbol_links(
                group.owner_symbol,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert!(self.set_structured_type_members(
                type_,
                None,
                None,
                Some(signature_ids.clone()),
                None,
                None,
            ));
            for (signature, signature_id) in group.signatures.iter().zip(&signature_ids) {
                assert!(self.set_signature_links(
                    signature.declaration,
                    SignatureLinks {
                        resolved_signature: ResolvedSignatureState::Resolved(*signature_id),
                        ..SignatureLinks::default()
                    },
                ));
                assert!(self.set_function_signature_return_annotation(
                    *signature_id,
                    signature.return_annotation,
                    signature.return_annotation_null_literal_identity,
                ));
            }
            assert!(
                self.set_callable_signature_parameter_types_batch(
                    group
                        .signatures
                        .iter()
                        .zip(&signature_ids)
                        .map(|(signature, signature_id)| {
                            (
                                *signature_id,
                                signature
                                    .parameters
                                    .iter()
                                    .map(|parameter| parameter.call_type)
                                    .collect(),
                            )
                        })
                        .collect(),
                )
            );
            for signature in &group.signatures {
                for parameter in &signature.parameters {
                    assert!(self.set_value_symbol_links(
                        parameter.symbol,
                        ValueSymbolLinks {
                            resolved_type: Some(parameter.call_type),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
            }
            published.push((type_, signature_ids.into_boxed_slice()));
        }
        Some(published)
    }

    pub(super) fn try_reserve_properties_type_cache(&mut self, additional: usize) -> bool {
        self.properties_types.try_reserve(additional).is_ok()
    }

    pub(super) fn cached_properties_type(&self, key: PropertiesTypeCacheKey) -> Option<TypeId> {
        self.properties_types.get(&key).copied()
    }

    pub(super) fn cache_properties_type(
        &mut self,
        key: PropertiesTypeCacheKey,
        result: TypeId,
    ) -> bool {
        let Some(target) = self.type_payload(key.type_id) else {
            return false;
        };
        if self.type_payload(result).is_none()
            || target
                .object_flags()
                .intersects(super::types::ObjectFlags::UNRESOLVED_MEMBERS)
                != key.unresolved_members
        {
            return false;
        }
        if let Some(cached) = self.properties_types.get(&key) {
            *cached == result
        } else {
            self.properties_types.insert(key, result);
            true
        }
    }

    #[must_use]
    pub fn properties_type_cache_len(&self) -> usize {
        self.properties_types.len()
    }

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
    ) -> Option<&DirectInterfaceHeritageProvenance> {
        self.observe_relation_type_read(type_);
        self.direct_interface_heritage_provenance.get(&type_)
    }
}

impl SemanticStore<TypeRecord, super::mapper::TypeMapper> {
    pub(super) fn try_reserve_published_interface_method_origins(
        &mut self,
        signature_count: usize,
    ) -> bool {
        self.published_interface_method_origins
            .try_reserve(1)
            .is_ok()
            && self
                .published_interface_method_signature_owners
                .try_reserve(signature_count)
                .is_ok()
    }

    /// Readers must validate a retained origin, including a damaged record.
    pub(super) fn published_interface_method_origin(
        &self,
        type_: TypeId,
    ) -> Option<&PublishedInterfaceMethodOrigin> {
        self.observe_relation_type_read(type_);
        self.published_interface_method_origins.get(&type_)
    }

    pub(super) fn published_interface_method_type_for_signature(
        &self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        self.observe_relation_signature_read(signature);
        self.published_interface_method_signature_owners
            .get(&signature)
            .copied()
    }

    /// Only the selected method producer can publish this complete signature group.
    pub(super) fn publish_published_interface_method_origin(
        &mut self,
        origin: PublishedInterfaceMethodOrigin,
    ) -> bool {
        let type_ = origin.result_type();
        let signatures = origin.signatures();
        if self.published_interface_method_origins.contains_key(&type_)
            || signatures.is_empty()
            || signatures.iter().enumerate().any(|(index, signature)| {
                signatures[..index].contains(signature)
                    || self
                        .published_interface_method_signature_owners
                        .contains_key(signature)
            })
            || !origin.matches_current_type(self)
        {
            return false;
        }
        for &signature in signatures {
            self.published_interface_method_signature_owners
                .insert(signature, type_);
        }
        self.published_interface_method_origins
            .insert(type_, origin);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    #[cfg(test)]
    pub(super) fn published_interface_method_origin_len(&self) -> usize {
        self.published_interface_method_origins.len()
    }

    #[cfg(test)]
    pub(super) fn published_interface_method_signature_owner_len(&self) -> usize {
        self.published_interface_method_signature_owners.len()
    }

    #[cfg(test)]
    pub(super) fn replace_published_interface_method_origin_for_test(
        &mut self,
        type_: TypeId,
        origin: Option<PublishedInterfaceMethodOrigin>,
    ) -> Option<PublishedInterfaceMethodOrigin> {
        let previous = match origin {
            Some(origin) => self
                .published_interface_method_origins
                .insert(type_, origin),
            None => self.published_interface_method_origins.remove(&type_),
        };
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        previous
    }

    #[cfg(test)]
    pub(super) fn replace_published_interface_method_type_for_signature_for_test(
        &mut self,
        signature: SignatureId,
        type_: Option<TypeId>,
    ) -> Option<TypeId> {
        let previous = match type_ {
            Some(type_) => self
                .published_interface_method_signature_owners
                .insert(signature, type_),
            None => self
                .published_interface_method_signature_owners
                .remove(&signature),
        };
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        previous
    }

    pub(super) fn published_interface_method_recovery(
        &self,
        type_: TypeId,
    ) -> Option<&PublishedInterfaceMethodRecovery> {
        self.observe_relation_type_read(type_);
        self.published_interface_method_recoveries.get(&type_)
    }

    pub(super) fn published_interface_callback_recovery(
        &self,
        actual: TypeId,
    ) -> Option<&PublishedInterfaceMethodRecovery> {
        self.observe_relation_type_read(actual);
        self.published_interface_method_recoveries
            .values()
            .find(|recovery| recovery.contains_callback(actual))
    }

    pub(super) fn try_reserve_published_interface_method_recoveries(&mut self) -> bool {
        self.published_interface_method_recoveries
            .try_reserve(1)
            .is_ok()
    }

    /// Only the selected method producer can construct this recovery evidence.
    pub(super) fn publish_published_interface_method_recovery(
        &mut self,
        recovery: PublishedInterfaceMethodRecovery,
    ) -> bool {
        let type_ = recovery.result_type();
        if self
            .published_interface_method_recoveries
            .contains_key(&type_)
            || !recovery.matches_current_type(self)
        {
            return false;
        }
        self.published_interface_method_recoveries
            .insert(type_, recovery);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    #[cfg(test)]
    pub(super) fn published_interface_method_recovery_len(&self) -> usize {
        self.published_interface_method_recoveries.len()
    }

    #[cfg(test)]
    pub(super) fn replace_published_interface_method_recovery_for_test(
        &mut self,
        type_: TypeId,
        recovery: Option<PublishedInterfaceMethodRecovery>,
    ) -> Option<PublishedInterfaceMethodRecovery> {
        let previous = match recovery {
            Some(recovery) => self
                .published_interface_method_recoveries
                .insert(type_, recovery),
            None => self.published_interface_method_recoveries.remove(&type_),
        };
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        previous
    }

    pub(super) fn try_reserve_instantiated_property_alias_callables(&mut self) -> bool {
        self.instantiated_property_alias_callables
            .try_reserve(1)
            .is_ok()
            && self
                .instantiated_property_alias_callable_types_by_signature
                .try_reserve(1)
                .is_ok()
    }

    /// A copied callable keeps its original mapping capability without granting it to a reader.
    pub(super) fn instantiated_property_alias_callable(
        &self,
        type_: TypeId,
    ) -> Option<InstantiatedPropertyAliasCallable> {
        self.observe_relation_type_read(type_);
        let origin = *self.instantiated_property_alias_callables.get(&type_)?;
        (origin.type_() == type_
            && self.instantiated_property_alias_callable_type_for_signature(origin.signature())
                == Some(type_)
            && origin.matches_current_type(self))
        .then_some(origin)
    }

    /// Returns the recorded owner even when its forward proof is damaged.
    /// The signature reader must validate that proof before returning a value.
    pub(super) fn instantiated_property_alias_callable_type_for_signature(
        &self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        self.observe_relation_signature_read(signature);
        self.instantiated_property_alias_callable_types_by_signature
            .get(&signature)
            .copied()
    }

    /// Only the property-function producer can construct this immutable record.
    pub(super) fn publish_instantiated_property_alias_callable(
        &mut self,
        origin: InstantiatedPropertyAliasCallable,
    ) -> bool {
        let type_ = origin.type_();
        if self
            .instantiated_property_alias_callables
            .contains_key(&type_)
            || self
                .instantiated_property_alias_callable_types_by_signature
                .contains_key(&origin.signature())
            || !origin.matches_current_type(self)
        {
            return false;
        }
        self.instantiated_property_alias_callables
            .insert(type_, origin);
        self.instantiated_property_alias_callable_types_by_signature
            .insert(origin.signature(), type_);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    #[cfg(test)]
    pub(super) fn instantiated_property_alias_callable_len(&self) -> usize {
        self.instantiated_property_alias_callables.len()
    }

    #[cfg(test)]
    pub(super) fn instantiated_property_alias_callable_signature_len(&self) -> usize {
        self.instantiated_property_alias_callable_types_by_signature
            .len()
    }

    #[cfg(test)]
    pub(super) fn replace_instantiated_property_alias_callable_type_for_signature_for_test(
        &mut self,
        signature: SignatureId,
        owner: Option<TypeId>,
    ) -> Option<TypeId> {
        let previous = match owner {
            Some(owner) => self
                .instantiated_property_alias_callable_types_by_signature
                .insert(signature, owner),
            None => self
                .instantiated_property_alias_callable_types_by_signature
                .remove(&signature),
        };
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        previous
    }

    #[cfg(test)]
    pub(super) fn replace_instantiated_property_alias_callable_for_test(
        &mut self,
        type_: TypeId,
        origin: Option<InstantiatedPropertyAliasCallable>,
    ) -> Option<InstantiatedPropertyAliasCallable> {
        let previous = match origin {
            Some(origin) => self
                .instantiated_property_alias_callables
                .insert(type_, origin),
            None => self.instantiated_property_alias_callables.remove(&type_),
        };
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        previous
    }

    /// The source alias producer records its supplied inputs after real recovery.
    pub(super) fn publish_property_object_alias_request_recovery(
        &mut self,
        recovery: PropertyObjectAliasRequestRecovery,
    ) -> bool {
        let key = recovery.cache_key();
        if self
            .property_object_alias_request_recoveries
            .contains_key(&key)
            || !recovery.matches_current_row(self)
        {
            return false;
        }
        self.property_object_alias_request_recoveries
            .insert(key, recovery);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    /// The source query retains the real request and its exact mapper receipt.
    pub(super) fn publish_ordinary_intersection_alias_request_recovery(
        &mut self,
        recovery: OrdinaryIntersectionAliasRequestRecovery,
    ) -> bool {
        let key = recovery.cache_key();
        if self
            .ordinary_intersection_alias_request_recoveries
            .contains_key(&key)
            || !recovery.matches_current_row(self)
        {
            return false;
        }
        self.ordinary_intersection_alias_request_recoveries
            .insert(key, recovery);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    /// Only the real anonymous-object producer can create this immutable record.
    pub(super) fn publish_property_object_alias_recovery(
        &mut self,
        recovery: PropertyObjectAliasRecovery,
    ) -> bool {
        let result = recovery.result();
        if self.property_object_alias_recoveries.contains_key(&result)
            || !recovery.matches_current_result(self)
        {
            return false;
        }
        self.property_object_alias_recoveries
            .insert(result, recovery);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    /// Only a real inline-object limit event can produce this immutable record.
    pub(super) fn publish_inline_property_object_recovery(
        &mut self,
        recovery: InlinePropertyObjectRecovery,
    ) -> bool {
        let result = recovery.result();
        if self.inline_property_object_recoveries.contains_key(&result)
            || !recovery.matches_current_result(self)
        {
            return false;
        }
        self.inline_property_object_recoveries
            .insert(result, recovery);
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        true
    }

    /// Publishes one source-checked partial construct's immutable parameter list.
    /// The interface's complete callable set is not published by this operation.
    pub(super) fn set_partial_declared_construct_parameter_types(
        &mut self,
        plan: &super::object_members::PropertyObjectPlan,
        declaration: NodeRef,
        signature: SignatureId,
        parameter_types: Vec<TypeId>,
    ) -> bool {
        if self
            .callable_signature_parameter_types
            .contains_key(&signature)
            || !super::object_members::validate_partial_declared_construct_parameter_types(
                self,
                plan,
                declaration,
                signature,
                &parameter_types,
            )
            || !self.try_reserve_callable_signature_parameter_types(1)
        {
            return false;
        }
        let relation_dirty = self.relation_signature_is_observable(signature);
        let previous = self
            .callable_signature_parameter_types
            .insert(signature, parameter_types);
        assert!(
            previous.is_none(),
            "the partial construct parameter list was absent"
        );
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    /// Checks mapped Array.sort callbacks before storing their source identity.
    #[allow(clippy::too_many_lines)] // The callee, source parameters, and mapped target form one proof.
    pub(super) fn set_contextual_source_callable_provenance(
        &mut self,
        type_: TypeId,
        provenance: &SourceCallableProvenance,
    ) -> bool {
        let sort_target_is_exact = (|| {
            let target = provenance.contextual_target?;
            let SourceNodeParent::Parent(call) = self.source_node_parent(provenance.declaration)?
            else {
                return None;
            };
            let children = self.source_direct_children(call)?;
            let [callee, argument] = children.as_slice() else {
                return None;
            };
            if provenance.family != SourceCallableFamily::ArrowFunction
                || provenance.return_provenance != SourceCallableReturnProvenance::Inferred
                || provenance.contextual_variable.is_some()
                || provenance.captured_assignment.is_some()
                || target == type_
                || *argument != provenance.declaration
                || !super::source_callables::stored_array_sort_argument_arrow_is_exact(
                    self,
                    provenance.declaration,
                    provenance.owner_symbol,
                    call,
                )
            {
                return None;
            }
            let callee_type = self.type_node_links(*callee)?.resolved_type?;
            let super::callables::StoredSingleCallableValidation::Valid {
                callable: method, ..
            } = super::callables::validate_stored_single_callable(self, callee_type)
            else {
                return None;
            };
            let [parameter] = method.parameters.as_slice() else {
                return None;
            };
            let target_matches = *parameter == target
                || matches!(self.type_payload(*parameter)?.data(), TypeData::Union(union)
                    if union.union.types.len() == 2
                        && union.union.types.contains(&target)
                        && union.union.types.contains(&self.intrinsic_bootstrap()?.undefined_type)
                        && self.validate_union_query_metadata(*parameter).is_ok());
            let super::callables::StoredSingleCallableValidation::Valid {
                callable: callback, ..
            } = super::callables::validate_stored_single_callable(self, target)
            else {
                return None;
            };
            let target_signature = self.signature(callback.signature)?;
            let signature = self.signature(provenance.signature)?;
            if !target_matches
                || callback.parameters.len() != 2
                || callback.min_argument_count != 2
                || callback.rest_parameter.is_some()
                || callback.return_type.is_none()
                || !target_signature.type_parameters().is_empty()
                || target_signature.this_parameter().is_some()
                || signature.declaration() != Some(provenance.declaration)
                || signature.flags() != SignatureFlags::NONE
                || signature.parameters().len() != 2
                || signature.parameters()[0] == signature.parameters()[1]
                || signature.min_argument_count() != 2
                || signature.resolved_min_argument_count() != -1
                || !signature.type_parameters().is_empty()
                || signature.this_parameter().is_some()
                || signature.resolved_type_predicate().is_some()
                || signature.target().is_some()
                || signature.mapper().is_some()
                || signature.isolated_signature_type().is_some()
                || signature.composite().is_some()
                || signature
                    .resolved_return_type()
                    .is_none_or(|returned| self.type_payload(returned).is_none())
            {
                return None;
            }
            for (&parameter, &expected) in signature.parameters().iter().zip(&callback.parameters) {
                let record = self.symbol(parameter)?;
                let declaration = record.value_declaration()?;
                if !super::source_callables::source_parameter_declarations_are_exact(
                    self,
                    provenance.declaration,
                    declaration,
                    parameter,
                ) || record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    || record.check_flags() != CheckFlags::NONE
                    || record.members().is_some()
                    || record.exports().is_some()
                    || record.parent().is_some()
                    || record.export_symbol().is_some()
                    || self.get_merged_symbol(parameter) != Some(parameter)
                    || self.value_symbol_links(parameter).is_some_and(|links| {
                        links != &ValueSymbolLinks::default()
                            && links
                                != &(ValueSymbolLinks {
                                    resolved_type: Some(expected),
                                    ..ValueSymbolLinks::default()
                                })
                    })
                {
                    return None;
                }
            }
            Some(())
        })()
        .is_some();
        if sort_target_is_exact {
            self.set_source_callable_provenance_with_context(type_, provenance, true)
        } else {
            self.set_source_callable_provenance(type_, provenance)
        }
    }

    /// Allocates the complete source-name record before any key or name is written.
    pub(super) fn prepare_late_bound_method_group_symbol(
        &self,
        host: &super::DeclaredTypeHost<'_>,
        owner: SemanticSymbolId,
        sources: &[SemanticSymbolId],
        key_type: TypeId,
    ) -> Option<PreparedComputedMethodNameGroup> {
        let first = *sources.first()?;
        let plan = super::object_members::plan_selected_interface_method(self, host, first).ok()?;
        if plan.symbol != owner
            || super::object_members::preflight_computed_method_group(self, host, &plan).ok()?
                != sources
        {
            return None;
        }
        let mut declarations = Vec::new();
        declarations.try_reserve_exact(sources.len()).ok()?;
        let mut retained_sources = Vec::new();
        retained_sources.try_reserve_exact(sources.len()).ok()?;
        let mut keys = Vec::new();
        keys.try_reserve_exact(sources.len()).ok()?;
        let mut name = None;
        for (&source, method) in sources.iter().zip(&plan.methods) {
            let key = method.computed_key?;
            let (type_, resolved_name) =
                super::object_members::resolved_computed_member_key(self, &key).ok()??;
            if type_ != key_type || name.as_ref().is_some_and(|name| name != &resolved_name) {
                return None;
            }
            name = Some(resolved_name);
            declarations.push(method.declaration);
            retained_sources.push(source);
            keys.push(key);
        }
        Some(PreparedComputedMethodNameGroup {
            owner,
            key_type,
            sources: retained_sources.into_boxed_slice(),
            declarations,
            keys: keys.into_boxed_slice(),
            flags: self.symbol(first)?.flags(),
            name: name?,
            existing: self
                .late_bound_links(first)
                .and_then(|links| links.late_symbol),
        })
    }

    pub(super) fn try_reserve_computed_method_names(
        &mut self,
        groups: usize,
        sources: usize,
        keys: usize,
        tables: usize,
    ) -> bool {
        let Some(nodes) = sources.checked_add(keys) else {
            return false;
        };
        let Some(values) = groups.checked_add(keys) else {
            return false;
        };
        self.try_reserve_checker_symbol_allocations(groups, tables)
            && self.computed_method_name_groups.try_reserve(groups).is_ok()
            && self.links.late_bound.try_reserve(sources)
            && self.links.symbol_node.try_reserve(nodes)
            && self.links.type_node.try_reserve(keys)
            && self.links.value_symbol.try_reserve(values)
            && self.links.members_and_exports.try_reserve(1)
            && self.try_reserve_declared_value_provenance(keys)
    }

    /// Publishes one name while retaining each original overload symbol.
    pub(super) fn create_late_bound_method_group_symbol(
        &mut self,
        prepared: PreparedComputedMethodNameGroup,
        members: SymbolTableId,
    ) -> Option<SemanticSymbolId> {
        let PreparedComputedMethodNameGroup {
            owner,
            key_type,
            sources,
            declarations,
            keys,
            flags,
            name,
            existing,
        } = prepared;
        let first = *sources.first()?;
        let owner_record = self.symbol(owner)?;
        let raw = owner_record.members();
        let table = self.symbol_table(members)?;
        if raw == Some(members)
            || table.get(name.as_ref()) != existing
            || self.get_merged_symbol(owner) != Some(owner)
            || !self.source_merged_symbol_declarations_match(owner)
            || raw.is_none() && !self.source_symbol_has_only_computed_members(owner)
            || raw.is_some_and(|raw| {
                self.symbol_table(raw).is_none_or(|raw| {
                    raw.iter()
                        .any(|(name, source)| table.get(name) != Some(source))
                })
            })
        {
            return None;
        }
        for ((&source, &declaration), key) in sources.iter().zip(&declarations).zip(keys.iter()) {
            let early = self.symbol(source)?;
            if early.flags() != flags
                || !self.source_symbol_declarations_match(source)
                || self.source_declaration_symbol(declaration) != Some(source)
                || self.get_parent_of_symbol(source) != Some(owner)
                || self
                    .late_bound_links(source)
                    .and_then(|links| links.late_symbol)
                    != existing
                || self
                    .symbol_node_links(declaration)
                    .and_then(|links| links.resolved_symbol)
                    != existing
                || self.symbol_node_links(key.expression)?.resolved_symbol != Some(key.key_symbol)
                || self.type_node_links(key.expression)?.resolved_type != Some(key_type)
                || super::object_members::resolved_computed_member_key(self, key).ok()??
                    != (key_type, name.clone())
            {
                return None;
            }
        }
        if let Some(late) = existing {
            return (self.late_bound_method_sources(late).as_deref() == Some(sources.as_ref())
                && self.value_symbol_links(late)?.name_type == Some(key_type))
            .then_some(late);
        }
        if sources.len() == 1 {
            return self.create_late_bound_property_symbol(owner, first, key_type, members);
        }
        let first_declaration = declarations[0];
        let late = self.alloc_transient_symbol(flags, name.clone(), CheckFlags::LATE);
        assert!(self.set_symbol_declarations(late, Some(declarations), Some(first_declaration)));
        assert!(self.set_symbol_relationships(late, None, None, Some(owner), None));
        assert!(self.set_value_symbol_links(
            late,
            ValueSymbolLinks {
                name_type: Some(key_type),
                ..ValueSymbolLinks::default()
            }
        ));
        for &source in &sources {
            let declaration = self
                .symbol(source)
                .and_then(Symbol::value_declaration)
                .expect("computed method source was prevalidated");
            assert!(self.set_late_bound_links(
                source,
                LateBoundLinks {
                    late_symbol: Some(late)
                }
            ));
            assert!(self.set_symbol_node_links(
                declaration,
                SymbolNodeLinks {
                    resolved_symbol: Some(late)
                }
            ));
        }
        assert!(
            self.computed_method_name_groups
                .insert(
                    late,
                    ComputedMethodNameGroup {
                        owner,
                        key_type,
                        key_symbol: keys[0].key_symbol,
                        sources,
                    },
                )
                .is_none()
        );
        assert_eq!(self.insert_symbol(members, name, late), Some(None));
        Some(late)
    }

    /// Publishes ordered source-planned direct-base edges exactly once.
    ///
    /// Callers stage the edge list and reserve the map slot before mutation.
    /// Every declared-type link is authoritative by the time heritage members
    /// resolve. The first base may be a canonical reference to its declared
    /// interface. Each later distinct base must be a resolved, nongeneric
    /// property-only interface. Repeated bases require the exact nongeneric
    /// source sequence. More than two edges require nongeneric identities.
    #[allow(clippy::too_many_lines)] // Keep every edge proof before the single publication.
    pub(super) fn publish_direct_interface_heritage_provenance(
        &mut self,
        type_: TypeId,
        provenance: DirectInterfaceHeritageProvenance,
    ) -> bool {
        let Some(&(first_symbol, first_type)) = provenance.bases.first() else {
            return false;
        };
        let owner_is_exact = self.type_payload(type_).is_some_and(|record| {
            matches!(record.data(), TypeData::Interface(_))
                && record.symbol() == Some(provenance.owner_symbol)
        }) && self.get_merged_symbol(provenance.owner_symbol)
            == Some(provenance.owner_symbol)
            && self
                .declared_type_links(provenance.owner_symbol)
                .is_some_and(|links| links.declared_type == Some(type_));
        let base_is_exact = self.get_merged_symbol(first_symbol) == Some(first_symbol)
            && self
                .declared_type_links(first_symbol)
                .and_then(|links| links.declared_type)
                .is_some_and(|target| {
                    self.type_payload(target).is_some_and(|record| {
                        matches!(record.data(), TypeData::Interface(_))
                            && record.symbol() == Some(first_symbol)
                    }) && (target == first_type
                        || super::reference_types::validate_direct_generic_reference(
                            self, first_type,
                        )
                        .is_ok_and(|reference| reference.target == target))
                });
        if provenance.owner_symbol == first_symbol || !owner_is_exact || !base_is_exact {
            return false;
        }
        if provenance.bases.len() > 2
            && std::iter::once(type_)
                .chain(provenance.bases.iter().map(|(_, base)| *base))
                .any(|type_| {
                    !super::structured_members::nongeneric_interface_heritage_type_is_exact(
                        self, type_,
                    )
                })
        {
            return false;
        }
        let mut distinct_bases = HashMap::from([(first_symbol, first_type)]);
        let mut distinct_types = HashSet::from([first_type]);
        let mut has_repeated_base = false;
        for &(base_symbol, base_type) in provenance.bases.iter().skip(1) {
            if let Some(previous) = distinct_bases.get(&base_symbol) {
                if *previous != base_type
                    || base_type == type_
                    || self
                        .declared_type_links(base_symbol)
                        .is_none_or(|links| links.declared_type != Some(base_type))
                {
                    return false;
                }
                has_repeated_base = true;
                continue;
            }
            let distinct_base_is_exact = base_symbol != provenance.owner_symbol
                && base_symbol != first_symbol
                && base_type != type_
                && base_type != first_type
                && self.get_merged_symbol(base_symbol) == Some(base_symbol)
                && self
                    .declared_type_links(base_symbol)
                    .is_some_and(|links| links.declared_type == Some(base_type))
                && self.type_payload(base_type).is_some_and(|record| {
                    let TypeData::Interface(interface) = record.data() else {
                        return false;
                    };
                    let structured = &interface.reference.object.structured;
                    record.flags() == TypeFlags::OBJECT
                        && record.object_flags()
                            == super::types::ObjectFlags::INTERFACE
                                | super::types::ObjectFlags::MEMBERS_RESOLVED
                        && record.symbol() == Some(base_symbol)
                        && record.alias().is_none()
                        && self.symbol(base_symbol).is_some_and(|symbol| {
                            (symbol.flags() == SymbolFlags::INTERFACE
                                || super::object_members::authenticated_nongeneric_global_interface_owner(
                                    self,
                                    base_symbol,
                                ))
                                && symbol.members() == interface.declared_members
                        })
                        && interface.all_type_parameters.is_none()
                        && interface.outer_type_parameter_count == 0
                        && interface.this_type.is_none()
                        && interface.reference.object.target.is_none()
                        && interface.reference.object.mapper.is_none()
                        && interface.reference.object.instantiations == TypeCacheState::Unallocated
                        && interface.reference.node.is_none()
                        && interface.reference.resolved_type_arguments.is_none()
                        && interface.base_types_resolved
                        && interface.declared_members_resolved
                        && interface.resolved_base_constructor_type.is_none()
                        && interface.declared_call_signatures.is_none()
                        && interface.declared_construct_signatures.is_none()
                        && interface.declared_index_infos.is_none()
                        && structured.signatures.is_none()
                        && structured.call_signature_count == 0
                        && structured.index_infos.is_none()
                });
            if !distinct_base_is_exact || !distinct_types.insert(base_type) {
                return false;
            }
            distinct_bases.insert(base_symbol, base_type);
        }
        if has_repeated_base
            && super::structured_members::repeated_nongeneric_interface_base_nodes(
                self,
                provenance.owner_symbol,
                provenance.bases.iter().map(|(symbol, _)| *symbol),
            )
            .is_none_or(|nodes| nodes.len() != provenance.bases.len())
        {
            return false;
        }
        let std::collections::hash_map::Entry::Vacant(entry) =
            self.direct_interface_heritage_provenance.entry(type_)
        else {
            return false;
        };
        entry.insert(provenance);
        if self.relation_type_is_observable(type_) {
            self.mark_relation_inputs_dirty();
        }
        true
    }
}

impl<MapperPayload> SemanticStore<TypeRecord, MapperPayload> {
    pub(super) fn try_reserve_direct_class_heritage_provenance(
        &mut self,
        additional: usize,
    ) -> bool {
        self.direct_class_heritage_provenance
            .try_reserve(additional)
            .is_ok()
    }

    fn source_callable_interface_return_proof_has_exact_owner(
        &self,
        proof: SourceCallableInterfaceReturnProof,
    ) -> bool {
        let signature = proof.signature();
        let declaration = proof.declaration();
        let owner = proof.owner_symbol();
        let annotation = proof.annotation();
        let target = proof.target_symbol();
        let Some(type_) = self.source_callable_type_for_signature(signature) else {
            return false;
        };
        let Some(provenance) = self.source_callable_provenance(type_) else {
            return false;
        };
        proof.has_direct_reference()
            && provenance.signature == signature
            && provenance.declaration == declaration
            && provenance.owner_symbol == owner
            && provenance.return_provenance == SourceCallableReturnProvenance::Annotated
            && provenance.contextual_target.is_none()
            && provenance.contextual_variable.is_none()
            && self.source_callable_type_for_owner(owner) == Some(type_)
            && self.source_callable_type_for_declaration(declaration) == Some(type_)
            && self.get_merged_symbol(owner) == Some(owner)
            && self.type_payload(type_).is_some_and(|record| {
                record.flags() == TypeFlags::OBJECT
                    && record.symbol() == Some(owner)
                    && record.alias().is_none()
                    && matches!(record.data(), TypeData::Object(_))
            })
            && self.value_symbol_links(owner)
                == Some(&ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
            && self
                .source_node_kind(declaration)
                .is_some_and(|kind| provenance.family.matches_syntax_kind(kind))
            && self.signature(signature).is_some_and(|record| {
                record.declaration() == Some(declaration)
                    && record.flags() == provenance.flags
                    && record.target().is_none()
                    && record.mapper().is_none()
            })
            && self
                .signature_links(declaration)
                .and_then(|links| links.resolved_signature.signature())
                == Some(signature)
            && self.function_signature_return_annotation(signature) == Some((annotation, false))
            && self.source_node_kind(annotation) == Some(SyntaxKind::TypeReference)
            && self.source_node_parent(annotation) == Some(SourceNodeParent::Parent(declaration))
            && self.source_return_annotation_belongs_to(declaration, annotation)
            && self.get_merged_symbol(target) == Some(target)
            && self.symbol(target).is_some_and(|record| {
                record.flags().contains(SymbolFlags::INTERFACE)
                    && !record.flags().contains(SymbolFlags::CLASS)
            })
    }

    fn source_callable_interface_return_proof_matches_published_type(
        &self,
        proof: SourceCallableInterfaceReturnProof,
    ) -> bool {
        let Some(return_type) = self
            .signature(proof.signature())
            .and_then(Signature::resolved_return_type)
        else {
            return false;
        };
        !self.signature_has_circular_return_type(proof.signature())
            && self.source_direct_type_annotation_is_exact(proof.annotation(), return_type)
            && self
                .declared_type_links(proof.target_symbol())
                .and_then(|links| links.declared_type)
                == Some(return_type)
            && self.type_payload(return_type).is_some_and(|record| {
                record.flags() == TypeFlags::OBJECT
                    && record.symbol() == Some(proof.target_symbol())
                    && record.object_flags().contains(ObjectFlags::INTERFACE)
                    && !record.object_flags().contains(ObjectFlags::CLASS)
                    && matches!(record.data(), TypeData::Interface(_))
            })
    }

    /// Reserves one proof slot without replacing an existing proof or repairing caches.
    pub(super) fn try_reserve_source_callable_interface_return_proof(
        &mut self,
        proof: SourceCallableInterfaceReturnProof,
    ) -> bool {
        if !self.source_callable_interface_return_proof_has_exact_owner(proof) {
            return false;
        }
        if let Some(existing) = self.source_callable_interface_return_proof(proof.signature()) {
            return existing == proof
                && self.source_callable_interface_return_proof_matches_published_type(proof);
        }
        if self
            .signature(proof.signature())
            .and_then(Signature::resolved_return_type)
            .is_some()
            && !self.source_callable_interface_return_proof_matches_published_type(proof)
        {
            return false;
        }
        self.source_callable_interface_return_proofs
            .try_reserve(1)
            .is_ok()
    }

    /// Publishes only the proof whose annotation and interface return are already checked.
    pub(super) fn publish_source_callable_interface_return_proof(
        &mut self,
        proof: SourceCallableInterfaceReturnProof,
    ) -> bool {
        if !self.source_callable_interface_return_proof_has_exact_owner(proof)
            || !self.source_callable_interface_return_proof_matches_published_type(proof)
        {
            return false;
        }
        let signature = proof.signature();
        if let Some(existing) = self.source_callable_interface_return_proof(signature) {
            return existing == proof;
        }
        if self.source_callable_interface_return_proofs.len()
            == self.source_callable_interface_return_proofs.capacity()
        {
            return false;
        }
        let relation_dirty = self.relation_signature_is_observable(signature)
            || self
                .relation_observable_nodes
                .contains(&proof.declaration())
            || self.relation_observable_nodes.contains(&proof.annotation())
            || self
                .relation_observable_symbols
                .contains(&proof.owner_symbol())
            || self
                .relation_observable_symbols
                .contains(&proof.target_symbol())
            || self
                .source_callable_type_for_signature(signature)
                .is_some_and(|type_| self.relation_type_is_observable(type_));
        self.source_callable_interface_return_proofs
            .insert(signature, proof);
        if relation_dirty {
            self.mark_relation_inputs_dirty();
        }
        self.mark_union_cache_validation_dirty();
        true
    }

    pub(super) fn constructor_annotation_binding(
        &self,
        reference: NodeRef,
    ) -> Option<SemanticSymbolId> {
        self.observe_relation_node_read(reference);
        self.constructor_annotation_bindings
            .get(&reference)
            .copied()
    }

    #[cfg(test)]
    pub(super) fn constructor_annotation_binding_count(&self) -> usize {
        self.constructor_annotation_bindings.len()
    }

    pub(super) fn try_reserve_constructor_annotation_bindings(
        &mut self,
        proof: &ConstructorAnnotationProof,
    ) -> bool {
        if !proof.bindings().all(|(reference, symbol)| {
            self.source_node_kind(reference) == Some(SyntaxKind::TypeReference)
                && self.get_merged_symbol(symbol) == Some(symbol)
                && self
                    .constructor_annotation_bindings
                    .get(&reference)
                    .is_none_or(|&existing| existing == symbol)
        }) {
            return false;
        }
        let missing = proof
            .bindings()
            .filter(|(reference, _)| !self.constructor_annotation_bindings.contains_key(reference))
            .count();
        self.constructor_annotation_bindings
            .try_reserve(missing)
            .is_ok()
    }

    /// Records source bindings from a checked plan. Existing bindings cannot change.
    pub(super) fn publish_constructor_annotation_bindings(
        &mut self,
        proof: &ConstructorAnnotationProof,
    ) -> bool {
        if !proof.bindings().all(|(reference, symbol)| {
            self.source_node_kind(reference) == Some(SyntaxKind::TypeReference)
                && self.get_merged_symbol(symbol) == Some(symbol)
                && self.symbol_node_links(reference)
                    == Some(&SymbolNodeLinks {
                        resolved_symbol: Some(symbol),
                    })
                && self.type_node_links(reference).is_some_and(|links| {
                    links.resolved_type.is_some() && links.outer_type_parameters.is_none()
                })
                && self
                    .constructor_annotation_bindings
                    .get(&reference)
                    .is_none_or(|&existing| existing == symbol)
        }) {
            return false;
        }
        let missing = proof
            .bindings()
            .filter(|(reference, _)| !self.constructor_annotation_bindings.contains_key(reference))
            .count();
        if missing
            > self.constructor_annotation_bindings.capacity()
                - self.constructor_annotation_bindings.len()
        {
            return false;
        }
        let mut observable = false;
        for (reference, symbol) in proof.bindings() {
            if self
                .constructor_annotation_bindings
                .insert(reference, symbol)
                .is_none()
            {
                observable |= self.relation_observable_nodes.contains(&reference);
            }
        }
        if missing != 0 {
            self.mark_union_cache_validation_dirty();
        }
        if observable {
            self.mark_relation_inputs_dirty();
        }
        true
    }

    pub(super) fn try_reserve_source_class_provenance(&mut self, additional: usize) -> bool {
        self.source_class_provenance.try_reserve(additional).is_ok()
            && self
                .source_classes_by_symbol
                .try_reserve(additional)
                .is_ok()
    }

    pub(super) fn source_class_provenance(
        &self,
        instance: TypeId,
    ) -> Option<&SourceClassProvenance> {
        self.observe_relation_type_read(instance);
        self.source_class_provenance.get(&instance)
    }

    pub(super) fn source_class_provenance_for_symbol(
        &self,
        symbol: SemanticSymbolId,
    ) -> Option<&SourceClassProvenance> {
        self.observe_relation_symbol_read(symbol);
        self.source_classes_by_symbol
            .get(&symbol)
            .and_then(|instance| self.source_class_provenance(*instance))
    }

    pub(super) fn publish_source_class_provenance(
        &mut self,
        instance: TypeId,
        provenance: SourceClassProvenance,
    ) -> bool {
        let symbol = provenance.symbol();
        if provenance.instance_type() != instance
            || self.types.get(instance).is_none()
            || self
                .source_classes_by_symbol
                .get(&symbol)
                .is_some_and(|existing| *existing != instance)
        {
            return false;
        }
        match self.source_class_provenance.entry(instance) {
            std::collections::hash_map::Entry::Occupied(entry) => entry.get() == &provenance,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(provenance);
                self.source_classes_by_symbol.insert(symbol, instance);
                self.mark_relation_inputs_dirty();
                self.mark_union_cache_validation_dirty();
                true
            }
        }
    }

    pub(super) fn source_class_provenance_mut(
        &mut self,
        instance: TypeId,
    ) -> Option<&mut SourceClassProvenance> {
        self.mark_relation_inputs_dirty();
        self.mark_union_cache_validation_dirty();
        self.source_class_provenance.get_mut(&instance)
    }

    pub(super) fn class_instance_super_view(
        &self,
        reference: TypeId,
    ) -> Option<ClassInstanceSuperView> {
        self.observe_relation_type_read(reference);
        self.class_instance_super_views.get(&reference).copied()
    }

    pub(super) fn class_instance_super_view_for_instance(
        &self,
        instance: TypeId,
    ) -> Option<ClassInstanceSuperView> {
        self.observe_relation_type_read(instance);
        self.class_instance_super_views_by_instance
            .get(&instance)
            .and_then(|reference| self.class_instance_super_view(*reference))
    }

    pub(super) fn try_reserve_class_instance_super_views(&mut self) -> bool {
        self.class_instance_super_views.try_reserve(1).is_ok()
            && self
                .class_instance_super_views_by_instance
                .try_reserve(1)
                .is_ok()
    }

    pub(super) fn publish_class_instance_super_view(
        &mut self,
        view: ClassInstanceSuperView,
    ) -> bool {
        let reference = view.receiver_type();
        let instance = view.instance_type();
        if self.types.get(reference).is_none()
            || self.types.get(instance).is_none()
            || self
                .class_instance_super_views_by_instance
                .get(&instance)
                .is_some_and(|current| *current != reference)
        {
            return false;
        }
        match self.class_instance_super_views.entry(reference) {
            std::collections::hash_map::Entry::Occupied(entry) => entry.get() == &view,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(view);
                self.class_instance_super_views_by_instance
                    .insert(instance, reference);
                self.mark_relation_inputs_dirty();
                self.mark_union_cache_validation_dirty();
                true
            }
        }
    }

    pub(super) fn class_instance_super_member(
        &self,
        view: TypeId,
        member: SemanticSymbolId,
    ) -> Option<&ClassInstanceSuperMember> {
        self.observe_relation_type_read(view);
        self.observe_relation_symbol_read(member);
        self.class_instance_super_members.get(&(view, member))
    }

    pub(super) fn class_instance_super_member_for_type(
        &self,
        type_: TypeId,
    ) -> Option<&ClassInstanceSuperMember> {
        self.observe_relation_type_read(type_);
        self.class_instance_super_members
            .values()
            .find(|member| member.type_() == type_ && member.is_instantiated_callable())
    }

    pub(super) fn try_reserve_class_instance_super_members(&mut self) -> bool {
        self.class_instance_super_members.try_reserve(1).is_ok()
    }

    pub(super) fn publish_class_instance_super_member(
        &mut self,
        member: ClassInstanceSuperMember,
    ) -> bool {
        if !self.class_instance_super_views.contains_key(&member.view())
            || self.symbol(member.member()).is_none()
            || self.types.get(member.type_()).is_none()
        {
            return false;
        }
        match self
            .class_instance_super_members
            .entry((member.view(), member.member()))
        {
            std::collections::hash_map::Entry::Occupied(entry) => entry.get() == &member,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(member);
                self.mark_relation_inputs_dirty();
                self.mark_union_cache_validation_dirty();
                true
            }
        }
    }

    pub(super) fn direct_class_heritage_provenance(
        &self,
        instance_type: TypeId,
    ) -> Option<DirectClassHeritageProvenance> {
        self.observe_relation_type_read(instance_type);
        self.direct_class_heritage_provenance
            .get(&instance_type)
            .copied()
    }

    /// Publishes the exact instance/value split selected by one direct class
    /// heritage plan. All five identities must already be authoritative.
    pub(super) fn publish_direct_class_heritage_provenance(
        &mut self,
        instance_type: TypeId,
        provenance: DirectClassHeritageProvenance,
    ) -> bool {
        let exact_class_instance = |store: &Self, type_: TypeId, symbol: SemanticSymbolId| {
            store.type_payload(type_).is_some_and(|record| {
                matches!(record.data(), TypeData::Interface(_))
                    && record
                        .object_flags()
                        .contains(super::types::ObjectFlags::CLASS)
                    && record
                        .object_flags()
                        .contains(super::types::ObjectFlags::REFERENCE)
                    && record.symbol() == Some(symbol)
            }) && store.get_merged_symbol(symbol) == Some(symbol)
                && store
                    .declared_type_links(symbol)
                    .is_some_and(|links| links.declared_type == Some(type_))
        };
        let exact_class_value = |store: &Self, type_: TypeId, symbol: SemanticSymbolId| {
            store.type_payload(type_).is_some_and(|record| {
                matches!(record.data(), TypeData::Object(_))
                    && record
                        .object_flags()
                        .contains(super::types::ObjectFlags::ANONYMOUS)
                    && record.symbol() == Some(symbol)
            }) && store.value_symbol_links(symbol).is_some_and(|links| {
                links
                    == &(ValueSymbolLinks {
                        resolved_type: Some(type_),
                        ..ValueSymbolLinks::default()
                    })
            })
        };
        if provenance.owner_symbol == provenance.base_symbol
            || !exact_class_instance(self, instance_type, provenance.owner_symbol)
            || !exact_class_value(self, provenance.owner_value_type, provenance.owner_symbol)
            || !exact_class_instance(self, provenance.base_instance_type, provenance.base_symbol)
            || !exact_class_value(self, provenance.base_value_type, provenance.base_symbol)
        {
            return false;
        }
        let std::collections::hash_map::Entry::Vacant(entry) =
            self.direct_class_heritage_provenance.entry(instance_type)
        else {
            return false;
        };
        entry.insert(provenance);
        if self.relation_type_is_observable(instance_type) {
            self.mark_relation_inputs_dirty();
        }
        true
    }
}

impl SemanticStore<TypeRecord, super::mapper::TypeMapper> {
    /// Publishes the type, signature, generic metadata, provenance reverse
    /// maps, owner barrier, optional return annotation, and signature link as
    /// one prevalidated transaction.
    ///
    /// No semantic identity or cache is mutated until every dependency and
    /// capacity has been checked. After the first allocation, all remaining
    /// writes are assertions over that frozen preflight.
    pub(super) fn publish_source_generic_callable(
        &mut self,
        prepared: PreparedSourceGenericCallablePublication<'_>,
    ) -> Option<(TypeId, SignatureId)> {
        let next_signature_local =
            NonZeroU32::new(u32::try_from(self.signature_len().checked_add(1)?).ok()?)?;
        let next_signature =
            <SignatureId as super::ids::ArenaId>::from_parts(self.id(), next_signature_local);
        if self
            .source_callable_type_queries
            .contains_key(&next_signature)
        {
            return None;
        }
        let ordinary_arrow = prepared.family == SourceCallableFamily::ArrowFunction
            && self.source_arrow_has_ordinary_type_parameters(prepared.declaration);
        if prepared.syntax.is_ordinary_typescript_arrow() != ordinary_arrow
            || ordinary_arrow && prepared.return_annotation.is_none()
        {
            return None;
        }
        let query_required = (prepared.family == SourceCallableFamily::FunctionDeclaration
            || ordinary_arrow)
            && prepared.return_annotation.is_some()
            && !prepared.type_parameters.is_empty();
        if query_required != prepared.query_evidence.is_some() {
            return None;
        }
        let resolution_states = match prepared.query_evidence.as_deref() {
            Some(evidence) => {
                self.validate_source_generic_query_publication(&prepared, evidence)?
            }
            None => self.validate_source_generic_type_parameters(
                prepared.syntax,
                prepared.declaration,
                &prepared.type_parameters,
            )?,
        };
        let generic_return_type_parameter_valid = query_required
            || self.source_generic_return_type_parameter_is_exact(
                prepared.syntax,
                prepared.return_annotation,
                prepared.generic_return_type_parameter,
                &prepared.type_parameters,
                prepared.array_targets,
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
            && (prepared.family != SourceCallableFamily::ArrowFunction
                || owner.name() == InternalSymbolName::Function.as_ref()
                    && prepared.owner_parent.is_none()
                    && prepared.export_local.is_none())
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
        let return_annotation_valid = match prepared.return_annotation {
            Some(annotation) => {
                !prepared.syntax.inferred_empty_body_is_exact()
                    && self.source_return_annotation_belongs_to(prepared.declaration, annotation)
            }
            None => {
                prepared.syntax.inferred_empty_body_is_exact()
                    && !prepared.return_null_literal_identity
                    && prepared.generic_return_type_parameter.is_none()
                    && self
                        .intrinsic_bootstrap
                        .as_ref()
                        .is_some_and(|bootstrap| self.types.get(bootstrap.void_type).is_some())
            }
        };
        let mut alias_nodes = HashSet::new();
        let mut alias_owners = HashSet::new();
        let alias_annotations_valid = prepared.syntax.alias_annotations().iter().all(|alias| {
            alias_nodes.insert(alias.annotation())
                && alias_owners.insert(alias.owner())
                && alias.source_is_exact(self)
                && !self
                    .source_callable_alias_annotations
                    .contains_key(&alias.annotation())
                && !self
                    .source_callable_alias_owners
                    .contains_key(&alias.owner())
                && (prepared.return_annotation == Some(alias.owner_annotation())
                    || prepared.parameters.iter().any(|parameter| {
                        self.symbol(*parameter)
                            .and_then(Symbol::value_declaration)
                            .is_some_and(|declaration| {
                                self.source_return_annotation_belongs_to(
                                    declaration,
                                    alias.owner_annotation(),
                                )
                            })
                    }))
                && (alias.owner() == prepared.owner_symbol && alias.has_cold_value(self)
                    || prepared
                        .syntax
                        .alias_resolutions()
                        .iter()
                        .any(|resolution| resolution.proof() == alias && resolution.is_exact(self)))
        });
        let alias_resolutions_valid =
            prepared
                .syntax
                .alias_resolutions()
                .iter()
                .all(|resolution| {
                    prepared
                        .syntax
                        .alias_annotations()
                        .contains(resolution.proof())
                        && resolution.is_exact(self)
                        && resolution.parameters().iter().copied().eq(prepared
                            .type_parameters
                            .iter()
                            .map(|parameter| parameter.provenance.type_parameter))
                });
        let has_rest_parameter = if query_required {
            prepared.flags.contains(SignatureFlags::HAS_REST_PARAMETER)
        } else {
            prepared.flags == SignatureFlags::HAS_REST_PARAMETER
        };
        let flags_valid = if query_required {
            prepared.flags.bits()
                & !(SignatureFlags::HAS_REST_PARAMETER | SignatureFlags::HAS_LITERAL_TYPES).bits()
                == 0
        } else {
            prepared.flags == SignatureFlags::NONE || has_rest_parameter
        };
        let minimum_argument_count_valid =
            usize::try_from(prepared.min_argument_count).is_ok_and(|minimum| {
                minimum
                    <= prepared
                        .parameters
                        .len()
                        .saturating_sub(usize::from(has_rest_parameter))
            });
        let owner_links_cold = self
            .value_symbol_links(prepared.owner_symbol)
            .is_none_or(|links| links == &ValueSymbolLinks::default());
        let signature_links_cold = self
            .signature_links(prepared.declaration)
            .is_none_or(|links| links == &SignatureLinks::default());
        let source_family_matches = matches!(
            (prepared.family, self.source_node_kind(prepared.declaration)),
            (
                SourceCallableFamily::FunctionDeclaration,
                Some(SyntaxKind::FunctionDeclaration)
            ) | (
                SourceCallableFamily::ArrowFunction,
                Some(SyntaxKind::ArrowFunction)
            )
        );
        if prepared.type_parameters.is_empty()
            || prepared.syntax.declaration() != prepared.declaration
            || !source_family_matches
            || !flags_valid
            || has_rest_parameter
                && (prepared.family != SourceCallableFamily::FunctionDeclaration
                    || prepared.parameters.is_empty()
                    || prepared.array_targets.is_none())
            || !minimum_argument_count_valid
            || !owner_valid
            || !export_route_valid
            || !parameters_valid
            || !owner_links_cold
            || !signature_links_cold
            || !return_annotation_valid
            || !alias_annotations_valid
            || !alias_resolutions_valid
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
            || self.source_callable_type_queries.values().any(|evidence| {
                evidence.callable().declaration == prepared.declaration
                    || evidence.callable().owner_symbol == prepared.owner_symbol
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
        let alias_annotations = prepared.syntax.alias_annotations().to_vec();
        let alias_resolutions = prepared.syntax.alias_resolutions().to_vec();
        let type_parameter_ids = prepared
            .type_parameters
            .iter()
            .map(|row| row.provenance.type_parameter)
            .collect::<Vec<_>>();
        let value_link_reservations = prepared.parameters.len().checked_add(1)?;
        if !self.try_reserve_types(1)
            || !self.try_reserve_signatures(1)
            || !self.try_reserve_source_callable_provenance(1)
            || !self.try_reserve_function_signature_return_annotations(usize::from(
                prepared.return_annotation.is_some(),
            ))
            || !self.links.signature.try_reserve(1)
            || !self.links.value_symbol.try_reserve(value_link_reservations)
            || self
                .source_callable_alias_annotations
                .try_reserve(alias_annotations.len())
                .is_err()
            || self
                .source_callable_alias_owners
                .try_reserve(alias_annotations.len())
                .is_err()
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
        if let Some(evidence) = prepared.query_evidence {
            assert!(
                self.source_callable_type_queries
                    .insert(signature, evidence)
                    .is_none()
            );
        }
        for alias in alias_annotations {
            let resolution = alias_resolutions
                .iter()
                .find(|resolution| resolution.annotation() == alias.annotation())
                .cloned();
            assert!(
                self.source_callable_alias_owners
                    .insert(alias.owner(), alias.annotation())
                    .is_none()
            );
            assert!(
                self.source_callable_alias_annotations
                    .insert(alias.annotation(), (alias, resolution))
                    .is_none()
            );
        }
        let provenance = SourceCallableProvenance {
            family: prepared.family,
            declaration: prepared.declaration,
            owner_symbol: prepared.owner_symbol,
            owner_parent: prepared.owner_parent,
            export_local: prepared.export_local,
            signature,
            flags: prepared.flags,
            return_provenance: if prepared.return_annotation.is_some() {
                SourceCallableReturnProvenance::Annotated
            } else {
                SourceCallableReturnProvenance::Inferred
            },
            array_targets: prepared.array_targets,
            generic_return_type_parameter: prepared.generic_return_type_parameter,
            contextual_target: None,
            contextual_variable: None,
            captured_assignment: None,
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
        if let Some(annotation) = prepared.return_annotation {
            assert!(
                self.function_signature_return_annotations
                    .insert(
                        signature,
                        (annotation, prepared.return_null_literal_identity),
                    )
                    .is_none()
            );
        }
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

    fn validate_source_generic_query_publication(
        &self,
        prepared: &PreparedSourceGenericCallablePublication<'_>,
        evidence: &SourceCallableTypeQueryEvidence,
    ) -> Option<Vec<SourceTypeParameterResolutionState>> {
        let plan = evidence.callable();
        let expected_return_parameter = prepared
            .syntax
            .generic_return_type_parameter_declaration()
            .and_then(|declaration| {
                evidence.type_parameters().iter().find_map(|row| {
                    (row.provenance.declaration == declaration)
                        .then_some(row.provenance.type_parameter)
                })
            });
        if !plan.requires_type_query_evidence()
            || plan.family == SourceCallableFamily::ArrowFunction
                && (!plan.type_parameter_syntax.is_ordinary_typescript_arrow()
                    || plan.is_async
                    || plan.body_mode.is_ambient()
                    || plan.type_predicate.is_some()
                    || plan.parameters.iter().any(|parameter| {
                        parameter.is_implicit_any()
                            || parameter.rest
                            || parameter.initializer.is_some()
                    }))
            || !evidence.is_exact(self)
            || plan.family != prepared.family
            || plan.declaration != prepared.declaration
            || plan.owner_symbol != prepared.owner_symbol
            || plan.owner_parent != prepared.owner_parent
            || plan.export_local != prepared.export_local
            || plan.type_parameter_syntax.as_ref() != prepared.syntax
            || evidence.type_parameters() != prepared.type_parameters.as_slice()
            || evidence.base_constraints().len() != prepared.type_parameters.len()
            || !plan
                .parameters
                .iter()
                .map(|row| row.symbol)
                .eq(prepared.parameters.iter().copied())
            || plan.flags != prepared.flags
            || plan.min_argument_count != prepared.min_argument_count
            || plan.return_type.annotation_identity()
                != prepared
                    .return_annotation
                    .map(|annotation| (annotation, prepared.return_null_literal_identity))
            || plan.array_targets != prepared.array_targets
            || expected_return_parameter != prepared.generic_return_type_parameter
            || plan.type_parameters.len() != prepared.type_parameters.len()
        {
            return None;
        }
        let mut declarations = HashSet::with_capacity(prepared.type_parameters.len());
        let mut symbols = HashSet::with_capacity(prepared.type_parameters.len());
        let mut identities = HashSet::with_capacity(prepared.type_parameters.len());
        let computed = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;
        for ((planned, row), base) in plan
            .type_parameters
            .iter()
            .zip(&prepared.type_parameters)
            .zip(evidence.base_constraints())
        {
            let provenance = row.provenance;
            let record = self.type_payload(provenance.type_parameter)?;
            let TypeData::TypeParameter(data) = record.data() else {
                return None;
            };
            let symbol = self.symbol(provenance.symbol)?;
            if provenance.declaration != planned.declaration
                || provenance.symbol != planned.symbol
                || provenance.constraint != planned.constraint
                || provenance.default_type != planned.default_type
                || !declarations.insert(provenance.declaration)
                || !symbols.insert(provenance.symbol)
                || !identities.insert(provenance.type_parameter)
                || record.flags() != TypeFlags::TYPE_PARAMETER
                || record.object_flags() != ObjectFlags::NONE && record.object_flags() != computed
                || record.symbol() != Some(provenance.symbol)
                || record.alias().is_some()
                || data.is_this_type
                || data.target.is_some()
                || data.mapper.is_some()
                || data.constraint != Some(row.constraint)
                || data.resolved_default_type != Some(row.default_type)
                || data.constrained.resolved_base_constraint != Some(*base)
                || self.type_payload(row.constraint).is_none()
                || self.type_payload(row.default_type).is_none()
                || self.type_payload(*base).is_none()
                || symbol.flags() != SymbolFlags::TYPE_PARAMETER
                || symbol.check_flags() != CheckFlags::NONE
                || symbol.declarations() != Some(&[provenance.declaration])
                || symbol.value_declaration().is_some()
                || symbol.members().is_some()
                || symbol.exports().is_some()
                || symbol.parent().is_some()
                || symbol.export_symbol().is_some()
                || self.get_merged_symbol(provenance.symbol) != Some(provenance.symbol)
                || self.declared_type_links(provenance.symbol)
                    != Some(&DeclaredTypeLinks {
                        declared_type: Some(provenance.type_parameter),
                        ..DeclaredTypeLinks::default()
                    })
                || self.source_node_kind(provenance.declaration) != Some(SyntaxKind::TypeParameter)
                || self.source_node_parent(provenance.declaration)
                    != Some(SourceNodeParent::Parent(prepared.declaration))
            {
                return None;
            }
        }
        Some(vec![
            SourceTypeParameterResolutionState::Warm;
            prepared.type_parameters.len()
        ])
    }

    /// Replaces the retained query and publishes its demanded return together.
    pub(super) fn publish_source_callable_query_return(
        &mut self,
        signature: SignatureId,
        evidence: Arc<SourceCallableTypeQueryEvidence>,
        return_type: TypeId,
    ) -> bool {
        let Some(previous) = self.source_callable_type_query(signature) else {
            return false;
        };
        let plan = evidence.callable();
        let Some(return_node) = plan.return_type.type_node() else {
            return false;
        };
        let input_roots = plan
            .type_parameters
            .iter()
            .flat_map(|row| [row.constraint, row.default_type])
            .flatten()
            .chain(
                plan.parameters
                    .iter()
                    .filter_map(|row| row.explicit_type_node()),
            );
        if !plan.requires_type_query_evidence()
            || !previous.matches_plan(plan)
            || !previous.is_exact(self)
            || !evidence.is_exact(self)
            || previous.type_parameters() != evidence.type_parameters()
            || previous.base_constraints() != evidence.base_constraints()
            || input_roots.into_iter().any(|root| {
                previous.annotation_type(root).is_none()
                    || previous.annotation_type(root) != evidence.annotation_type(root)
            })
            || evidence.annotation_type(return_node) != Some(return_type)
            || previous
                .annotation_type(return_node)
                .is_some_and(|old| old != return_type)
            || self.type_payload(return_type).is_none()
            || self.signature_has_circular_return_type(signature)
            || self
                .checked_source_callable_return_type(signature)
                .is_some()
            || !super::source_callables::validate_lazy_source_callable_return(self, plan, signature)
                .is_ok_and(|resolved| resolved.is_none())
        {
            return false;
        }
        let previous = self
            .source_callable_type_queries
            .insert(signature, evidence);
        assert!(
            previous.is_some(),
            "the queried source signature was prevalidated"
        );
        let published = self.set_signature_resolved_return_type(signature, Some(return_type));
        assert!(published, "the queried source return was prevalidated");
        true
    }
}

impl<MapperPayload> SemanticStore<TypeRecord, MapperPayload> {
    fn source_generic_return_type_parameter_is_exact(
        &self,
        syntax: &SourceCallableTypeParameterSyntaxProof,
        annotation: Option<NodeRef>,
        return_type_parameter: Option<TypeId>,
        resolved: &[ResolvedSourceCallableTypeParameter],
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        let Some(annotation) = annotation else {
            return syntax.inferred_empty_body_is_exact()
                && !syntax.generic_fixed_return_is_exact()
                && syntax.generic_return_type_parameter_declaration().is_none()
                && return_type_parameter.is_none();
        };
        if syntax.inferred_empty_body_is_exact() {
            return false;
        }
        match (
            syntax.generic_return_type_parameter_declaration(),
            return_type_parameter,
            syntax.generic_fixed_return_is_exact(),
        ) {
            (None, None, true) => {
                syntax
                    .alias_annotations()
                    .iter()
                    .any(|alias| alias.annotation() == annotation && alias.source_is_exact(self))
                    || self.source_node_kind(annotation) != Some(SyntaxKind::TypeReference)
                    || self.source_named_generic_return_annotation_is_exact(
                        annotation,
                        resolved,
                        syntax.alias_annotations(),
                        array_targets,
                    )
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

    fn source_named_generic_return_annotation_is_exact(
        &self,
        annotation: NodeRef,
        resolved: &[ResolvedSourceCallableTypeParameter],
        aliases: &[SourceCallableAliasAnnotation],
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        if self.source_node_kind(annotation) != Some(SyntaxKind::TypeReference) {
            return false;
        }
        let symbol_links = self.symbol_node_links(annotation);
        let type_links = self.type_node_links(annotation);
        let cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default())
            && type_links.is_none_or(|links| links == &TypeNodeLinks::default());
        if !cold {
            return type_links
                .and_then(|links| links.resolved_type)
                .is_some_and(|result| {
                    self.source_named_generic_type_reference_with_arguments_is_exact(
                        annotation,
                        result,
                        |argument, expected| {
                            self.source_generic_return_argument_is_exact(
                                argument,
                                Some(expected),
                                resolved,
                                aliases,
                                array_targets,
                            )
                        },
                    )
                });
        }

        let Some(facts) = self.source_node_facts.get(&annotation.arena) else {
            return false;
        };
        let mut names = 0usize;
        let mut arguments = 0usize;
        for (index, child) in facts.iter().enumerate() {
            let Some(child) = child else {
                continue;
            };
            if child.parent != Some(annotation.node) {
                continue;
            }
            if child.kind == SyntaxKind::Identifier {
                names += 1;
                continue;
            }
            let Some(index) = u32::try_from(index).ok() else {
                return false;
            };
            let argument = NodeRef::new(annotation.arena, annotation.file, NodeId::new(index));
            if !self.source_generic_return_argument_is_exact(
                argument,
                None,
                resolved,
                aliases,
                array_targets,
            ) {
                return false;
            }
            arguments += 1;
        }

        names == 1 && arguments != 0
    }

    fn source_generic_return_argument_is_exact(
        &self,
        annotation: NodeRef,
        expected: Option<TypeId>,
        resolved: &[ResolvedSourceCallableTypeParameter],
        aliases: &[SourceCallableAliasAnnotation],
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        let symbol_links = self.symbol_node_links(annotation);
        let type_links = self.type_node_links(annotation);
        if expected.is_some_and(|expected| {
            type_links
                != Some(&TypeNodeLinks {
                    resolved_type: Some(expected),
                    outer_type_parameters: None,
                })
        }) {
            return false;
        }
        if let Some(alias) = aliases
            .iter()
            .find(|alias| alias.annotation() == annotation)
        {
            let parameters = resolved
                .iter()
                .map(|row| row.provenance.type_parameter)
                .collect::<Vec<_>>();
            return alias.source_is_exact(self)
                && (expected.is_none() && alias.has_cold_value(self)
                    || alias.snapshot(self, &parameters).is_some_and(|snapshot| {
                        expected.is_none_or(|expected| expected == snapshot.result())
                            && self.source_callable_alias_resolution_matches(alias, &snapshot)
                    }));
        }
        let symbol_cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default());
        let cold = symbol_cold && type_links.is_none_or(|links| links == &TypeNodeLinks::default());
        let Some(children) = self.source_direct_children(annotation) else {
            return false;
        };
        match self.source_node_kind(annotation) {
            Some(SyntaxKind::TypeReference) => {
                if matches!(children.as_slice(), [name]
                    if self.source_node_kind(*name) == Some(SyntaxKind::Identifier))
                {
                    cold || resolved.iter().any(|row| {
                        symbol_links
                            == Some(&SymbolNodeLinks {
                                resolved_symbol: Some(row.provenance.symbol),
                            })
                            && type_links
                                == Some(&TypeNodeLinks {
                                    resolved_type: Some(row.provenance.type_parameter),
                                    outer_type_parameters: None,
                                })
                    })
                } else {
                    self.source_named_generic_return_annotation_is_exact(
                        annotation,
                        resolved,
                        aliases,
                        array_targets,
                    )
                }
            }
            Some(SyntaxKind::ArrayType) => {
                let (Some(targets), [element]) = (array_targets, children.as_slice()) else {
                    return false;
                };
                if cold {
                    return self.source_generic_return_argument_is_exact(
                        *element,
                        None,
                        resolved,
                        aliases,
                        array_targets,
                    );
                }
                let Some(result) = type_links.and_then(|links| links.resolved_type) else {
                    return false;
                };
                let Some(record) = self.type_payload(result) else {
                    return false;
                };
                let TypeData::TypeReference(reference) = record.data() else {
                    return false;
                };
                let Some([element_type]) = reference.resolved_type_arguments.as_deref() else {
                    return false;
                };
                let Some(target) = self.type_payload(targets.array_type()) else {
                    return false;
                };
                let TypeData::Interface(interface) = target.data() else {
                    return false;
                };
                let TypeCacheState::Allocated(instantiations) =
                    &interface.reference.object.instantiations
                else {
                    return false;
                };
                symbol_cold
                    && type_links
                        == Some(&TypeNodeLinks {
                            resolved_type: Some(result),
                            outer_type_parameters: None,
                        })
                    && record.flags() == TypeFlags::OBJECT
                    && record.object_flags().contains(ObjectFlags::REFERENCE)
                    && record.symbol() == target.symbol()
                    && target.symbol().is_some()
                    && target.flags() == TypeFlags::OBJECT
                    && target
                        .object_flags()
                        .contains(ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
                    && record.alias().is_none()
                    && reference.object.target == Some(targets.array_type())
                    && reference.object.mapper.is_none()
                    && reference.node.is_none()
                    && instantiations.get(&type_list_key(&[*element_type])) == Some(&result)
                    && self.source_generic_return_argument_is_exact(
                        *element,
                        Some(*element_type),
                        resolved,
                        aliases,
                        array_targets,
                    )
            }
            Some(SyntaxKind::MappedType) => {
                let Some(syntax) = source_generic_index_map_syntax(self, annotation) else {
                    return false;
                };
                if cold {
                    return self.source_generic_return_argument_is_exact(
                        syntax.template,
                        None,
                        resolved,
                        aliases,
                        array_targets,
                    );
                }
                let parameters = resolved
                    .iter()
                    .map(|row| row.provenance.type_parameter)
                    .collect::<Vec<_>>();
                type_links
                    .and_then(|links| links.resolved_type)
                    .is_some_and(|result| {
                        valid_source_generic_index_map(self, annotation, result, &parameters)
                    })
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
            let compatible_constraint_default_pair = provenance.constraint.is_none()
                || provenance.default_type.is_none()
                || source_type_parameter_default_is_assignable(
                    self,
                    row.constraint,
                    row.default_type,
                );
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
                || !compatible_constraint_default_pair
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
                    } else if self.source_direct_constraint_has_leaf_base(
                        row.constraint,
                        provenance.constraint,
                    ) {
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

    fn source_direct_constraint_has_leaf_base(
        &self,
        constraint: TypeId,
        annotation: Option<NodeRef>,
    ) -> bool {
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
            || annotation.is_some_and(|node| {
                self.source_fixed_string_tuple_result_is_exact(node, constraint)
                    || self.source_named_interface_keyof_result_is_exact(node, constraint)
                    || self.source_recovered_unresolved_type_reference_is_exact(node, constraint)
                    || self.source_named_generic_type_reference_is_exact(node, constraint, &[])
            })
    }

    fn source_fixed_string_tuple_result_is_exact(&self, node: NodeRef, result: TypeId) -> bool {
        let Some(string) = self
            .intrinsic_bootstrap
            .as_ref()
            .map(|bootstrap| bootstrap.string_type)
        else {
            return false;
        };
        let Some(record) = self.type_payload(result) else {
            return false;
        };
        let TypeData::TypeReference(reference) = record.data() else {
            return false;
        };
        let Some(target) = reference.object.target else {
            return false;
        };
        let Some(TypeData::Tuple(tuple)) = self.type_payload(target).map(TypeRecord::data) else {
            return false;
        };
        let Some((key, provenance)) = self.canonical_tuple_target_for_type(target) else {
            return false;
        };
        let [element] = tuple.metadata.element_infos() else {
            return false;
        };
        let TypeCacheState::Allocated(instantiations) =
            &tuple.interface.reference.object.instantiations
        else {
            return false;
        };
        let Some(TypeData::TypeParameter(this)) = tuple
            .interface
            .this_type
            .and_then(|this| self.type_payload(this))
            .map(TypeRecord::data)
        else {
            return false;
        };
        if self.source_node_kind(node) != Some(SyntaxKind::TupleType)
            || self.type_node_links(node)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(result),
                    outer_type_parameters: None,
                })
            || self
                .symbol_node_links(node)
                .is_some_and(|links| links != &SymbolNodeLinks::default())
            || record.flags() != TypeFlags::OBJECT
            || record.symbol().is_some()
            || record.alias().is_some()
            || reference.object.mapper.is_some()
            || reference.object.instantiations != TypeCacheState::Unallocated
            || reference.node.is_some()
            || reference.resolved_type_arguments.as_deref() != Some(&[string])
            || provenance.target != target
            || key.element_infos.as_slice() != tuple.metadata.element_infos()
            || key.readonly
            || instantiations.get(&type_list_key(&[string])) != Some(&result)
            || element.flags() != ElementFlags::REQUIRED
            || element.labeled_declaration().is_some()
            || tuple.metadata.min_length() != 1
            || tuple.metadata.fixed_length() != 1
            || tuple.metadata.is_readonly()
            || this.constraint != Some(target)
            || this
                .constrained
                .resolved_base_constraint
                .is_some_and(|base| base != target)
        {
            return false;
        }

        let Some(facts) = self.source_node_facts.get(&node.arena) else {
            return false;
        };
        let mut children = facts.iter().enumerate().filter_map(|(index, facts)| {
            facts
                .as_ref()
                .filter(|facts| facts.parent == Some(node.node))
                .map(|facts| (index, facts))
        });
        let Some((index, child)) = children.next() else {
            return false;
        };
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        child.kind == SyntaxKind::StringKeyword
            && children.next().is_none()
            && self.source_type_node_result_is_exact(
                NodeRef::new(node.arena, node.file, NodeId::new(index)),
                string,
                &[],
            )
    }

    /// Authenticates an instantiated interface, class, or alias annotation.
    /// Arguments must match their source nodes and previously resolved generics.
    pub(super) fn source_named_generic_type_reference_is_exact(
        &self,
        node: NodeRef,
        result: TypeId,
        earlier: &[ResolvedSourceCallableTypeParameter],
    ) -> bool {
        self.source_named_generic_type_reference_with_arguments_is_exact(
            node,
            result,
            |node, result| self.source_type_node_result_is_exact(node, result, earlier),
        )
    }

    fn source_named_generic_type_reference_with_arguments_is_exact(
        &self,
        node: NodeRef,
        result: TypeId,
        mut validate_argument: impl FnMut(NodeRef, TypeId) -> bool,
    ) -> bool {
        if self.source_node_kind(node) != Some(SyntaxKind::TypeReference)
            || self.type_node_links(node)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(result),
                    outer_type_parameters: None,
                })
        {
            return false;
        }
        let Some(owner) = self
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
        else {
            return false;
        };
        if self.symbol_node_links(node)
            != Some(&SymbolNodeLinks {
                resolved_symbol: Some(owner),
            })
            || self.get_merged_symbol(owner) != Some(owner)
        {
            return false;
        }
        let Some(owner_record) = self.symbol(owner) else {
            return false;
        };
        if owner_record.check_flags() != CheckFlags::NONE
            || owner_record.declarations().is_none_or(|declarations| {
                declarations.is_empty()
                    || declarations.iter().any(|declaration| {
                        !matches!(
                            self.source_node_kind(*declaration),
                            Some(
                                SyntaxKind::InterfaceDeclaration
                                    | SyntaxKind::ClassDeclaration
                                    | SyntaxKind::TypeAliasDeclaration
                            )
                        )
                    })
            })
        {
            return false;
        }

        let Some(record) = self.type_payload(result) else {
            return false;
        };
        let arguments = if owner_record
            .flags()
            .intersects(SymbolFlags::INTERFACE | SymbolFlags::CLASS)
        {
            let Some(target) = self
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
            else {
                return false;
            };
            let Some(target_record) = self.type_payload(target) else {
                return false;
            };
            let TypeData::Interface(target_interface) = target_record.data() else {
                return false;
            };
            let reference = match record.data() {
                TypeData::TypeReference(reference) => reference,
                TypeData::Interface(interface) if result == target => &interface.reference,
                _ => return false,
            };
            let Some(arguments) = reference.resolved_type_arguments.as_deref() else {
                return false;
            };
            let TypeCacheState::Allocated(instantiations) =
                &target_interface.reference.object.instantiations
            else {
                return false;
            };
            if record.flags() != TypeFlags::OBJECT
                || !record.object_flags().contains(ObjectFlags::REFERENCE)
                || record.symbol() != Some(owner)
                || record.alias().is_some()
                || target_record.symbol() != Some(owner)
                || !target_record
                    .object_flags()
                    .intersects(ObjectFlags::CLASS | ObjectFlags::INTERFACE)
                || reference.object.target != Some(target)
                || reference.object.mapper.is_some()
                || reference.node.is_some()
                || arguments.is_empty()
                || instantiations.get(&type_list_key(arguments)) != Some(&result)
            {
                return false;
            }
            arguments
        } else if owner_record.flags().contains(SymbolFlags::TYPE_ALIAS) {
            let Some(alias) = record.alias().and_then(|alias| self.type_alias(alias)) else {
                return false;
            };
            let Some(arguments) = alias.type_arguments() else {
                return false;
            };
            if alias.symbol() != Some(owner) || arguments.is_empty() {
                return false;
            }
            arguments
        } else {
            return false;
        };

        let Some(facts) = self.source_node_facts.get(&node.arena) else {
            return false;
        };
        let mut name_count = 0usize;
        let mut argument_count = 0usize;
        for (index, facts) in facts.iter().enumerate() {
            let Some(facts) = facts else {
                continue;
            };
            if facts.parent != Some(node.node) {
                continue;
            }
            if facts.kind == SyntaxKind::Identifier {
                name_count += 1;
                continue;
            }
            let Some(expected) = arguments.get(argument_count).copied() else {
                return false;
            };
            let Some(index) = u32::try_from(index).ok() else {
                return false;
            };
            let argument = NodeRef::new(node.arena, node.file, NodeId::new(index));
            if !validate_argument(argument, expected) {
                return false;
            }
            argument_count += 1;
        }

        name_count == 1 && argument_count == arguments.len()
    }

    /// Authenticates the cached error result for an unresolved generic bound.
    pub(super) fn source_recovered_unresolved_type_reference_is_exact(
        &self,
        node: NodeRef,
        result: TypeId,
    ) -> bool {
        let Some(bootstrap) = self.intrinsic_bootstrap.as_ref() else {
            return false;
        };
        let Some(SourceNodeParent::Parent(parameter)) = self.source_node_parent(node) else {
            return false;
        };
        let Some(identifier_index) = node
            .node
            .index()
            .checked_sub(1)
            .and_then(|index| u32::try_from(index).ok())
        else {
            return false;
        };
        let identifier = NodeRef::new(node.arena, node.file, NodeId::new(identifier_index));
        result == bootstrap.error_type
            && self.source_node_kind(node) == Some(SyntaxKind::TypeReference)
            && self.source_node_kind(parameter) == Some(SyntaxKind::TypeParameter)
            && self.source_node_kind(identifier) == Some(SyntaxKind::Identifier)
            && self.source_node_parent(identifier) == Some(SourceNodeParent::Parent(node))
            && self.type_node_links(node)
                == Some(&TypeNodeLinks {
                    resolved_type: Some(result),
                    outer_type_parameters: None,
                })
            && self
                .symbol_node_links(node)
                .is_none_or(|links| links == &SymbolNodeLinks::default())
            && self
                .symbol_node_links(identifier)
                .is_none_or(|links| links == &SymbolNodeLinks::default())
    }

    fn source_named_interface_keyof_result_is_exact(&self, node: NodeRef, result: TypeId) -> bool {
        let Some(facts) = self.source_node_fact(node) else {
            return false;
        };
        if facts.kind != SyntaxKind::TypeOperator
            || facts.type_operator != Some(SyntaxKind::KeyOfKeyword)
            || self.type_node_links(node)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(result),
                    outer_type_parameters: None,
                })
            || self
                .symbol_node_links(node)
                .is_some_and(|links| links != &SymbolNodeLinks::default())
        {
            return false;
        }

        let Some(operand_index) = node
            .node
            .index()
            .checked_sub(1)
            .and_then(|index| u32::try_from(index).ok())
        else {
            return false;
        };
        let operand = NodeRef::new(node.arena, node.file, NodeId::new(operand_index));
        if self.source_node_kind(operand) != Some(SyntaxKind::TypeReference)
            || self.source_node_parent(operand) != Some(SourceNodeParent::Parent(node))
        {
            return false;
        }
        let Some(target) = self
            .type_node_links(operand)
            .filter(|links| links.outer_type_parameters.is_none())
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        let Some(owner) = self
            .symbol_node_links(operand)
            .and_then(|links| links.resolved_symbol)
        else {
            return false;
        };
        let Some(record) = self.type_payload(target) else {
            return false;
        };
        let TypeData::Interface(interface) = record.data() else {
            return false;
        };
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
            || record.alias().is_some()
            || record
                .symbol()
                .and_then(|symbol| self.get_merged_symbol(symbol))
                != Some(owner)
            || self.get_merged_symbol(owner) != Some(owner)
            || self
                .symbol(owner)
                .is_none_or(|symbol| symbol.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE)
            || self
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                != Some(target)
        {
            return false;
        }
        let structured = &interface.reference.object.structured;
        let Some(member_table) = structured.members else {
            return false;
        };
        let Some(members) = self.symbol_table(member_table) else {
            return false;
        };
        let Some(properties) = structured.properties.as_deref() else {
            return false;
        };
        if properties.is_empty()
            || properties.len() != members.len()
            || self.symbol(owner).and_then(Symbol::members) != Some(member_table)
            || !interface.base_types_resolved
            || !interface.declared_members_resolved
            || interface.declared_members != Some(member_table)
            || interface.resolved_base_types.is_some()
            || interface.resolved_base_constructor_type.is_some()
            || interface.declared_call_signatures.is_some()
            || interface.declared_construct_signatures.is_some()
            || interface.declared_index_infos.is_some()
            || structured.signatures.is_some()
            || structured.call_signature_count != 0
            || structured.index_infos.is_some()
        {
            return false;
        }

        let key = PropertiesTypeCacheKey::new(
            target,
            TypeFlags::STRING_LIKE | TypeFlags::NUMBER_LIKE | TypeFlags::ES_SYMBOL_LIKE,
            true,
            record
                .object_flags()
                .intersects(ObjectFlags::UNRESOLVED_MEMBERS),
        );
        if self.cached_properties_type(key) != Some(result) {
            return false;
        }

        let Some(bootstrap) = self.intrinsic_bootstrap.as_ref() else {
            return false;
        };
        let mut keys = Vec::with_capacity(properties.len());
        for property in properties {
            let Some(symbol) = self.symbol(*property) else {
                return false;
            };
            let Some(name) = symbol.name().as_utf8() else {
                return false;
            };
            let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
            if !symbol.flags().contains(SymbolFlags::PROPERTY)
                || symbol.flags().without(allowed_flags) != SymbolFlags::NONE
                || symbol
                    .parent()
                    .and_then(|parent| self.get_merged_symbol(parent))
                    != Some(owner)
                || members.get_source(name) != Some(*property)
                || self.get_merged_symbol(*property) != Some(*property)
            {
                return false;
            }
            let Some(literal) = bootstrap.cached_string_literal_type(name) else {
                return false;
            };
            let Some(literal_record) = self.type_payload(literal) else {
                return false;
            };
            let TypeData::Literal(value) = literal_record.data() else {
                return false;
            };
            if literal_record.flags() != TypeFlags::STRING_LITERAL
                || literal_record.symbol().is_some()
                || literal_record.alias().is_some()
                || value.regular_type != literal
                || !matches!(&value.value, LiteralValue::String(value) if value == name)
                || keys.contains(&literal)
            {
                return false;
            }
            keys.push(literal);
        }

        if let [only] = keys.as_slice() {
            result == *only
        } else {
            let Some(result_record) = self.type_payload(result) else {
                return false;
            };
            let TypeData::Union(union) = result_record.data() else {
                return false;
            };
            let Some(origin) = union.origin else {
                return false;
            };
            let Some(origin_record) = self.type_payload(origin) else {
                return false;
            };
            let TypeData::Index(index) = origin_record.data() else {
                return false;
            };
            result_record.flags() == TypeFlags::UNION
                && result_record.symbol().is_none()
                && result_record.alias().is_none()
                && union.union.types.len() == keys.len()
                && keys.iter().all(|key| union.union.types.contains(key))
                && origin_record.flags() == TypeFlags::INDEX
                && origin_record.object_flags() == ObjectFlags::NONE
                && origin_record.symbol().is_none()
                && origin_record.alias().is_none()
                && index.target == target
                && index.index_flags == IndexFlags::NONE
        }
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

        if kind == Some(SyntaxKind::TupleType) {
            return self.source_fixed_string_tuple_result_is_exact(node, result);
        }

        if kind == Some(SyntaxKind::TypeOperator) {
            return self.source_named_interface_keyof_result_is_exact(node, result);
        }

        if kind == Some(SyntaxKind::LiteralType) {
            if self.type_node_links(node)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(result),
                    outer_type_parameters: None,
                })
                || self
                    .symbol_node_links(node)
                    .is_some_and(|links| links != &SymbolNodeLinks::default())
            {
                return false;
            }
            let Some(literal_index) = node.node.index().checked_sub(1) else {
                return false;
            };
            let Some(literal) = self
                .source_node_facts
                .get(&node.arena)
                .and_then(|facts| facts.get(literal_index))
                .and_then(Option::as_ref)
            else {
                return false;
            };
            if literal.parent != Some(node.node) {
                return false;
            }
            let (literal_kind, negative) = if literal.kind == SyntaxKind::PrefixUnaryExpression {
                if literal.prefix_unary_operator != Some(SyntaxKind::MinusToken) {
                    return false;
                }
                let Some(operand_index) = literal_index.checked_sub(1) else {
                    return false;
                };
                let Some(operand) = self
                    .source_node_facts
                    .get(&node.arena)
                    .and_then(|facts| facts.get(operand_index))
                    .and_then(Option::as_ref)
                else {
                    return false;
                };
                if operand.parent.map(NodeId::index) != Some(literal_index) {
                    return false;
                }
                (operand.kind, true)
            } else {
                (literal.kind, false)
            };
            let Some(record) = self.type_payload(result) else {
                return false;
            };
            let TypeData::Literal(data) = record.data() else {
                return false;
            };
            if record.object_flags() != super::types::ObjectFlags::NONE
                || record.symbol().is_some()
                || record.alias().is_some()
                || data.regular_type != result
            {
                return false;
            }
            let (expected_kind, expected_flags, cached) = match &data.value {
                LiteralValue::String(value) if !negative => (
                    SyntaxKind::StringLiteral,
                    TypeFlags::STRING_LITERAL,
                    bootstrap.cached_string_literal_type(value),
                ),
                LiteralValue::Number(value)
                    if value.value() == 0.0 || value.value().is_sign_negative() == negative =>
                {
                    (
                        SyntaxKind::NumericLiteral,
                        TypeFlags::NUMBER_LITERAL,
                        bootstrap.cached_number_literal_type(*value),
                    )
                }
                LiteralValue::BigInt(value)
                    if value.negative == negative || value.base10_value.is_empty() =>
                {
                    (
                        SyntaxKind::BigIntLiteral,
                        TypeFlags::BIG_INT_LITERAL,
                        bootstrap.cached_bigint_literal_type(value),
                    )
                }
                LiteralValue::Boolean(true) if !negative => (
                    SyntaxKind::TrueKeyword,
                    TypeFlags::BOOLEAN_LITERAL,
                    Some(bootstrap.regular_true_type),
                ),
                LiteralValue::Boolean(false) if !negative => (
                    SyntaxKind::FalseKeyword,
                    TypeFlags::BOOLEAN_LITERAL,
                    Some(bootstrap.regular_false_type),
                ),
                _ => return false,
            };
            return literal_kind == expected_kind
                && record.flags() == expected_flags
                && cached == Some(result);
        }

        // Except for the fixed tuple above, the source proof does not retain
        // enough structure to authenticate aliases or composite type syntax.
        // Earlier type parameters are proven by both canonical query links.
        if kind != Some(SyntaxKind::TypeReference) {
            return false;
        }
        if self.source_recovered_unresolved_type_reference_is_exact(node, result) {
            return true;
        }
        if self.source_named_generic_type_reference_is_exact(node, result, earlier) {
            return true;
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

    pub(super) fn source_return_annotation_belongs_to(
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

    pub(super) fn is_signature_return_resolving(&self, signature: SignatureId) -> bool {
        self.signature(signature)
            .is_some_and(|record| record.resolved_return_type().is_none())
            && self
                .type_resolutions
                .find_cycle_start_index(
                    TypeResolutionTarget::Signature(signature),
                    TypeSystemPropertyName::ResolvedReturnType,
                    |target, property| {
                        canonical_resolution_has_property_readonly(
                            &self.links,
                            &self.types,
                            &self.signatures,
                            target,
                            property,
                        )
                    },
                )
                .is_ok_and(|index| index.is_some())
    }

    pub(super) fn is_signature_return_inference_active(&self, signature: SignatureId) -> bool {
        self.type_resolutions.contains(
            TypeResolutionTarget::Signature(signature),
            TypeSystemPropertyName::ResolvedReturnType,
        )
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

fn canonical_resolution_has_property_readonly(
    links: &CheckerLinkStores,
    types: &TypedArena<TypeId, TypeRecord>,
    signatures: &SignatureArena,
    target: TypeResolutionTarget,
    property: TypeSystemPropertyName,
) -> bool {
    match (target, property) {
        (TypeResolutionTarget::Symbol(symbol), TypeSystemPropertyName::Type) => links
            .value_symbol
            .try_get(&symbol)
            .is_some_and(|links| links.resolved_type.is_some()),
        (TypeResolutionTarget::Symbol(symbol), TypeSystemPropertyName::DeclaredType) => links
            .type_alias
            .try_get(&symbol)
            .is_some_and(|links| links.declared_type.is_some()),
        (TypeResolutionTarget::Symbol(symbol), TypeSystemPropertyName::WriteType) => links
            .value_symbol
            .try_get(&symbol)
            .is_some_and(|links| links.write_type.is_some()),
        (TypeResolutionTarget::Symbol(symbol), TypeSystemPropertyName::AliasTarget) => links
            .alias_symbol
            .try_get(&symbol)
            .is_some_and(|links| links.alias_target.has_property()),
        (TypeResolutionTarget::Type(type_id), property) => types
            .get(type_id)
            .and_then(|record| canonical_type_resolution_property(record.data(), property))
            .unwrap_or(false),
        (
            TypeResolutionTarget::Signature(signature),
            TypeSystemPropertyName::ResolvedReturnType,
        ) => signatures
            .get(signature)
            .is_some_and(|record| record.resolved_return_type().is_some()),
        (TypeResolutionTarget::Node(node), TypeSystemPropertyName::InitializerIsUndefined) => {
            links.node.try_get(&node).is_some_and(|links| {
                links
                    .flags
                    .contains(super::links::NodeCheckFlags::INITIALIZER_IS_UNDEFINED_COMPUTED)
            })
        }
        _ => false,
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
    use std::collections::{HashMap, HashSet};

    use ts_ast::{
        FileId, IdentifierData, Node, NodeArena, NodeData, NodeFlags, NodeId, NodeRef,
        QualifiedNameData, SyntaxKind,
    };
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, CheckFlags, EscapedName,
        InternalSymbolName, SymbolData, SymbolFlags, SymbolStore,
    };
    use ts_core::TextRange;
    use ts_parser::{parse_isolated_entity_name, parse_source_file};

    use super::{
        AstScope, CachedSignatureLookup, PlainInterfaceBaseFacts, PlainInterfaceHeritageFacts,
        SemanticStore, type_list_key,
    };
    use crate::semantic::{
        AccessibleChainCacheKey, AliasSymbolLinks, AliasTargetState, ArrayLiteralLinks,
        AssertionLinks, CacheHashKey, CanonicalCheckerContext, CanonicalCheckerOptions,
        CanonicalTypeMapperStore, ContainingSymbolLinks, DeclaredTypeHost, DeclaredTypeLinks,
        DecoratorSignatureState, DeferredSymbolLinks, EffectsSignatureState, EntityNameNode,
        EnumMemberLinks, EvaluatorResult, EvaluatorValue, ExhaustiveState, ExportTypeLinks,
        ExtendedContainersState, ExternalEmitHelpers, IntrinsicBootstrapOptions, JsxElementLinks,
        JsxFlags, LateBoundLinks, MappedSymbolLinks, MarkedAssignmentSymbolLinks,
        MembersAndExportsLinks, ModuleSymbolLinks, NodeCheckFlags, NodeLinks,
        OptionalSymbolSequence, OrderedNodeSet, RelationComparisonResult, RelationKind,
        ResolvedSignatureState, ReverseMappedSymbolLinks, SignatureLinks, SourceFileLinks,
        SpreadLinks, SwitchStatementLinks, SymbolNodeLinks, SymbolReferenceLinks, TypeAliasLinks,
        TypeData, TypeNodeLinks, TypeRecord, TypeResolutionTarget, TypeSystemPropertyName,
        ValueSymbolLinks, VarianceFlags, VarianceLinks,
        bootstrap::UnionReduction,
        declared::execute_type_parameter,
        production::GlobalMergeCompletion,
        reference_types::create_direct_generic_reference,
        signatures::{ElementFlags, SignatureFlags, TypePredicateKind},
        source_callables::plan_source_callable,
        types::{ObjectFlags, TypeFlags},
    };
    use ts_jsnum::{Number, PseudoBigInt};

    type TestStore = SemanticStore<&'static str, &'static str>;
    type CanonicalTestStore = SemanticStore<TypeRecord, &'static str>;

    #[test]
    fn published_interface_method_origin_misses_are_observed_and_test_writes_invalidate() {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let type_ = store.intrinsic_bootstrap().unwrap().number_type;
        let signature = empty_signature(&mut store);
        let key = CacheHashKey::from_halves(43, 47);
        for reverse in [false, true] {
            let observation = store.begin_relation_read_observation().unwrap();
            assert!(store.published_interface_method_origin(type_).is_none());
            assert_eq!(
                store.published_interface_method_type_for_signature(signature),
                None
            );
            assert!(store.commit_relation_cache_writes(
                observation,
                RelationKind::Assignable,
                [(key, RelationComparisonResult::SUCCEEDED)],
            ));
            assert!(store.relation_type_is_observable(type_));
            assert!(store.relation_signature_is_observable(signature));
            store.union_cache_needs_validation = false;

            assert!(store.try_reserve_published_interface_method_origins(1));
            assert_eq!(store.published_interface_method_origin_len(), 0);
            assert_eq!(store.published_interface_method_signature_owner_len(), 0);
            assert_eq!(
                store.relation_cache_get(RelationKind::Assignable, key),
                RelationComparisonResult::SUCCEEDED
            );
            assert!(!store.union_cache_needs_validation);

            if reverse {
                assert_eq!(
                    store.replace_published_interface_method_type_for_signature_for_test(
                        signature,
                        Some(type_),
                    ),
                    None
                );
                assert_eq!(
                    store.published_interface_method_type_for_signature(signature),
                    Some(type_)
                );
                assert_eq!(store.published_interface_method_signature_owner_len(), 1);
            } else {
                assert!(
                    store
                        .replace_published_interface_method_origin_for_test(type_, None)
                        .is_none()
                );
            }
            assert_eq!(store.published_interface_method_origin_len(), 0);
            assert_eq!(
                store.relation_cache_get(RelationKind::Assignable, key),
                RelationComparisonResult::NONE
            );
            assert!(store.union_cache_needs_validation);
            if reverse {
                assert_eq!(
                    store.replace_published_interface_method_type_for_signature_for_test(
                        signature, None,
                    ),
                    Some(type_)
                );
                assert_eq!(store.published_interface_method_signature_owner_len(), 0);
            }
        }
    }

    #[test]
    fn published_interface_method_recovery_misses_are_observed_and_test_writes_invalidate() {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let method = bootstrap.number_type;
        let callback = bootstrap.string_type;
        let observation = store.begin_relation_read_observation().unwrap();
        assert!(store.published_interface_method_recovery(method).is_none());
        assert!(
            store
                .published_interface_callback_recovery(callback)
                .is_none()
        );
        let key = CacheHashKey::from_halves(37, 41);
        assert!(store.commit_relation_cache_writes(
            observation,
            RelationKind::Assignable,
            [(key, RelationComparisonResult::SUCCEEDED)],
        ));
        assert!(store.relation_type_is_observable(method));
        assert!(store.relation_type_is_observable(callback));
        store.union_cache_needs_validation = false;

        assert!(store.try_reserve_published_interface_method_recoveries());
        assert_eq!(store.published_interface_method_recovery_len(), 0);
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, key),
            RelationComparisonResult::SUCCEEDED
        );
        assert!(!store.union_cache_needs_validation);

        assert!(
            store
                .replace_published_interface_method_recovery_for_test(method, None)
                .is_none()
        );
        assert_eq!(store.published_interface_method_recovery_len(), 0);
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, key),
            RelationComparisonResult::NONE
        );
        assert!(store.union_cache_needs_validation);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // A real inline producer checks immutable publication and restored cache ownership.
    fn inline_object_recovery_records_require_the_exact_result_and_publish_once() {
        use crate::semantic::{
            CanonicalCheckerDiagnostics,
            instantiate::{
                InstantiationLimits, InstantiationSession, instantiate_type_with_vector,
                instantiate_type_with_vector_and_session,
            },
            object_aliases::{inline_property_object_projection, property_object_alias_projection},
            type_nodes::{
                CanonicalTypeQuery, CanonicalTypeQueryOptions, type_alias_instantiation_cache_key,
            },
        };

        let parsed = parse_source_file(concat!(
            "type Left<T> = { left: T };\n",
            "type Inline<T> = { value: T } & Left<T>;\n",
            "type Other<T> = { other: T };\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(90_074);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/inline-object-recovery.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let globals = bootstrap.globals;
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let error = bootstrap.error_type;
        let locals = bound.locals(bound.source_file()).unwrap();
        let table = store.symbol_table(locals).unwrap();
        let inline_alias = table.get_source("Inline").unwrap();
        let other_alias = table.get_source("Other").unwrap();
        let declarations = table.iter().map(|(_, symbol)| symbol).collect::<Vec<_>>();
        for symbol in declarations {
            assert_eq!(store.merge_global_symbol(globals, symbol), Ok(symbol));
        }
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut query = CanonicalTypeQuery::new(
            &mut store,
            &host,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let intersection = query.get_declared_type_of_symbol(inline_alias).unwrap();
        let other = query.get_declared_type_of_symbol(other_alias).unwrap();
        let target = store
            .validate_deferred_intersection_type(intersection)
            .unwrap()
            .types[0];
        let source = inline_property_object_projection(&store, target)
            .unwrap()
            .unwrap();
        let outer = property_object_alias_projection(&store, other)
            .unwrap()
            .unwrap()
            .parameters;
        let normal =
            instantiate_type_with_vector(&mut store, target, &source.parameters, &[string])
                .unwrap();
        let intermediate =
            instantiate_type_with_vector(&mut store, target, &source.parameters, &outer).unwrap();
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 1,
                max_count: 100,
            },
            error,
        )
        .unwrap();
        let result = instantiate_type_with_vector_and_session(
            &mut store,
            intermediate,
            &outer,
            &[number],
            None,
            &mut session,
        )
        .unwrap();
        let projection = inline_property_object_projection(&store, result)
            .unwrap()
            .unwrap();
        assert_eq!(projection.arguments, [error]);
        assert_eq!(projection.target, target);
        assert_eq!(session.limit_event_count(), 1);
        assert!(store.type_payload(result).unwrap().alias().is_none());
        assert_eq!(store.inline_property_object_recoveries.len(), 1);
        assert!(store.property_object_alias_recoveries.is_empty());
        assert!(store.property_object_alias_request_recoveries.is_empty());
        assert_eq!(
            store.relation_object_instantiation(
                target,
                type_alias_instantiation_cache_key(&[error], None)
            ),
            Some(result),
        );
        let counts = |store: &CanonicalTypeMapperStore| {
            (
                [
                    store.type_len(),
                    store.type_alias_len(),
                    store.mapper_len(),
                    store.symbol_len(),
                    store.symbol_store().symbol_table_len(),
                    store.signature_len(),
                    store.index_info_len(),
                ],
                store.checker_link_allocated_lengths(),
            )
        };
        let stable = counts(&store);
        let retained = store
            .inline_property_object_recovery(result)
            .unwrap()
            .clone();
        assert!(retained.matches_current_result(&store));
        assert!(store.try_reserve_inline_property_object_recoveries());
        assert!(!store.publish_inline_property_object_recovery(retained.clone()));
        assert_eq!(store.inline_property_object_recoveries.len(), 1);
        assert_eq!(counts(&store), stable);

        let flags = store.type_payload(result).unwrap().object_flags();
        for changed in [
            flags | ObjectFlags::OBJECT_LITERAL,
            flags
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES,
        ] {
            let saved = store
                .inline_property_object_recoveries
                .remove(&result)
                .unwrap();
            assert!(store.set_type_object_flags(result, changed));
            assert!(!store.publish_inline_property_object_recovery(saved.clone()));
            assert!(store.inline_property_object_recovery(result).is_none());
            assert_eq!(counts(&store), stable);
            assert!(store.set_type_object_flags(result, flags));
            assert!(store.publish_inline_property_object_recovery(saved));
        }

        let saved = store
            .inline_property_object_recoveries
            .remove(&result)
            .unwrap();
        assert!(
            store
                .inline_property_object_recoveries
                .insert(target, saved)
                .is_none()
        );
        assert!(inline_property_object_projection(&store, target).is_err());
        assert!(inline_property_object_projection(&store, result).is_err());
        assert_eq!(counts(&store), stable);
        let saved = store
            .inline_property_object_recoveries
            .remove(&target)
            .unwrap();
        assert!(store.publish_inline_property_object_recovery(saved));

        let saved = store
            .inline_property_object_recoveries
            .remove(&result)
            .unwrap();
        let other_mapper = inline_property_object_projection(&store, normal)
            .unwrap()
            .unwrap()
            .mapper;
        assert!(store.set_object_target_and_mapper(result, Some(target), other_mapper));
        assert!(!store.publish_inline_property_object_recovery(retained.clone()));
        assert!(store.inline_property_object_recovery(result).is_none());
        assert!(inline_property_object_projection(&store, result).is_err());
        assert_eq!(counts(&store), stable);
        assert!(store.set_object_target_and_mapper(result, Some(target), projection.mapper));
        assert!(store.publish_inline_property_object_recovery(saved));

        let saved = store
            .inline_property_object_recoveries
            .remove(&result)
            .unwrap();
        let identity = store.type_payload(intersection).unwrap().alias().unwrap();
        assert!(store.set_type_alias(result, Some(identity)));
        assert!(!store.publish_inline_property_object_recovery(retained));
        assert!(store.inline_property_object_recovery(result).is_none());
        assert_eq!(counts(&store), stable);
        assert!(store.set_type_alias(result, None));
        assert!(store.publish_inline_property_object_recovery(saved));
        assert_eq!(store.inline_property_object_recoveries.len(), 1);
        assert!(
            store
                .inline_property_object_recovery(result)
                .unwrap()
                .matches_current_result(&store)
        );
        assert_eq!(
            inline_property_object_projection(&store, result)
                .unwrap()
                .unwrap(),
            projection
        );
        assert_eq!(counts(&store), stable);
        assert!(diagnostics.is_empty());
        for property in source.properties {
            assert!(store.type_node_links(property.type_node).is_none());
            assert!(store.value_symbol_links(property.symbol).is_none());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One real producer result exercises immutable storage, poisoning, and restoration.
    fn property_alias_recovery_records_require_the_exact_result_and_publish_once() {
        use crate::semantic::{
            CanonicalCheckerDiagnostics,
            instantiate::{
                InstantiationLimits, InstantiationSession, instantiate_type_with_vector_and_session,
            },
            object_aliases::property_object_alias_projection,
            type_nodes::{CanonicalTypeQuery, CanonicalTypeQueryOptions},
        };

        let parsed = parse_source_file("type Box<T>={value:T};");
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(90_071);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/property-alias-recovery.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let declaration = node_ref_of_kind(&parsed.arena, file, SyntaxKind::TypeAliasDeclaration);
        let symbol = binder.file(file).unwrap().symbol(declaration).unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let globals = bootstrap.globals;
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let error = bootstrap.error_type;
        assert_eq!(store.merge_global_symbol(globals, symbol), Ok(symbol));
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, files.get(&file).unwrap())],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let target = CanonicalTypeQuery::new(
            &mut store,
            &host,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(symbol)
        .unwrap();
        let parameters = store
            .type_alias_links(symbol)
            .unwrap()
            .type_parameters
            .clone()
            .unwrap();
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 1,
                max_count: 100,
            },
            error,
        )
        .unwrap();
        let recovered = instantiate_type_with_vector_and_session(
            &mut store,
            target,
            &parameters,
            &[string],
            None,
            &mut session,
        )
        .unwrap();
        let other = instantiate_type_with_vector_and_session(
            &mut store,
            target,
            &parameters,
            &[number],
            None,
            &mut session,
        )
        .unwrap();
        assert_ne!(recovered, other);
        assert_eq!(session.limit_event_count(), 2);
        assert_eq!(store.property_object_alias_recoveries.len(), 2);
        let projection = property_object_alias_projection(&store, recovered)
            .unwrap()
            .unwrap();
        assert_eq!(projection.arguments, [string]);
        assert_eq!(projection.identity_arguments, [error]);
        let counts = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.type_alias_len(),
                store.mapper_len(),
                store.checker_link_allocated_lengths(),
            )
        };
        let stable = counts(&store);
        let retained = store
            .property_object_alias_recovery(recovered)
            .unwrap()
            .clone();
        assert!(retained.matches_current_result(&store));
        assert!(store.try_reserve_property_object_alias_recoveries());
        assert!(!store.publish_property_object_alias_recovery(retained.clone()));
        assert_eq!(counts(&store), stable);
        assert_eq!(store.property_object_alias_recoveries.len(), 2);

        let saved = store
            .property_object_alias_recoveries
            .remove(&recovered)
            .unwrap();
        assert!(property_object_alias_projection(&store, recovered).is_err());
        assert_eq!(counts(&store), stable);
        assert!(
            store
                .property_object_alias_recoveries
                .insert(target, saved)
                .is_none()
        );
        assert!(property_object_alias_projection(&store, target).is_err());
        assert!(property_object_alias_projection(&store, recovered).is_err());
        let saved = store
            .property_object_alias_recoveries
            .remove(&target)
            .unwrap();
        assert!(
            store
                .property_object_alias_recoveries
                .insert(recovered, saved)
                .is_none()
        );
        assert_eq!(
            property_object_alias_projection(&store, recovered)
                .unwrap()
                .unwrap()
                .type_,
            recovered
        );
        assert_eq!(counts(&store), stable);

        let other_mapper = property_object_alias_projection(&store, other)
            .unwrap()
            .unwrap()
            .mapper;
        let saved = store
            .property_object_alias_recoveries
            .remove(&recovered)
            .unwrap();
        assert!(store.set_object_target_and_mapper(recovered, Some(target), other_mapper));
        assert!(!store.publish_property_object_alias_recovery(retained));
        assert!(store.property_object_alias_recovery(recovered).is_none());
        assert_eq!(counts(&store), stable);
        assert!(store.set_object_target_and_mapper(recovered, Some(target), projection.mapper));
        assert!(store.publish_property_object_alias_recovery(saved));
        assert_eq!(store.property_object_alias_recoveries.len(), 2);
        assert!(
            store
                .property_object_alias_recovery(recovered)
                .unwrap()
                .matches_current_result(&store)
        );
        assert_eq!(
            property_object_alias_projection(&store, recovered)
                .unwrap()
                .unwrap()
                .arguments,
            [string]
        );
        assert_eq!(
            property_object_alias_projection(&store, other)
                .unwrap()
                .unwrap()
                .arguments,
            [number]
        );
        assert_eq!(counts(&store), stable);
        assert!(diagnostics.is_empty());
        for property in projection.properties {
            assert!(store.type_node_links(property.type_node).is_none());
            assert!(store.value_symbol_links(property.symbol).is_none());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Two real requests share an output but keep separate immutable input records.
    fn property_alias_request_recovery_keeps_inputs_when_results_share_an_identity() {
        use crate::semantic::{
            CanonicalCheckerDiagnostics,
            global_types::initialize_global_library_types,
            instantiate::{
                InstantiationLimits, InstantiationSession, instantiate_type_with_vector_and_session,
            },
            type_nodes::{
                CanonicalTypeQuery, CanonicalTypeQueryOptions,
                cached_property_object_alias_request_matches, type_alias_instantiation_cache_key,
            },
        };

        let parsed = parse_source_file(concat!(
            "interface Object{} interface Function{} interface IArguments{} ",
            "interface String{} interface Number{} interface Boolean{} interface RegExp{} ",
            "interface Array<T>{} interface ReadonlyArray<T>{} ",
            "type Box<T>={value:T}; type Wrapped<U>=Box<U>; ",
            "declare const left:Wrapped<string>; declare const right:Wrapped<number>;",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(90_072);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/property-alias-requests.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let bound = files.get(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let globals = bootstrap.globals;
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let error = bootstrap.error_type;
        let symbols = store
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap()
            .iter()
            .map(|(_, symbol)| symbol)
            .collect::<Vec<_>>();
        for symbol in symbols {
            store.merge_global_symbol(globals, symbol).unwrap();
        }
        let alias = store
            .symbol_table(globals)
            .unwrap()
            .get_source("Wrapped")
            .unwrap();
        let nodes = parsed
            .arena
            .iter()
            .filter_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                variable
                    .type_
                    .map(|node| NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect::<Vec<_>>();
        assert_eq!(nodes.len(), 2);
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let global_types =
            initialize_global_library_types(&mut store, &host, globals, false).unwrap();
        assert!(global_types.diagnostics().is_empty());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let declared = CanonicalTypeQuery::new_with_global_types(
            &mut store,
            &host,
            &global_types,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(alias)
        .unwrap();
        let parameters = store
            .type_alias_links(alias)
            .unwrap()
            .type_parameters
            .clone()
            .unwrap();
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 1,
                max_count: 100,
            },
            error,
        )
        .unwrap();
        let mut results = Vec::new();
        for &node in &nodes {
            results.push(
                CanonicalTypeQuery::new_with_global_types_and_session(
                    &mut store,
                    &host,
                    &global_types,
                    CanonicalTypeQueryOptions::default(),
                    &mut session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_type_from_type_node(node)
                .unwrap(),
            );
        }
        assert_eq!(results[0], results[1]);
        let result = results[0];
        assert_eq!(session.query_count(), 2);
        assert_eq!(session.limit_event_count(), 4);
        assert_eq!(diagnostics.as_slice().len(), 2);
        let left_key = type_alias_instantiation_cache_key(&[string], None);
        let right_key = type_alias_instantiation_cache_key(&[number], None);
        assert_ne!(left_key, right_key);
        assert_eq!(store.property_object_alias_request_recoveries.len(), 2);
        let left = store
            .property_object_alias_request_recovery(alias, left_key)
            .unwrap()
            .clone();
        let right = store
            .property_object_alias_request_recovery(alias, right_key)
            .unwrap()
            .clone();
        assert_eq!(left.result(), result);
        assert_eq!(right.result(), result);
        assert!(left.matches_current_row(&store));
        assert!(right.matches_current_row(&store));
        let targets =
            crate::semantic::array_types::CanonicalArrayTargets::from_global_types(&global_types);
        for argument in [string, number] {
            assert_eq!(
                cached_property_object_alias_request_matches(
                    &store,
                    alias,
                    declared,
                    &parameters,
                    &[argument],
                    None,
                    result,
                    Some(targets),
                ),
                Ok(true)
            );
        }
        let normal_number = instantiate_type_with_vector_and_session(
            &mut store,
            declared,
            &parameters,
            &[number],
            Some(targets),
            &mut InstantiationSession::new(InstantiationLimits::default()),
        )
        .unwrap();
        assert_ne!(normal_number, result);
        let counts = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.type_alias_len(),
                store.mapper_len(),
                store.checker_link_allocated_lengths(),
                store.property_object_alias_recoveries.len(),
                store.property_object_alias_request_recoveries.len(),
            )
        };
        let stable = counts(&store);
        assert!(!store.publish_property_object_alias_request_recovery(left.clone()));
        assert_eq!(counts(&store), stable);
        assert_eq!(
            store
                .property_object_alias_request_recoveries
                .insert((alias, left_key), right.clone()),
            Some(left.clone())
        );
        assert!(
            cached_property_object_alias_request_matches(
                &store,
                alias,
                declared,
                &parameters,
                &[string],
                None,
                result,
                Some(targets),
            )
            .is_err()
        );
        assert!(
            CanonicalTypeQuery::new_with_global_types(
                &mut store,
                &host,
                &global_types,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(nodes[0])
            .is_err()
        );
        assert_eq!(counts(&store), stable);
        assert_eq!(
            store
                .property_object_alias_request_recoveries
                .insert((alias, left_key), left.clone()),
            Some(right)
        );
        assert_eq!(
            store
                .property_object_alias_request_recoveries
                .remove(&(alias, left_key)),
            Some(left.clone())
        );
        let missing = counts(&store);
        assert!(
            CanonicalTypeQuery::new_with_global_types(
                &mut store,
                &host,
                &global_types,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(nodes[0])
            .is_err()
        );
        assert_eq!(counts(&store), missing);
        assert!(store.publish_property_object_alias_request_recovery(left.clone()));
        assert_eq!(counts(&store), stable);
        let source_rows = store.type_alias_links(alias).cloned().unwrap();
        let saved_right = store
            .property_object_alias_request_recoveries
            .remove(&(alias, right_key))
            .unwrap();
        let missing = counts(&store);
        assert!(
            store
                .property_object_alias_recovery(result)
                .unwrap()
                .matches_current_result(&store)
        );
        assert_eq!(store.type_alias_links(alias), Some(&source_rows));
        assert!(
            crate::semantic::object_aliases::property_object_alias_projection(
                &store,
                normal_number
            )
            .is_err()
        );
        assert_eq!(counts(&store), missing);
        assert!(store.publish_property_object_alias_request_recovery(saved_right));
        assert_eq!(
            crate::semantic::object_aliases::property_object_alias_projection(
                &store,
                normal_number
            )
            .unwrap()
            .unwrap()
            .type_,
            normal_number
        );
        assert_eq!(counts(&store), stable);
        let original = store.type_alias_links(alias).cloned().unwrap();
        for replacement in [None, Some(normal_number)] {
            let mut poisoned = original.clone();
            let entries = poisoned.instantiations.as_mut().unwrap();
            if let Some(replacement) = replacement {
                assert_eq!(entries.insert(left_key, replacement), Some(result));
            } else {
                assert_eq!(entries.remove(&left_key), Some(result));
            }
            assert!(store.set_type_alias_links(alias, poisoned));
            assert!(
                cached_property_object_alias_request_matches(
                    &store,
                    alias,
                    declared,
                    &parameters,
                    &[string],
                    None,
                    result,
                    Some(targets),
                )
                .is_err()
            );
            assert!(
                CanonicalTypeQuery::new_with_global_types(
                    &mut store,
                    &host,
                    &global_types,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_type_from_type_node(nodes[0])
                .is_err()
            );
            assert_eq!(counts(&store), stable);
            assert!(store.set_type_alias_links(alias, original.clone()));
        }
        let mut warm_session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 0,
                max_count: 0,
            },
            error,
        )
        .unwrap();
        for node in nodes {
            assert_eq!(
                CanonicalTypeQuery::new_with_global_types_and_session(
                    &mut store,
                    &host,
                    &global_types,
                    CanonicalTypeQueryOptions::default(),
                    &mut warm_session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_type_from_type_node(node),
                Ok(result)
            );
        }
        assert_eq!(warm_session.total_count(), 0);
        assert_eq!(warm_session.limit_event_count(), 0);
        assert_eq!(diagnostics.as_slice().len(), 2);
        assert_eq!(counts(&store), stable);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Delete only the branded source-frame request record, then restore the same result.
    fn property_alias_branded_source_frame_requires_its_recovery_request() {
        use crate::semantic::{
            CanonicalCheckerDiagnostics,
            global_types::initialize_global_library_types,
            instantiate::{InstantiationLimits, InstantiationSession},
            object_aliases::property_object_alias_projection,
            type_nodes::{
                CanonicalTypeQuery, CanonicalTypeQueryOptions, type_alias_instantiation_cache_key,
            },
        };
        let parsed = parse_source_file(concat!(
            "interface Object{} interface Function{} interface IArguments{} ",
            "interface String{} interface Number{} interface Boolean{} interface RegExp{} ",
            "interface Array<T>{} interface ReadonlyArray<T>{} ",
            "type Box<T>={value:T}; type Wrapped<U>=Box<U>; type StringBox=Wrapped<string>;",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(90_073);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/branded-property-alias-request.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let bound = files.get(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let globals = bootstrap.globals;
        let string = bootstrap.string_type;
        let error = bootstrap.error_type;
        let symbols = store
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap()
            .iter()
            .map(|(_, symbol)| symbol)
            .collect::<Vec<_>>();
        for symbol in symbols {
            store.merge_global_symbol(globals, symbol).unwrap();
        }
        let wrapped = store
            .symbol_table(globals)
            .unwrap()
            .get_source("Wrapped")
            .unwrap();
        let alias = store
            .symbol_table(globals)
            .unwrap()
            .get_source("StringBox")
            .unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let global_types =
            initialize_global_library_types(&mut store, &host, globals, false).unwrap();
        assert!(global_types.diagnostics().is_empty());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 1,
                max_count: 100,
            },
            error,
        )
        .unwrap();
        let result = CanonicalTypeQuery::new_with_global_types_and_session(
            &mut store,
            &host,
            &global_types,
            CanonicalTypeQueryOptions::default(),
            &mut session,
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(alias)
        .unwrap();
        let projection = property_object_alias_projection(&store, result)
            .unwrap()
            .unwrap();
        assert_eq!(projection.identity_symbol, alias);
        assert!(projection.identity_arguments.is_empty());
        assert_eq!(projection.arguments, [error]);
        assert_eq!(session.total_count(), 2);
        assert_eq!(session.limit_event_count(), 1);
        let identity = store
            .symbol_store()
            .assigned_global_symbol_id(alias)
            .unwrap();
        let key = type_alias_instantiation_cache_key(&[string], Some((identity, &[])));
        let source_rows = store.type_alias_links(wrapped).cloned().unwrap();
        assert_eq!(
            source_rows.instantiations.as_ref().unwrap().get(&key),
            Some(&result)
        );
        let target_rows = match store.type_payload(projection.target).unwrap().data() {
            crate::semantic::type_records::TypeData::Object(object) => {
                object.instantiations.clone()
            }
            _ => panic!("the source Box target stays anonymous"),
        };
        let counts = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.type_alias_len(),
                store.mapper_len(),
                store.checker_link_allocated_lengths(),
                store.property_object_alias_recoveries.len(),
                store.property_object_alias_request_recoveries.len(),
            )
        };
        let stable = counts(&store);
        let saved = store
            .property_object_alias_request_recoveries
            .remove(&(wrapped, key))
            .unwrap();
        assert_eq!(saved.result(), result);
        let missing = counts(&store);
        assert!(
            store
                .property_object_alias_recovery(result)
                .unwrap()
                .matches_current_result(&store)
        );
        assert_eq!(store.type_alias_links(wrapped), Some(&source_rows));
        assert_eq!(
            match store.type_payload(projection.target).unwrap().data() {
                crate::semantic::type_records::TypeData::Object(object) => &object.instantiations,
                _ => panic!("the target identity does not change"),
            },
            &target_rows
        );
        assert!(property_object_alias_projection(&store, result).is_err());
        assert!(
            CanonicalTypeQuery::new_with_global_types(
                &mut store,
                &host,
                &global_types,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(alias)
            .is_err()
        );
        assert_eq!(counts(&store), missing);
        assert!(store.publish_property_object_alias_request_recovery(saved));
        assert_eq!(
            property_object_alias_projection(&store, result)
                .unwrap()
                .unwrap()
                .type_,
            result
        );
        assert_eq!(
            CanonicalTypeQuery::new_with_global_types(
                &mut store,
                &host,
                &global_types,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(alias),
            Ok(result)
        );
        assert_eq!(counts(&store), stable);
        assert_eq!(store.type_alias_links(wrapped), Some(&source_rows));
        assert_eq!(session.total_count(), 2);
        assert_eq!(session.limit_event_count(), 1);
        assert_eq!(diagnostics.as_slice().len(), 1);
        for property in projection.properties {
            assert!(store.type_node_links(property.type_node).is_none());
            assert!(store.value_symbol_links(property.symbol).is_none());
        }
    }

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
    fn recovered_generic_constraints_require_exact_unresolved_reference_caches() {
        let parsed = parse_source_file("function broken<T extends hm>(value: T) {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_015);
        let mut store = CanonicalTypeMapperStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let constraint = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeReference
                    && record.parent.is_some_and(|parent| {
                        parsed
                            .arena
                            .get(parent)
                            .is_some_and(|parent| parent.kind == SyntaxKind::TypeParameter)
                    }))
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .expect("the generic parameter has one unresolved constraint");
        let (error, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.error_type, bootstrap.number_type)
        };
        assert!(!store.source_recovered_unresolved_type_reference_is_exact(constraint, error));
        assert!(!store.source_type_node_result_is_exact(constraint, error, &[]));
        assert!(store.set_type_node_links(
            constraint,
            TypeNodeLinks {
                resolved_type: Some(error),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.source_recovered_unresolved_type_reference_is_exact(constraint, error));
        assert!(store.source_type_node_result_is_exact(constraint, error, &[]));
        assert!(store.source_direct_constraint_has_leaf_base(error, Some(constraint)));
        assert!(!store.source_direct_constraint_has_leaf_base(error, None));

        let forged = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_PARAMETER,
                EscapedName::source("forged"),
            ))
            .unwrap();
        assert!(store.set_symbol_node_links(
            constraint,
            SymbolNodeLinks {
                resolved_symbol: Some(forged),
            },
        ));
        assert!(!store.source_recovered_unresolved_type_reference_is_exact(constraint, error));
        assert!(store.set_symbol_node_links(constraint, SymbolNodeLinks::default()));
        assert!(store.source_recovered_unresolved_type_reference_is_exact(constraint, error));
        assert!(store.set_type_node_links(
            constraint,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(!store.source_recovered_unresolved_type_reference_is_exact(constraint, error));
        assert!(!store.source_type_node_result_is_exact(constraint, number, &[]));
    }

    #[test]
    fn contextual_callable_anchors_authenticate_variables_and_object_properties() {
        let parsed = parse_source_file(concat!(
            "const direct: (value: string) => void = value => {}; ",
            "const object = { run: value => {} };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_016);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/contextual-anchors.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let direct_arrow = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction
                    && record.parent.is_some_and(|parent| {
                        parsed
                            .arena
                            .get(parent)
                            .is_some_and(|parent| parent.kind == SyntaxKind::VariableDeclaration)
                    }))
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .expect("direct contextual variable has one arrow");
        let property = node_ref_of_kind(&parsed.arena, file, SyntaxKind::PropertyAssignment);
        let property_arrow = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction && record.parent == Some(property.node))
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .expect("object property has one direct arrow");
        let variable = NodeRef::new(
            direct_arrow.arena,
            direct_arrow.file,
            parsed.arena.get(direct_arrow.node).unwrap().parent.unwrap(),
        );
        let (direct_owner, property_owner, variable_symbol, property_symbol) = {
            let bound = binder.file(file).unwrap();
            (
                bound.symbol(direct_arrow).unwrap(),
                bound.symbol(property_arrow).unwrap(),
                bound.symbol(variable).unwrap(),
                bound.symbol(property).unwrap(),
            )
        };
        let (symbols, _) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );

        assert!(store.source_contextual_callable_anchor_is_exact(
            direct_arrow,
            direct_owner,
            variable_symbol,
        ));
        assert!(store.source_contextual_callable_anchor_is_exact(
            property_arrow,
            property_owner,
            property_symbol,
        ));
        assert!(!store.source_contextual_callable_anchor_is_exact(
            direct_arrow,
            direct_owner,
            property_symbol,
        ));
        assert!(!store.source_contextual_callable_anchor_is_exact(
            property_arrow,
            property_owner,
            property_owner,
        ));
        assert!(!store.source_contextual_callable_anchor_is_exact(
            property_arrow,
            direct_owner,
            property_symbol,
        ));

        let property_parent = store.symbol(property_symbol).unwrap().parent();
        assert!(store.set_symbol_relationships(property_symbol, None, None, None, None));
        assert!(!store.source_contextual_callable_anchor_is_exact(
            property_arrow,
            property_owner,
            property_symbol,
        ));
        assert!(
            store.set_symbol_relationships(property_symbol, None, None, property_parent, None,)
        );
        assert!(store.source_contextual_callable_anchor_is_exact(
            property_arrow,
            property_owner,
            property_symbol,
        ));
    }

    #[test]
    fn prototype_contextual_callables_reject_forged_method_and_receiver_caches() {
        for poison in 0..7 {
            let parsed = parse_source_file(concat!(
                "declare class Point { add(dx: number, dy: number): void; } ",
                "Point.prototype.add = function(dx, dy) {};",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(90_044 + poison);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/prototype-contextual-callable.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                vec![(file, &parsed.arena)],
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            context.check_source_file(file).unwrap();

            let declaration = node_ref_of_kind(&parsed.arena, file, SyntaxKind::FunctionExpression);
            let assignment = node_ref_of_kind(&parsed.arena, file, SyntaxKind::BinaryExpression);
            let NodeData::BinaryExpression(binary) =
                &parsed.arena.get(assignment.node).unwrap().data
            else {
                panic!("the prototype fixture retains one binary assignment")
            };
            let left = NodeRef::new(parsed.arena.id(), file, binary.left);
            let operator = NodeRef::new(parsed.arena.id(), file, binary.operator_token);
            let NodeData::PropertyAccessExpression(member) =
                &parsed.arena.get(left.node).unwrap().data
            else {
                panic!("the prototype fixture retains its method access")
            };
            let prototype = NodeRef::new(parsed.arena.id(), file, member.expression);
            let NodeData::PropertyAccessExpression(access) =
                &parsed.arena.get(prototype.node).unwrap().data
            else {
                panic!("the prototype fixture retains its class receiver")
            };
            let receiver = NodeRef::new(parsed.arena.id(), file, access.expression);
            let store = context.store_mut_for_test();
            let class = store
                .intrinsic_bootstrap()
                .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
                .and_then(|globals| globals.get_source("Point"))
                .unwrap();
            let method = store
                .symbol(class)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("add"))
                .unwrap();
            let method_declaration = store.symbol(method).unwrap().declarations().unwrap()[0];
            let method_signature = store
                .signature_links(method_declaration)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let method_parameter = store.signature(method_signature).unwrap().parameters()[0];
            let method_parameter_declaration = store
                .symbol(method_parameter)
                .unwrap()
                .declarations()
                .unwrap()[0];
            let callable = store
                .type_node_links(declaration)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let provenance = store.source_callable_provenance(callable).unwrap();
            let source_parameter = store.signature(provenance.signature).unwrap().parameters()[0];
            let contextual_target = provenance.contextual_target.unwrap();
            let wrong = store.intrinsic_bootstrap().unwrap().string_type;
            assert!(store.source_prototype_contextual_callable_is_exact(
                declaration,
                provenance.owner_symbol,
                provenance.signature,
                contextual_target,
            ));

            match poison {
                0 => {
                    for parameter in [method_parameter, source_parameter] {
                        assert!(store.set_value_symbol_links(
                            parameter,
                            ValueSymbolLinks {
                                resolved_type: Some(wrong),
                                ..ValueSymbolLinks::default()
                            },
                        ));
                    }
                }
                1 => {
                    for signature in [method_signature, provenance.signature] {
                        assert!(store.set_signature_resolved_return_type(signature, Some(wrong)));
                    }
                }
                2 => {
                    assert!(store.set_type_node_links(
                        receiver,
                        TypeNodeLinks {
                            resolved_type: Some(wrong),
                            ..TypeNodeLinks::default()
                        },
                    ));
                }
                3 => {
                    assert!(store.set_symbol_node_links(
                        receiver,
                        SymbolNodeLinks {
                            resolved_symbol: Some(method),
                        },
                    ));
                }
                4 => {
                    assert!(store.set_value_symbol_links(
                        class,
                        ValueSymbolLinks {
                            resolved_type: Some(wrong),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                5 => {
                    store.source_node_facts.get_mut(&operator.arena).unwrap()
                        [operator.node.index()]
                    .as_mut()
                    .unwrap()
                    .kind = SyntaxKind::PlusEqualsToken;
                }
                6 => {
                    let annotation = store
                        .source_direct_type_annotation(method_parameter_declaration)
                        .unwrap();
                    assert!(store.set_type_node_links(
                        annotation,
                        TypeNodeLinks {
                            resolved_type: Some(wrong),
                            ..TypeNodeLinks::default()
                        },
                    ));
                }
                _ => unreachable!("prototype poison cases are bounded"),
            }
            let before = (
                store.type_len(),
                store.signature_len(),
                store.source_callable_provenance_lengths(),
                store.checker_link_allocated_lengths(),
            );

            assert!(
                !store.source_prototype_contextual_callable_is_exact(
                    declaration,
                    provenance.owner_symbol,
                    provenance.signature,
                    contextual_target,
                ),
                "poison case {poison}",
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.signature_len(),
                    store.source_callable_provenance_lengths(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
                "poison case {poison}",
            );
        }
    }

    #[test]
    fn source_literal_type_results_require_canonical_values_and_exact_links() {
        let parsed = parse_source_file("type Text = 'ready'; type Numeric = 1; type Truth = true;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_002);
        let mut store = CanonicalTypeMapperStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let string = store
            .regular_string_literal_type("ready".to_owned())
            .unwrap();
        let number = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let boolean = store.intrinsic_bootstrap().unwrap().regular_true_type;
        let wrappers = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::LiteralTypeNode(literal) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    parsed.arena.get(literal.literal).unwrap().kind,
                ))
            })
            .collect::<Vec<_>>();
        for (node, kind) in &wrappers {
            let expected = match kind {
                SyntaxKind::StringLiteral => string,
                SyntaxKind::NumericLiteral => number,
                SyntaxKind::TrueKeyword => boolean,
                _ => panic!("unexpected literal kind {kind:?}"),
            };
            assert!(!store.source_type_node_result_is_exact(*node, expected, &[]));
            assert!(store.set_type_node_links(
                *node,
                TypeNodeLinks {
                    resolved_type: Some(expected),
                    outer_type_parameters: None,
                },
            ));
            assert!(store.source_type_node_result_is_exact(*node, expected, &[]));
        }

        let string_node = wrappers
            .iter()
            .find_map(|(node, kind)| (*kind == SyntaxKind::StringLiteral).then_some(*node))
            .unwrap();
        assert!(store.set_type_node_links(
            string_node,
            TypeNodeLinks {
                resolved_type: Some(number),
                outer_type_parameters: None,
            },
        ));
        assert!(!store.source_type_node_result_is_exact(string_node, number, &[]));
    }

    #[test]
    fn signed_source_literal_results_require_minus_operator_and_owned_operand() {
        let parsed = parse_source_file("type NegativeNumber = -1; type NegativeBigInt = -2n;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_003);
        let mut store = CanonicalTypeMapperStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let positive_number = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let negative_number = store
            .regular_number_literal_type(Number::new(-1.0))
            .unwrap();
        let positive_bigint = store
            .regular_bigint_literal_type(PseudoBigInt::new("2", false))
            .unwrap();
        let negative_bigint = store
            .regular_bigint_literal_type(PseudoBigInt::new("2", true))
            .unwrap();
        let signed_literals = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::LiteralTypeNode(literal) = &record.data else {
                    return None;
                };
                let prefix = parsed.arena.get(literal.literal)?;
                let NodeData::PrefixUnaryExpression(prefix_data) = &prefix.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    literal.literal,
                    prefix_data.operand,
                    parsed.arena.get(prefix_data.operand)?.kind,
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(signed_literals.len(), 2);

        for (node, _, _, kind) in &signed_literals {
            let (expected, wrong_sign) = match kind {
                SyntaxKind::NumericLiteral => (negative_number, positive_number),
                SyntaxKind::BigIntLiteral => (negative_bigint, positive_bigint),
                _ => panic!("unexpected signed literal kind {kind:?}"),
            };
            assert!(!store.source_type_node_result_is_exact(*node, expected, &[]));
            assert!(store.set_type_node_links(
                *node,
                TypeNodeLinks {
                    resolved_type: Some(expected),
                    outer_type_parameters: None,
                },
            ));
            assert!(store.source_type_node_result_is_exact(*node, expected, &[]));
            assert!(store.set_type_node_links(
                *node,
                TypeNodeLinks {
                    resolved_type: Some(wrong_sign),
                    outer_type_parameters: None,
                },
            ));
            assert!(!store.source_type_node_result_is_exact(*node, wrong_sign, &[]));
            assert!(store.set_type_node_links(
                *node,
                TypeNodeLinks {
                    resolved_type: Some(expected),
                    outer_type_parameters: None,
                },
            ));
        }

        let (number_node, prefix, operand, _) = signed_literals[0];
        store.source_node_facts.get_mut(&parsed.arena.id()).unwrap()[prefix.index()]
            .as_mut()
            .unwrap()
            .prefix_unary_operator = Some(SyntaxKind::PlusToken);
        assert!(!store.source_type_node_result_is_exact(number_node, negative_number, &[]));
        store.source_node_facts.get_mut(&parsed.arena.id()).unwrap()[prefix.index()]
            .as_mut()
            .unwrap()
            .prefix_unary_operator = Some(SyntaxKind::MinusToken);
        store.source_node_facts.get_mut(&parsed.arena.id()).unwrap()[operand.index()]
            .as_mut()
            .unwrap()
            .parent = Some(number_node.node);
        assert!(!store.source_type_node_result_is_exact(number_node, negative_number, &[]));
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

    #[test]
    fn union_order_source_ownership_preserves_global_merges_and_rejects_module_borrows() {
        let first = parse_source_file("interface Shared { first: string }");
        let second = parse_source_file("interface Shared { second: number }");
        let module = parse_source_file("export interface Shared { local: boolean }");
        let files = [
            (FileId::new(20), &first, CanonicalModuleState::Script),
            (FileId::new(3), &second, CanonicalModuleState::Script),
            (FileId::new(11), &module, CanonicalModuleState::External),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed, state) in files {
            assert!(parsed.diagnostics.is_empty());
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        state,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let declarations = files.map(|(file, parsed, _)| {
            node_ref_of_kind(&parsed.arena, file, SyntaxKind::InterfaceDeclaration)
        });
        let symbols =
            declarations.map(|node| binder.file(node.file).unwrap().symbol(node).unwrap());
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let store = context.store_mut_for_test();
        let merged = store.get_merged_symbol(symbols[0]).unwrap();
        assert_eq!(store.get_merged_symbol(symbols[1]), Some(merged));
        assert_ne!(store.get_merged_symbol(symbols[2]), Some(merged));
        assert!(store.source_declaration_belongs_to_symbol(declarations[0], merged));
        assert!(store.source_declaration_belongs_to_symbol(declarations[1], merged));
        assert!(!store.source_declaration_belongs_to_symbol(declarations[2], merged));
        assert!(store.source_declaration_belongs_to_symbol(declarations[2], symbols[2]));
        assert!(store.set_symbol_declarations(merged, Some(vec![declarations[2]]), None));
        assert!(!store.source_declaration_belongs_to_symbol(declarations[2], merged));
        let fabricated = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::INTERFACE,
                EscapedName::source("Shared"),
            ))
            .unwrap();
        assert!(store.set_symbol_declarations(fabricated, Some(vec![declarations[0]]), None));
        assert!(!store.source_declaration_belongs_to_symbol(declarations[0], fabricated));
        for (file, parsed, _) in files.into_iter().rev() {
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
        }
        for (rank, (file, _, _)) in files.into_iter().enumerate() {
            assert_eq!(store.source_file_rank(file), Some(rank));
        }
    }

    struct GlobalInterfaceMethodFixture {
        store: CanonicalTypeMapperStore,
        owner: crate::semantic::SemanticSymbolId,
        wrapper: crate::semantic::TypeId,
        method: crate::semantic::SemanticSymbolId,
        declaration: NodeRef,
        return_annotation: NodeRef,
        parameter: Option<(crate::semantic::SemanticSymbolId, NodeRef)>,
    }

    fn global_interface_method_fixture(
        global: &str,
        declaration: &str,
    ) -> GlobalInterfaceMethodFixture {
        let original = parse_source_file(&format!("interface {global} {{ {declaration} }}"));
        let augmentation = parse_source_file(&format!(
            "interface {global} {{ marker: number }} declare var {global}: any;"
        ));
        assert!(
            original.diagnostics.is_empty(),
            "{:?}",
            original.diagnostics
        );
        assert!(
            augmentation.diagnostics.is_empty(),
            "{:?}",
            augmentation.diagnostics
        );
        let first_file = FileId::new(90_010);
        let second_file = FileId::new(90_011);
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in [(first_file, &original), (second_file, &augmentation)] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/global-{}.d.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }

        let method_declaration =
            node_ref_of_kind(&original.arena, first_file, SyntaxKind::MethodSignature);
        let first_interface = node_ref_of_kind(
            &original.arena,
            first_file,
            SyntaxKind::InterfaceDeclaration,
        );
        let second_interface = node_ref_of_kind(
            &augmentation.arena,
            second_file,
            SyntaxKind::InterfaceDeclaration,
        );
        let first_bound = binder.file(first_file).unwrap();
        let first_owner = first_bound.symbol(first_interface).unwrap();
        let method = first_bound.symbol(method_declaration).unwrap();
        let NodeData::MethodSignatureDeclaration(method_data) =
            &original.arena.get(method_declaration.node).unwrap().data
        else {
            panic!("the global declaration must contain one method signature")
        };
        let return_annotation = NodeRef::new(
            original.arena.id(),
            first_file,
            method_data.type_.expect("the method has a return type"),
        );
        let parameter = method_data.parameters.nodes.first().map(|node| {
            let declaration = NodeRef::new(original.arena.id(), first_file, *node);
            let symbol = first_bound.symbol(declaration).unwrap();
            (symbol, declaration)
        });
        let second_owner = binder
            .file(second_file)
            .unwrap()
            .symbol(second_interface)
            .unwrap();

        let (symbols, _) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for (file, parsed) in [(first_file, &original), (second_file, &augmentation)] {
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            store.merge_global_symbol(globals, first_owner),
            Ok(first_owner)
        );
        let owner = store.merge_global_symbol(globals, second_owner).unwrap();
        let wrapper = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(owner))
            .unwrap();
        assert!(store.set_declared_type_links(
            owner,
            DeclaredTypeLinks {
                declared_type: Some(wrapper),
                ..DeclaredTypeLinks::default()
            },
        ));

        GlobalInterfaceMethodFixture {
            store,
            owner,
            wrapper,
            method,
            declaration: method_declaration,
            return_annotation,
            parameter,
        }
    }

    fn publish_global_interface_method_fixture(
        fixture: &mut GlobalInterfaceMethodFixture,
    ) -> (crate::semantic::TypeId, crate::semantic::SignatureId) {
        let (number, string) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let type_ = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(fixture.method))
            .unwrap();
        let signature = fixture
            .store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(fixture.declaration),
                Vec::new(),
                None,
                fixture
                    .parameter
                    .map(|(symbol, _)| vec![symbol])
                    .unwrap_or_default(),
                Some(string),
                None,
                0,
            )
            .unwrap();
        assert!(fixture.store.set_signature_links(
            fixture.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(fixture.store.set_value_symbol_links(
            fixture.method,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(fixture.store.set_structured_type_members(
            type_,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        assert!(fixture.store.set_type_node_links(
            fixture.return_annotation,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(fixture.store.set_function_signature_return_annotation(
            signature,
            fixture.return_annotation,
            false,
        ));
        if let Some((parameter, declaration)) = fixture.parameter {
            let annotation = fixture
                .store
                .source_primitive_type_annotation(declaration)
                .unwrap();
            assert!(fixture.store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(number),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(fixture.store.set_value_symbol_links(
                parameter,
                ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..ValueSymbolLinks::default()
                },
            ));
        }
        assert!(
            fixture
                .store
                .set_callable_signature_parameter_types_batch(vec![(
                    signature,
                    fixture.parameter.map(|_| vec![number]).unwrap_or_default(),
                )]),
        );
        (type_, signature)
    }

    struct InterfaceMethodFixture {
        store: CanonicalTypeMapperStore,
        owner: crate::semantic::SemanticSymbolId,
        method: crate::semantic::SemanticSymbolId,
        type_: crate::semantic::TypeId,
        declarations: Vec<NodeRef>,
        signatures: Vec<crate::semantic::SignatureId>,
        return_annotations: Vec<NodeRef>,
        parameters: Vec<crate::semantic::SemanticSymbolId>,
        parameter_types: Vec<crate::semantic::TypeId>,
    }

    fn interface_method_fixture() -> InterfaceMethodFixture {
        interface_method_fixture_with_keyword_annotation_links(true)
    }

    fn interface_method_fixture_with_keyword_annotation_links(
        publish_annotations: bool,
    ) -> InterfaceMethodFixture {
        let parsed = parse_source_file(concat!(
            "interface Contract { ",
            "run(value: string): number; ",
            "run(value: number): string; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_042);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/interface-methods.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();

        let interface = node_ref_of_kind(&parsed.arena, file, SyntaxKind::InterfaceDeclaration);
        let declarations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::MethodSignature).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        let bound = binder.file(file).unwrap();
        let owner = bound.symbol(interface).unwrap();
        let method = bound.symbol(declarations[0]).unwrap();
        let plans = declarations
            .iter()
            .copied()
            .map(|declaration| {
                let NodeData::MethodSignatureDeclaration(method) =
                    &parsed.arena.get(declaration.node).unwrap().data
                else {
                    panic!("the fixture contains only interface method signatures")
                };
                let return_annotation = NodeRef::new(
                    parsed.arena.id(),
                    file,
                    method.type_.expect("each method has a return annotation"),
                );
                let parameter_declaration =
                    NodeRef::new(parsed.arena.id(), file, method.parameters.nodes[0]);
                let NodeData::ParameterDeclaration(parameter) =
                    &parsed.arena.get(parameter_declaration.node).unwrap().data
                else {
                    panic!("each overload has one parameter")
                };
                let parameter_annotation = NodeRef::new(
                    parsed.arena.id(),
                    file,
                    parameter.type_.expect("each parameter has an annotation"),
                );
                (
                    declaration,
                    return_annotation,
                    bound.symbol(parameter_declaration).unwrap(),
                    parameter_annotation,
                )
            })
            .collect::<Vec<_>>();

        let (symbols, _) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let globals = bootstrap.globals;
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        assert_eq!(store.merge_global_symbol(globals, owner), Ok(owner));
        let interface_type = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(owner))
            .unwrap();
        assert!(store.set_declared_type_links(
            owner,
            DeclaredTypeLinks {
                declared_type: Some(interface_type),
                ..DeclaredTypeLinks::default()
            },
        ));
        let type_ = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let mut signatures = Vec::new();
        let mut return_annotations = Vec::new();
        let mut parameters = Vec::new();
        let mut parameter_types = Vec::new();

        for (declaration, return_annotation, parameter, parameter_annotation) in plans {
            let return_type = match store.source_node_kind(return_annotation) {
                Some(SyntaxKind::StringKeyword) => string,
                Some(SyntaxKind::NumberKeyword) => number,
                _ => panic!("method return annotations are primitive"),
            };
            let parameter_type = match store.source_node_kind(parameter_annotation) {
                Some(SyntaxKind::StringKeyword) => string,
                Some(SyntaxKind::NumberKeyword) => number,
                _ => panic!("method parameter annotations are primitive"),
            };
            if publish_annotations {
                assert!(store.set_type_node_links(
                    return_annotation,
                    TypeNodeLinks {
                        resolved_type: Some(return_type),
                        ..TypeNodeLinks::default()
                    },
                ));
                assert!(store.set_type_node_links(
                    parameter_annotation,
                    TypeNodeLinks {
                        resolved_type: Some(parameter_type),
                        ..TypeNodeLinks::default()
                    },
                ));
            }
            assert!(store.set_value_symbol_links(
                parameter,
                ValueSymbolLinks {
                    resolved_type: Some(parameter_type),
                    ..ValueSymbolLinks::default()
                },
            ));
            let signature = store
                .alloc_signature(
                    SignatureFlags::NONE,
                    Some(declaration),
                    Vec::new(),
                    None,
                    vec![parameter],
                    Some(return_type),
                    None,
                    1,
                )
                .unwrap();
            assert!(store.set_signature_links(
                declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                },
            ));
            signatures.push(signature);
            return_annotations.push(return_annotation);
            parameters.push(parameter);
            parameter_types.push(parameter_type);
        }
        assert!(store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            type_,
            None,
            None,
            Some(signatures.clone()),
            None,
            None,
        ));

        InterfaceMethodFixture {
            store,
            owner,
            method,
            type_,
            declarations,
            signatures,
            return_annotations,
            parameters,
            parameter_types,
        }
    }

    struct LateBoundPropertyFixture {
        store: CanonicalTypeMapperStore,
        owner: crate::semantic::SemanticSymbolId,
        early: crate::semantic::SemanticSymbolId,
        key: crate::semantic::SemanticSymbolId,
        key_type: crate::semantic::TypeId,
        declaration: NodeRef,
        members: crate::semantic::SymbolTableId,
    }

    fn late_bound_property_fixture(optional: bool) -> LateBoundPropertyFixture {
        let postfix = if optional { "?" } else { "" };
        let parsed = parse_source_file(&format!(
            "declare const key: unique symbol; interface Validator<T> {{ [key]{postfix}: T; }}"
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_040 + u32::from(optional));
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/late-bound.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(
                    record.kind,
                    SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature
                )
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .expect("the interface has one computed property");
        let interface = node_ref_of_kind(&parsed.arena, file, SyntaxKind::InterfaceDeclaration);
        let key_declaration =
            node_ref_of_kind(&parsed.arena, file, SyntaxKind::VariableDeclaration);
        let bound = binder.file(file).unwrap();
        let owner = bound.symbol(interface).unwrap();
        let early = bound.symbol(declaration).unwrap();
        let key = bound.symbol(key_declaration).unwrap();
        let (symbols, _) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let key_type = store.alloc_unique_es_symbol_type(key).unwrap();
        assert!(store.set_value_symbol_links(
            key,
            ValueSymbolLinks {
                resolved_type: Some(key_type),
                ..ValueSymbolLinks::default()
            },
        ));
        let members = store.alloc_symbol_table();
        LateBoundPropertyFixture {
            store,
            owner,
            early,
            key,
            key_type,
            declaration,
            members,
        }
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
    fn relation_read_observations_reject_nesting_and_discard_without_a_write() {
        let mut store = TestStore::new();
        let table = store.alloc_symbol_table();
        let first = store.begin_relation_read_observation().unwrap();
        assert!(store.begin_relation_read_observation().is_none());
        assert!(store.symbol_table(table).is_some());
        assert!(store.discard_relation_read_observation(first));

        let key = CacheHashKey::from_halves(13, 17);
        store.relation_cache_set(
            RelationKind::Assignable,
            key,
            RelationComparisonResult::SUCCEEDED,
        );
        let symbol = alloc_test_symbol(&mut store, "late");
        assert_eq!(
            store.insert_symbol(table, EscapedName::source("late"), symbol),
            Some(None)
        );
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, key),
            RelationComparisonResult::SUCCEEDED
        );
    }

    #[test]
    fn publishing_another_alias_owner_invalidates_an_observed_reverse_lookup() {
        let mut seeded = seeded_store("alias target");
        let first_alias = alloc_test_symbol(&mut seeded.store, "First");
        assert!(seeded.store.set_type_alias_links(
            first_alias,
            TypeAliasLinks {
                declared_type: Some(seeded.type_id),
                ..TypeAliasLinks::default()
            },
        ));

        let observation = seeded.store.begin_relation_read_observation().unwrap();
        assert_eq!(
            seeded
                .store
                .type_alias_declared_type_owners(seeded.type_id)
                .map(HashSet::len),
            Some(1)
        );
        let key = CacheHashKey::from_halves(19, 23);
        assert!(seeded.store.commit_relation_cache_writes(
            observation,
            RelationKind::StrictSubtype,
            [(key, RelationComparisonResult::SUCCEEDED)],
        ));

        let second_alias = alloc_test_symbol(&mut seeded.store, "Second");
        assert!(seeded.store.set_type_alias_links(
            second_alias,
            TypeAliasLinks {
                declared_type: Some(seeded.type_id),
                ..TypeAliasLinks::default()
            },
        ));
        assert_eq!(
            seeded
                .store
                .relation_cache_get(RelationKind::StrictSubtype, key),
            RelationComparisonResult::NONE
        );
    }

    #[test]
    fn first_members_and_exports_publication_invalidates_an_observed_miss() {
        let mut store = TestStore::new();
        let symbol = alloc_test_symbol(&mut store, "late-bound owner");
        let observation = store.begin_relation_read_observation().unwrap();
        assert_eq!(store.members_and_exports_links(symbol), None);
        let key = CacheHashKey::from_halves(29, 31);
        assert!(store.commit_relation_cache_writes(
            observation,
            RelationKind::StrictSubtype,
            [(key, RelationComparisonResult::SUCCEEDED)],
        ));

        let members = store.alloc_symbol_table();
        let mut links = MembersAndExportsLinks::default();
        links.tables[0] = Some(members);
        assert!(store.set_members_and_exports_links(symbol, links));
        assert_eq!(
            store.relation_cache_get(RelationKind::StrictSubtype, key),
            RelationComparisonResult::NONE
        );
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
    fn source_child_kind_queries_match_the_retained_fact_scan() {
        let mut parsed =
            parse_source_file("interface Item { run?(value: string): boolean; other(): void }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(57);
        let root = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let name = node_ref_of_kind(&parsed.arena, file, SyntaxKind::Identifier);
        let mut detached = parsed.arena.get(name.node).unwrap().clone();
        detached.parent = None;
        let detached = parsed.arena.alloc(detached);
        let mut store = TestStore::new();
        assert_eq!(
            store.source_child_with_kind(root, SyntaxKind::Identifier),
            None
        );
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let before = format!("{store:?}");
        let facts = store.source_node_facts.get(&parsed.arena.id()).unwrap();
        for (index, parent) in facts.iter().enumerate() {
            if parent.is_none() {
                continue;
            }
            let parent = NodeRef::new(
                parsed.arena.id(),
                file,
                NodeId::new(u32::try_from(index).unwrap()),
            );
            for kind in [
                SyntaxKind::Identifier,
                SyntaxKind::MethodSignature,
                SyntaxKind::Parameter,
                SyntaxKind::QuestionToken,
            ] {
                let matching = facts
                    .iter()
                    .enumerate()
                    .filter_map(|(index, child)| {
                        let child = child.as_ref()?;
                        if child.parent != Some(parent.node) || child.kind != kind {
                            return None;
                        }
                        Some(NodeRef::new(
                            parent.arena,
                            parent.file,
                            NodeId::new(u32::try_from(index).unwrap()),
                        ))
                    })
                    .collect::<Vec<_>>();
                let expected = match matching.as_slice() {
                    [child] => Some(*child),
                    _ => None,
                };
                assert_eq!(store.source_child_with_kind(parent, kind), expected);
            }
        }
        let foreign = NodeArena::new();
        for invalid in [
            NodeRef::new(parsed.arena.id(), file, detached),
            NodeRef::new(foreign.id(), file, root.node),
            NodeRef::new(root.arena, FileId::new(58), root.node),
            NodeRef::new(root.arena, file, NodeId::new(u32::MAX)),
        ] {
            assert_eq!(
                store.source_child_with_kind(invalid, SyntaxKind::Identifier),
                None
            );
        }
        assert_eq!(format!("{store:?}"), before);
    }

    #[test]
    fn declared_method_optional_counts_match_retained_fact_scan() {
        let parsed = parse_source_file(concat!(
            "interface Contract { ",
            "required(callback: (value?: string) => void, value?: number): void; ",
            "required(): void; optional?(value?: string): void; optional?(): void; } ",
            "type Other = { unrelated?: string };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(60);
        let mut binder = CanonicalBinder::new();
        let facts = CanonicalSourceFileFacts::new(
            EscapedName::source("\"/method-optional-count.ts\""),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::Script,
        );
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts)
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let methods = parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::MethodSignature)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect::<Vec<_>>();
        assert_eq!(methods.len(), 4);
        let owners = [methods[0], methods[2]]
            .map(|declaration| binder.file(file).unwrap().symbol(declaration).unwrap());
        assert_ne!(owners[0], owners[1]);
        let (symbols, _) = binder.finish().try_into_parts().unwrap();
        let mut store = TestStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let original = store.source_node_facts[&parsed.arena.id()].clone();
        let before = format!("{store:?}");
        for (symbol, optional) in owners.into_iter().zip([false, true]) {
            let method = store.symbol(symbol).unwrap();
            let declarations = method.declarations().unwrap().to_vec();
            let expected_tokens = usize::from(optional);
            assert_eq!(declarations.len(), 2);
            for duplicate in [false, true] {
                if duplicate {
                    let extra = store
                        .source_direct_children(declarations[1])
                        .unwrap()
                        .into_iter()
                        .filter(|&child| {
                            store.source_node_kind(child) != Some(SyntaxKind::QuestionToken)
                        })
                        .take(2 - expected_tokens)
                        .collect::<Vec<_>>();
                    assert_eq!(extra.len(), 2 - expected_tokens);
                    for child in extra {
                        store.source_node_facts.get_mut(&child.arena).unwrap()
                            [child.node.index()]
                        .as_mut()
                        .unwrap()
                        .kind = SyntaxKind::QuestionToken;
                    }
                }
                let facts = store.source_node_facts.get(&parsed.arena.id()).unwrap();
                let counts = declarations
                    .iter()
                    .map(|declaration| {
                        facts
                            .iter()
                            .flatten()
                            .filter(|child| {
                                child.parent == Some(declaration.node)
                                    && child.kind == SyntaxKind::QuestionToken
                            })
                            .count()
                    })
                    .collect::<Vec<_>>();
                assert_eq!(
                    counts,
                    [expected_tokens, if duplicate { 2 } else { expected_tokens }]
                );
                let expected = counts
                    .into_iter()
                    .all(|count| count == expected_tokens)
                    .then_some(optional);
                let frozen = format!("{store:?}");
                for _ in 0..2 {
                    assert_eq!(store.declared_method_optional_flag(symbol), expected);
                    assert_eq!(format!("{store:?}"), frozen);
                }
                store
                    .source_node_facts
                    .insert(parsed.arena.id(), original.clone());
                assert_eq!(format!("{store:?}"), before);
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Compare each method read with its old retained-fact scan.
    fn declared_method_source_children_match_retained_parameter_scans() {
        let parsed = parse_source_file(concat!(
            "interface Contract { ",
            "run<T, U>(first: T, callback: <V>(value?: V) => U, ",
            "last?: U, ...rest: T[]): U; ",
            "run(): number; ",
            "} ",
            "type Other = { run<V>(value?: V, ...rest: V[]): void }; ",
            "declare function unrelated<X>(value?: X, ...rest: X[]): X;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(59);
        let mut store = TestStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );

        let before = format!("{store:?}");
        let facts = store.source_node_facts.get(&parsed.arena.id()).unwrap();
        let mut parameter_shapes = Vec::new();
        let mut type_parameter_counts = Vec::new();
        for (method, record) in parsed.arena.iter() {
            if record.kind != SyntaxKind::MethodSignature {
                continue;
            }
            let method = NodeRef::new(parsed.arena.id(), file, method);
            let retained_parameters = facts
                .iter()
                .enumerate()
                .filter_map(|(index, child)| {
                    let child = child.as_ref()?;
                    (child.kind == SyntaxKind::Parameter && child.parent == Some(method.node))
                        .then_some(NodeRef::new(
                            method.arena,
                            file,
                            NodeId::new(u32::try_from(index).unwrap()),
                        ))
                })
                .collect::<Vec<_>>();
            let mut indexed_parameters = store.source_direct_children(method).unwrap();
            indexed_parameters.retain(|parameter| {
                store.source_node_kind(*parameter) == Some(SyntaxKind::Parameter)
            });
            assert_eq!(indexed_parameters, retained_parameters);
            assert!(
                indexed_parameters
                    .windows(2)
                    .all(|pair| pair[0].node < pair[1].node)
            );

            let retained_type_parameters = facts[..method.node.index()]
                .iter()
                .enumerate()
                .filter_map(|(index, child)| {
                    let child = child.as_ref()?;
                    (child.kind == SyntaxKind::TypeParameter && child.parent == Some(method.node))
                        .then_some(NodeRef::new(
                            method.arena,
                            file,
                            NodeId::new(u32::try_from(index).unwrap()),
                        ))
                })
                .collect::<Vec<_>>();
            let mut indexed_type_parameters = store.source_direct_children(method).unwrap();
            indexed_type_parameters.retain(|parameter| {
                parameter.node < method.node
                    && store.source_node_kind(*parameter) == Some(SyntaxKind::TypeParameter)
            });
            assert_eq!(indexed_type_parameters, retained_type_parameters);
            type_parameter_counts.push(indexed_type_parameters.len());

            let mut shape = Vec::new();
            for parameter in indexed_parameters {
                let children = store.source_direct_children(parameter).unwrap();
                let flags = [SyntaxKind::QuestionToken, SyntaxKind::DotDotDotToken].map(|kind| {
                    let retained = facts
                        .iter()
                        .flatten()
                        .any(|child| child.kind == kind && child.parent == Some(parameter.node));
                    let indexed = children
                        .iter()
                        .any(|child| store.source_node_kind(*child) == Some(kind));
                    assert_eq!(indexed, retained);
                    indexed
                });
                shape.push(flags);
            }
            parameter_shapes.push(shape);
        }
        assert_eq!(type_parameter_counts, vec![2, 0, 1]);
        assert_eq!(
            parameter_shapes,
            vec![
                vec![[false, false], [false, false], [true, false], [false, true]],
                vec![],
                vec![[true, false], [false, true]],
            ],
        );
        assert_eq!(format!("{store:?}"), before);
    }

    #[test]
    fn source_direct_children_matches_retained_fact_order_and_ownership() {
        let mut parsed = parse_source_file(concat!(
            "type Read<T> = { [K in keyof T as K]?: T[K] }; ",
            "interface Base {} ",
            "interface Pair extends Base { first: number; run(value: string): boolean }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(51);
        let leaf = node_ref_of_kind(&parsed.arena, file, SyntaxKind::Identifier);
        let mut detached = parsed.arena.get(leaf.node).unwrap().clone();
        detached.parent = None;
        let detached = parsed.arena.alloc(detached);
        let root = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(AstScope::new(file, &parsed.arena)));
        assert_eq!(store.source_direct_children(root), None);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );

        let before = format!("{store:?}");
        let facts = store.source_node_facts.get(&parsed.arena.id()).unwrap();
        for (index, parent) in facts.iter().enumerate() {
            if parent.is_none() {
                continue;
            }
            let parent = NodeRef::new(
                parsed.arena.id(),
                file,
                NodeId::new(u32::try_from(index).unwrap()),
            );
            let expected = facts
                .iter()
                .enumerate()
                .filter_map(|(index, child)| {
                    if child.as_ref()?.parent != Some(parent.node) {
                        return None;
                    }
                    Some(NodeRef::new(
                        parent.arena,
                        parent.file,
                        NodeId::new(u32::try_from(index).unwrap()),
                    ))
                })
                .collect::<Vec<_>>();
            assert_eq!(store.source_direct_children(parent), Some(expected));
        }
        let mapped = node_ref_of_kind(&parsed.arena, file, SyntaxKind::MappedType);
        let mut syntax_order = Vec::new();
        parsed
            .arena
            .get(mapped.node)
            .unwrap()
            .for_each_child(|child| syntax_order.push(NodeRef::new(mapped.arena, file, child)));
        let indexed_order = store.source_direct_children(mapped).unwrap();
        assert_ne!(indexed_order, syntax_order);
        assert!(
            indexed_order
                .windows(2)
                .all(|pair| pair[0].node < pair[1].node)
        );
        assert_eq!(store.source_direct_children(leaf), Some(Vec::new()));
        let detached = NodeRef::new(parsed.arena.id(), file, detached);
        assert!(store.contains_node_ref(detached));
        assert_eq!(store.source_direct_children(detached), None);
        let foreign = NodeArena::new();
        for invalid in [
            NodeRef::new(foreign.id(), file, root.node),
            NodeRef::new(root.arena, FileId::new(52), root.node),
            NodeRef::new(root.arena, file, NodeId::new(u32::MAX)),
        ] {
            assert_eq!(store.source_direct_children(invalid), None);
        }
        assert_eq!(format!("{store:?}"), before);
    }

    fn append_source_type_alias(
        arena: &mut NodeArena,
        source_file: NodeId,
    ) -> (NodeId, [NodeId; 2]) {
        let mut declaration = arena
            .iter()
            .find_map(|(_, node)| {
                matches!(node.data, NodeData::TypeAliasDeclaration(_)).then(|| node.clone())
            })
            .unwrap();
        let NodeData::TypeAliasDeclaration(alias) = &mut declaration.data else {
            panic!("the fixture contains a type alias")
        };
        let mut name = arena.get(alias.name).unwrap().clone();
        let NodeData::Identifier(identifier) = &mut name.data else {
            panic!("the alias has an identifier name")
        };
        identifier.text = "Appended".to_owned();
        let annotation = arena.get(alias.type_).unwrap().clone();
        assert!(annotation.kind.is_keyword_type());
        alias.name = arena.alloc(name);
        alias.type_ = arena.alloc(annotation);
        let children = [alias.name, alias.type_];
        declaration.parent = Some(source_file);
        let declaration = arena.alloc(declaration);
        for child in children {
            arena.get_mut(child).unwrap().parent = Some(declaration);
        }
        let NodeData::SourceFile(source) = &mut arena.get_mut(source_file).unwrap().data else {
            panic!("the fixture has a source-file root")
        };
        source.statements.nodes.push(declaration);
        (declaration, children)
    }

    #[test]
    fn source_direct_children_refreshes_after_accepted_arena_append() {
        let mut parsed = parse_source_file("type First = number;");
        let file = FileId::new(53);
        let mut store = TestStore::new();
        let source = store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let old_facts = store.source_node_facts[&parsed.arena.id()].clone();
        let mut expected = store.source_direct_children(source.node_ref()).unwrap();
        let (appended, children) = append_source_type_alias(&mut parsed.arena, parsed.source_file);
        let appended = NodeRef::new(parsed.arena.id(), file, appended);
        assert!(!store.contains_node_ref(appended));
        assert_eq!(store.source_direct_children(appended), None);
        assert_eq!(
            store.source_direct_children(source.node_ref()),
            Some(expected.clone())
        );

        assert_eq!(
            store.register_source_file(&parsed.arena, parsed.source_file, file),
            Some(source)
        );
        assert_eq!(
            &store.source_node_facts[&parsed.arena.id()][..old_facts.len()],
            old_facts.as_slice()
        );
        expected.push(appended);
        assert_eq!(
            store.source_direct_children(source.node_ref()),
            Some(expected)
        );
        assert_eq!(
            store.source_direct_children(appended),
            Some(
                children
                    .map(|node| NodeRef::new(appended.arena, file, node))
                    .to_vec()
            )
        );
        for child in children {
            assert_eq!(
                store.source_direct_children(NodeRef::new(appended.arena, file, child)),
                Some(Vec::new())
            );
        }
        let before = format!("{store:?}");
        assert_eq!(
            store.register_source_file(&parsed.arena, parsed.source_file, file),
            Some(source)
        );
        assert_eq!(format!("{store:?}"), before);
    }

    #[test]
    fn source_direct_children_keeps_the_index_after_rejected_registration() {
        let mut parsed = parse_source_file("type First = number;");
        let file = FileId::new(54);
        let original_name = node_ref_of_kind(&parsed.arena, file, SyntaxKind::Identifier).node;
        let original = parsed.arena.get(original_name).unwrap().clone();
        let mut store = TestStore::new();
        let source = store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let index = store.source_node_children.clone();
        let children = store.source_direct_children(source.node_ref()).unwrap();
        let (appended, _) = append_source_type_alias(&mut parsed.arena, parsed.source_file);
        let appended = NodeRef::new(parsed.arena.id(), file, appended);
        for wrong_parent in [false, true] {
            let changed = parsed.arena.get_mut(original_name).unwrap();
            *changed = original.clone();
            if wrong_parent {
                changed.parent = None;
            } else {
                let NodeData::Identifier(identifier) = &mut changed.data else {
                    panic!("the selected node is an identifier")
                };
                identifier.text = "Changed".to_owned();
            }
            let before = format!("{store:?}");
            assert_eq!(
                store.register_source_file(&parsed.arena, parsed.source_file, file),
                None
            );
            assert_eq!(store.source_node_children, index);
            assert_eq!(
                store.source_direct_children(source.node_ref()),
                Some(children.clone())
            );
            assert!(!store.contains_node_ref(appended));
            assert_eq!(store.source_direct_children(appended), None);
            assert_eq!(format!("{store:?}"), before);
        }
        *parsed.arena.get_mut(original_name).unwrap() = original;
        assert_eq!(
            store.register_source_file(&parsed.arena, parsed.source_file, file),
            Some(source)
        );
        assert!(
            store
                .source_direct_children(source.node_ref())
                .unwrap()
                .contains(&appended)
        );
    }

    #[test]
    fn source_identifier_text_requires_registered_source_ownership() {
        let mut parsed = parse_source_file("type Value = Date;");
        let file = FileId::new(41);
        let identifier = parsed
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::Identifier(identifier) if identifier.text == "Date" => Some(node),
                _ => None,
            })
            .unwrap();
        let name = NodeRef::new(parsed.arena.id(), file, identifier);
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(AstScope::new(file, &parsed.arena)));
        assert_eq!(store.source_identifier_text(name), None);
        let source = store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        assert_eq!(store.source_identifier_text(name), Some("Date"));
        assert_eq!(store.source_identifier_text(source.node_ref()), None);
        assert_eq!(
            store.source_identifier_text(NodeRef::new(
                parsed.arena.id(),
                FileId::new(42),
                identifier
            )),
            None,
        );

        let other = parse_source_file("type Value = Other;");
        let mut other_store = TestStore::new();
        assert!(
            other_store
                .register_source_file(&other.arena, other.source_file, file)
                .is_some()
        );
        assert_eq!(other_store.source_identifier_text(name), None);
        assert_eq!(
            store.source_identifier_text(NodeRef::new(other.arena.id(), file, identifier)),
            None
        );

        let mut discarded = parsed.arena.get(identifier).unwrap().clone();
        discarded.parent = None;
        let discarded = parsed.arena.alloc(discarded);
        assert_eq!(
            store.register_source_file(&parsed.arena, parsed.source_file, file),
            Some(source)
        );
        assert_eq!(
            store.source_identifier_text(NodeRef::new(parsed.arena.id(), file, discarded)),
            None
        );

        let NodeData::Identifier(changed) = &mut parsed.arena.get_mut(identifier).unwrap().data
        else {
            panic!("the selected node must remain an identifier")
        };
        changed.text = "Other".to_owned();
        assert_eq!(
            store.register_source_file(&parsed.arena, parsed.source_file, file),
            None
        );
        assert_eq!(store.source_identifier_text(name), Some("Date"));
        assert!(store.contains_source_file(source));
    }

    #[test]
    fn source_plain_interface_heritage_retains_exact_ordered_roles() {
        let mut parsed = parse_source_file(concat!(
            "interface First {} interface Second {} ",
            "interface Derived extends Second, First, Second { own: number }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(44);
        let interfaces = parsed
            .arena
            .iter()
            .filter_map(|(id, node)| {
                (node.kind == SyntaxKind::InterfaceDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    id,
                ))
            })
            .collect::<Vec<_>>();
        let [first, second, derived] = interfaces.as_slice() else {
            panic!("the source has three interfaces")
        };
        let clause = node_ref_of_kind(&parsed.arena, file, SyntaxKind::HeritageClause);
        let bases = parsed
            .arena
            .iter()
            .filter_map(|(expression, node)| match &node.data {
                NodeData::ExpressionWithTypeArguments(base) => Some(PlainInterfaceBaseFacts {
                    expression,
                    name: base.expression,
                }),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(bases.len(), 3);
        let expected = PlainInterfaceHeritageFacts::Plain {
            clause: clause.node,
            bases: bases.clone().into_boxed_slice(),
        };
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(AstScope::new(file, &parsed.arena)));
        assert_eq!(store.source_plain_interface_heritage(*derived), None);
        let source = store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        for &base in [first, second] {
            assert_eq!(
                store.source_plain_interface_heritage(base),
                Some(&PlainInterfaceHeritageFacts::NoHeritage),
            );
        }
        assert_eq!(
            store.source_plain_interface_heritage(*derived),
            Some(&expected)
        );
        for (base, name) in bases.iter().zip(["Second", "First", "Second"]) {
            assert_eq!(
                store.source_identifier_text(NodeRef::new(derived.arena, file, base.name)),
                Some(name),
            );
        }
        assert_eq!(
            store.source_plain_interface_heritage(source.node_ref()),
            None
        );
        assert_eq!(store.source_plain_interface_heritage(clause), None);
        assert_eq!(
            store.source_plain_interface_heritage(NodeRef::new(
                derived.arena,
                FileId::new(45),
                derived.node,
            )),
            None,
        );
        let foreign = parse_source_file("interface Derived extends Other {}");
        assert_eq!(
            store.source_plain_interface_heritage(node_ref_of_kind(
                &foreign.arena,
                file,
                SyntaxKind::InterfaceDeclaration,
            )),
            None,
        );

        let NodeData::HeritageClause(heritage) =
            &mut parsed.arena.get_mut(clause.node).unwrap().data
        else {
            panic!("the retained clause has a heritage payload")
        };
        heritage.token = SyntaxKind::ImplementsKeyword;
        assert_eq!(
            store.register_source_file(&parsed.arena, parsed.source_file, file),
            None,
        );
        assert_eq!(
            store.source_plain_interface_heritage(*derived),
            Some(&expected)
        );
    }

    #[test]
    fn source_plain_interface_heritage_keeps_unsupported_source_registered() {
        for source in [
            "interface Derived<T> {}",
            "interface Derived<T> extends Base {}",
            "interface Derived extends Namespace.Base {}",
            "interface Derived extends Base<string> {}",
            "interface Derived implements Base {}",
            "interface Derived extends First implements Second {}",
            "interface Derived extends Base, {}",
        ] {
            let parsed = parse_source_file(source);
            let file = FileId::new(46);
            let declaration =
                node_ref_of_kind(&parsed.arena, file, SyntaxKind::InterfaceDeclaration);
            let mut store = TestStore::new();
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some(),
                "{source}",
            );
            assert_eq!(
                store.source_plain_interface_heritage(declaration),
                Some(&PlainInterfaceHeritageFacts::Unsupported),
                "{source}",
            );
        }
    }

    #[test]
    fn source_plain_interface_heritage_rejects_interface_state() {
        for source in ["interface Base {}", "interface Derived extends Base {}"] {
            for field in ["flow_node", "local_symbol", "symbol"] {
                let mut parsed = parse_source_file(source);
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                let file = FileId::new(51);
                let declaration =
                    node_ref_of_kind(&parsed.arena, file, SyntaxKind::InterfaceDeclaration);
                let NodeData::InterfaceDeclaration(interface) =
                    &mut parsed.arena.get_mut(declaration.node).unwrap().data
                else {
                    panic!("the declaration is an interface")
                };
                match field {
                    "flow_node" => interface.flow_node = Some(ts_ast::FlowNodeId(1)),
                    "local_symbol" => interface.local_symbol = Some(ts_ast::SymbolId(1)),
                    "symbol" => interface.symbol = Some(ts_ast::SymbolId(1)),
                    _ => unreachable!(),
                }
                let mut store = TestStore::new();
                assert!(
                    store
                        .register_source_file(&parsed.arena, parsed.source_file, file)
                        .is_some(),
                    "{source}, {field}",
                );
                assert_eq!(
                    store.source_plain_interface_heritage(declaration),
                    Some(&PlainInterfaceHeritageFacts::Unsupported),
                    "{source}, {field}",
                );
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each mutation checks one retained syntax condition.
    fn source_plain_interface_heritage_rejects_altered_syntax() {
        #[derive(Clone, Copy, Debug)]
        enum Damage {
            EmptyParameters,
            EmptyClauses,
            EmptyBases,
            EmptyArguments,
            ClauseComma,
            BaseComma,
            ClauseFacts,
            BaseFacts,
            InterfaceFlags,
            ClauseFlags,
            BaseFlags,
            NameFlags,
            NameFlow,
            EmptyName,
            ClauseRange,
            BaseListRange,
            BaseRange,
            NameRange,
            BaseOrder,
        }
        for damage in [
            Damage::EmptyParameters,
            Damage::EmptyClauses,
            Damage::EmptyBases,
            Damage::EmptyArguments,
            Damage::ClauseComma,
            Damage::BaseComma,
            Damage::ClauseFacts,
            Damage::BaseFacts,
            Damage::InterfaceFlags,
            Damage::ClauseFlags,
            Damage::BaseFlags,
            Damage::NameFlags,
            Damage::NameFlow,
            Damage::EmptyName,
            Damage::ClauseRange,
            Damage::BaseListRange,
            Damage::BaseRange,
            Damage::NameRange,
            Damage::BaseOrder,
        ] {
            let mut parsed = parse_source_file("interface Derived extends First, Second {}");
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(47);
            let declaration =
                node_ref_of_kind(&parsed.arena, file, SyntaxKind::InterfaceDeclaration);
            let clause = node_ref_of_kind(&parsed.arena, file, SyntaxKind::HeritageClause);
            let expression =
                node_ref_of_kind(&parsed.arena, file, SyntaxKind::ExpressionWithTypeArguments);
            let NodeData::ExpressionWithTypeArguments(base) =
                &parsed.arena.get(expression.node).unwrap().data
            else {
                panic!("the base has the expected payload")
            };
            let name = base.expression;
            match damage {
                Damage::EmptyParameters | Damage::EmptyClauses | Damage::ClauseComma => {
                    let NodeData::InterfaceDeclaration(interface) =
                        &mut parsed.arena.get_mut(declaration.node).unwrap().data
                    else {
                        panic!("the declaration is an interface")
                    };
                    match damage {
                        Damage::EmptyParameters => {
                            interface.type_parameters = Some(ts_ast::NodeList::default());
                        }
                        Damage::EmptyClauses => {
                            interface.heritage_clauses.as_mut().unwrap().nodes.clear();
                        }
                        Damage::ClauseComma => {
                            interface
                                .heritage_clauses
                                .as_mut()
                                .unwrap()
                                .has_trailing_comma = true;
                        }
                        _ => unreachable!(),
                    }
                }
                Damage::EmptyBases
                | Damage::BaseComma
                | Damage::ClauseFacts
                | Damage::BaseListRange
                | Damage::BaseOrder => {
                    let record = parsed.arena.get_mut(clause.node).unwrap();
                    let NodeData::HeritageClause(heritage) = &mut record.data else {
                        panic!("the clause has the expected payload")
                    };
                    match damage {
                        Damage::EmptyBases => heritage.types.nodes.clear(),
                        Damage::BaseComma => heritage.types.has_trailing_comma = true,
                        Damage::ClauseFacts => heritage.facts = 1,
                        Damage::BaseListRange => heritage.types.range.start = record.range.start,
                        Damage::BaseOrder => heritage.types.nodes.reverse(),
                        _ => unreachable!(),
                    }
                }
                Damage::EmptyArguments | Damage::BaseFacts => {
                    let NodeData::ExpressionWithTypeArguments(base) =
                        &mut parsed.arena.get_mut(expression.node).unwrap().data
                    else {
                        panic!("the base has the expected payload")
                    };
                    match damage {
                        Damage::EmptyArguments => {
                            base.type_arguments = Some(ts_ast::NodeList::default());
                        }
                        Damage::BaseFacts => base.facts = 1,
                        _ => unreachable!(),
                    }
                }
                Damage::InterfaceFlags => {
                    parsed.arena.get_mut(declaration.node).unwrap().flags = NodeFlags(1);
                }
                Damage::ClauseFlags => {
                    parsed.arena.get_mut(clause.node).unwrap().flags = NodeFlags(1);
                }
                Damage::BaseFlags => {
                    parsed.arena.get_mut(expression.node).unwrap().flags = NodeFlags(1);
                }
                Damage::NameFlags => {
                    parsed.arena.get_mut(name).unwrap().flags = NodeFlags(1);
                }
                Damage::NameFlow | Damage::EmptyName => {
                    let NodeData::Identifier(identifier) =
                        &mut parsed.arena.get_mut(name).unwrap().data
                    else {
                        panic!("the base name is an identifier")
                    };
                    match damage {
                        Damage::NameFlow => identifier.flow_node = Some(ts_ast::FlowNodeId(1)),
                        Damage::EmptyName => identifier.text.clear(),
                        _ => unreachable!(),
                    }
                }
                Damage::ClauseRange => {
                    let record = parsed.arena.get_mut(clause.node).unwrap();
                    record.range.start = record.range.end;
                }
                Damage::BaseRange => {
                    let record = parsed.arena.get_mut(expression.node).unwrap();
                    record.range.end = record.range.start;
                }
                Damage::NameRange => {
                    let record = parsed.arena.get_mut(name).unwrap();
                    record.range.end = record.range.start;
                }
            }
            let mut store = TestStore::new();
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some(),
                "{damage:?}",
            );
            assert_eq!(
                store.source_plain_interface_heritage(declaration),
                Some(&PlainInterfaceHeritageFacts::Unsupported),
                "{damage:?}",
            );
        }
    }

    #[test]
    fn source_plain_interface_heritage_keeps_registration_parent_checks() {
        for kind in [
            SyntaxKind::HeritageClause,
            SyntaxKind::ExpressionWithTypeArguments,
            SyntaxKind::Identifier,
        ] {
            let mut parsed = parse_source_file("interface Derived extends Base {}");
            let file = FileId::new(48);
            let declaration =
                node_ref_of_kind(&parsed.arena, file, SyntaxKind::InterfaceDeclaration);
            let node = if kind == SyntaxKind::Identifier {
                let expression =
                    node_ref_of_kind(&parsed.arena, file, SyntaxKind::ExpressionWithTypeArguments);
                let NodeData::ExpressionWithTypeArguments(base) =
                    &parsed.arena.get(expression.node).unwrap().data
                else {
                    panic!("the base has the expected payload")
                };
                base.expression
            } else {
                node_ref_of_kind(&parsed.arena, file, kind).node
            };
            parsed.arena.get_mut(node).unwrap().parent = None;
            let mut store = TestStore::new();
            assert_eq!(
                store.register_source_file(&parsed.arena, parsed.source_file, file),
                None,
                "{kind:?}",
            );
            assert_eq!(store.source_plain_interface_heritage(declaration), None);
        }
    }

    #[test]
    fn source_global_bindings_keep_declaration_order_after_symbol_changes() {
        let first = parse_source_file(concat!(
            "interface Base { first: string } ",
            "interface Derived extends Base { first: string }",
        ));
        let second = parse_source_file(concat!(
            "interface Base { second: number } declare var Base: unknown; ",
            "interface Derived { second: number } declare var Derived: unknown;",
        ));
        let files = [(FileId::new(49), &first), (FileId::new(50), &second)];
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in files {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/heritage-snapshot-{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            files
                .iter()
                .map(|(file, parsed)| (*file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let globals = context.globals();
        let owners = ["Base", "Derived"].map(|name| {
            context
                .store()
                .symbol_table(globals)
                .and_then(|table| table.get_source(name))
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap()
        });
        let store = context.store_mut_for_test();
        for owner in owners {
            let retained = |store: &CanonicalTypeMapperStore| {
                store
                    .source_global_bindings()
                    .unwrap()
                    .iter()
                    .find(|binding| binding.symbol == owner)
                    .unwrap()
                    .declarations()
                    .unwrap()
                    .to_vec()
            };
            let record = store.symbol(owner).unwrap();
            let original = record.declarations().unwrap().to_vec();
            let value = record.value_declaration();
            assert_eq!(original.len(), 3);
            assert_eq!(retained(store), original);
            let mut reversed = original.clone();
            reversed.reverse();
            for declarations in [None, Some(Vec::new()), Some(reversed)] {
                assert!(store.set_symbol_declarations(owner, declarations, None));
                let before = format!("{store:?}");
                assert_eq!(retained(store), original);
                assert!(!store.record_source_global_bindings(globals));
                assert_eq!(format!("{store:?}"), before);
            }
            assert!(store.set_symbol_declarations(owner, Some(original.clone()), value));
            assert_eq!(retained(store), original);
        }
        let unknown = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::INTERFACE,
                EscapedName::source("Unrecorded"),
            ))
            .unwrap();
        assert!(
            store
                .source_global_bindings()
                .unwrap()
                .iter()
                .all(|binding| binding.symbol != unknown)
        );
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
    fn declared_construct_signatures_require_matching_flags_and_publish_owned_caches() {
        let parsed = parse_source_file(concat!(
            "type Factory = { new(value: number): string }; ",
            "type Callback = { (value: number): string };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_004);
        let mut store = CanonicalTypeMapperStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let construct = node_ref_of_kind(&parsed.arena, file, SyntaxKind::ConstructSignature);
        let call = node_ref_of_kind(&parsed.arena, file, SyntaxKind::CallSignature);
        let NodeData::ConstructSignatureDeclaration(construct_data) =
            &parsed.arena.get(construct.node).unwrap().data
        else {
            panic!("the factory has a construct signature")
        };
        let parameter_node =
            NodeRef::new(parsed.arena.id(), file, construct_data.parameters.nodes[0]);
        let return_annotation = NodeRef::new(
            parsed.arena.id(),
            file,
            construct_data
                .type_
                .expect("the constructor has a return type"),
        );
        let mut parameter_data = SymbolData::new(
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            EscapedName::source("value"),
        );
        parameter_data.declarations = Some(vec![parameter_node]);
        parameter_data.value_declaration = Some(parameter_node);
        let parameter = store.alloc_symbol(parameter_data).unwrap();
        let (number, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let owner = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let missing_construct_flag = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(construct),
                Vec::new(),
                None,
                vec![parameter],
                Some(string),
                None,
                1,
            )
            .unwrap();
        let wrong_construct_flag = store
            .alloc_signature(
                SignatureFlags::CONSTRUCT,
                Some(call),
                Vec::new(),
                None,
                Vec::new(),
                Some(string),
                None,
                0,
            )
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::CONSTRUCT,
                Some(construct),
                Vec::new(),
                None,
                vec![parameter],
                Some(string),
                None,
                1,
            )
            .unwrap();
        let before = (
            store.declared_call_set_provenance.len(),
            store.declared_call_set_types_by_signature.len(),
        );

        assert!(!store.set_declared_call_set_provenance(owner, &[missing_construct_flag]));
        assert!(!store.set_declared_call_set_provenance(owner, &[wrong_construct_flag]));
        assert_eq!(
            (
                store.declared_call_set_provenance.len(),
                store.declared_call_set_types_by_signature.len(),
            ),
            before,
        );
        assert!(store.try_reserve_declared_call_set_provenance(1, 1));
        assert!(store.set_declared_call_set_provenance(owner, &[signature]));
        assert_eq!(
            store.declared_call_set_type_for_signature(signature),
            Some(owner)
        );
        assert!(store.set_function_signature_return_annotation(
            signature,
            return_annotation,
            false,
        ));
        assert!(store.set_signature_links(
            construct,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(
            store.set_callable_signature_parameter_types_batch(vec![(signature, vec![number],)])
        );
        assert_eq!(
            store.callable_signature_parameter_types(signature),
            Some([number].as_slice()),
        );
        assert!(store.signature_is_callable(signature));
        assert!(store.symbol_is_callable_parameter(parameter));
        assert!(store.node_has_callable_ancestor(return_annotation));

        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            },
        ));
        store.union_cache_needs_validation = false;
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.union_cache_needs_validation);
    }

    #[test]
    fn global_interface_methods_authenticate_merged_owners_and_publish_callable_caches() {
        for (global, declaration) in [
            ("Number", "toFixed(fractionDigits?: number): string;"),
            ("String", "toLowerCase(): string;"),
        ] {
            let mut fixture = global_interface_method_fixture(global, declaration);
            assert_ne!(
                fixture.store.symbol(fixture.method).unwrap().parent(),
                Some(fixture.owner),
                "global merging preserves the method's original interface parent",
            );
            assert_eq!(
                fixture.store.get_parent_of_symbol(fixture.method),
                Some(fixture.owner),
            );
            assert_eq!(
                fixture
                    .store
                    .authenticated_global_interface_method(fixture.method),
                Some((fixture.wrapper, fixture.declaration)),
            );
            assert_eq!(
                fixture
                    .store
                    .symbol_store()
                    .assigned_global_symbol_id(fixture.owner),
                None,
            );

            let (type_, signature) = publish_global_interface_method_fixture(&mut fixture);
            assert_eq!(
                fixture
                    .store
                    .global_interface_method_callable_type(signature),
                Some(type_),
            );
            assert!(fixture.store.signature_is_callable(signature));
            assert!(
                fixture
                    .store
                    .node_has_callable_ancestor(fixture.return_annotation)
            );
            assert_eq!(
                fixture
                    .store
                    .symbol_store()
                    .assigned_global_symbol_id(fixture.owner),
                None,
            );
            if let Some((parameter, _)) = fixture.parameter {
                assert!(fixture.store.symbol_is_callable_parameter(parameter));
            }
        }
    }

    #[test]
    fn interface_method_overloads_publish_owned_caches_and_replay_without_mutation() {
        let mut fixture = interface_method_fixture();
        assert_eq!(
            fixture
                .store
                .authenticated_interface_method_owner(fixture.method)
                .map(|(owner, _)| owner),
            Some(fixture.owner),
        );

        for ((signature, annotation), parameter) in fixture
            .signatures
            .iter()
            .copied()
            .zip(fixture.return_annotations.iter().copied())
            .zip(fixture.parameters.iter().copied())
        {
            assert_eq!(
                fixture.store.interface_method_linked_type(signature),
                Some(fixture.type_),
            );
            assert!(fixture.store.signature_is_callable(signature));
            assert!(fixture.store.symbol_is_callable_parameter(parameter));
            assert!(fixture.store.node_has_callable_ancestor(annotation));
            assert!(
                fixture
                    .store
                    .set_function_signature_return_annotation(signature, annotation, false)
            );
        }
        assert!(
            fixture.store.set_callable_signature_parameter_types_batch(
                fixture
                    .signatures
                    .iter()
                    .copied()
                    .zip(fixture.parameter_types.iter().copied())
                    .map(|(signature, type_)| (signature, vec![type_]))
                    .collect(),
            )
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture.store.callable_signature_parameter_types_len(),
            fixture.store.function_signature_return_annotations.len(),
        );
        for ((signature, annotation), type_) in fixture
            .signatures
            .iter()
            .copied()
            .zip(fixture.return_annotations.iter().copied())
            .zip(fixture.parameter_types.iter().copied())
        {
            assert_eq!(
                fixture.store.interface_method_linked_type(signature),
                Some(fixture.type_),
            );
            assert_eq!(
                fixture
                    .store
                    .function_signature_return_annotation(signature),
                Some((annotation, false)),
            );
            assert_eq!(
                fixture.store.callable_signature_parameter_types(signature),
                Some([type_].as_slice()),
            );
        }
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.store.callable_signature_parameter_types_len(),
                fixture.store.function_signature_return_annotations.len(),
            ),
            warm,
        );
    }

    #[test]
    fn interface_methods_accept_uncached_intrinsic_return_and_parameter_annotations() {
        let mut fixture = interface_method_fixture_with_keyword_annotation_links(false);
        for ((signature, return_annotation), parameter) in fixture
            .signatures
            .iter()
            .copied()
            .zip(fixture.return_annotations.iter().copied())
            .zip(fixture.parameters.iter().copied())
        {
            let parameter_declaration = fixture
                .store
                .symbol(parameter)
                .unwrap()
                .value_declaration()
                .unwrap();
            let parameter_annotation = fixture
                .store
                .source_direct_type_annotation(parameter_declaration)
                .unwrap();
            assert!(fixture.store.type_node_links(return_annotation).is_none());
            assert!(
                fixture
                    .store
                    .type_node_links(parameter_annotation)
                    .is_none()
            );
            assert_eq!(
                fixture.store.interface_method_linked_type(signature),
                Some(fixture.type_),
            );
            assert!(fixture.store.set_function_signature_return_annotation(
                signature,
                return_annotation,
                false,
            ));
        }

        assert!(
            fixture.store.set_callable_signature_parameter_types_batch(
                fixture
                    .signatures
                    .iter()
                    .copied()
                    .zip(fixture.parameter_types.iter().copied())
                    .map(|(signature, type_)| (signature, vec![type_]))
                    .collect(),
            )
        );

        let return_annotation = fixture.return_annotations[0];
        let wrong_type = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_type_node_links(
            return_annotation,
            TypeNodeLinks {
                resolved_type: Some(wrong_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            fixture
                .store
                .interface_method_linked_type(fixture.signatures[0]),
            None,
        );
    }

    #[test]
    fn interface_method_overloads_reject_forged_owners_signatures_and_parameters() {
        for poison in 0..3 {
            let mut fixture = interface_method_fixture();
            match poison {
                0 => {
                    let members = fixture
                        .store
                        .symbol(fixture.owner)
                        .unwrap()
                        .members()
                        .unwrap();
                    assert_eq!(
                        fixture.store.insert_symbol(
                            members,
                            EscapedName::source("run"),
                            fixture.parameters[0],
                        ),
                        Some(Some(fixture.method)),
                    );
                }
                1 => {
                    assert!(fixture.store.set_signature_links(
                        fixture.declarations[0],
                        SignatureLinks {
                            resolved_signature: ResolvedSignatureState::Resolved(
                                fixture.signatures[1],
                            ),
                            ..SignatureLinks::default()
                        },
                    ));
                }
                2 => {
                    assert!(fixture.store.set_value_symbol_links(
                        fixture.parameters[0],
                        ValueSymbolLinks {
                            resolved_type: Some(fixture.parameter_types[0]),
                            target: Some(fixture.method),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                _ => unreachable!("poison cases are bounded"),
            }

            let before = (
                fixture.store.callable_signature_parameter_types_len(),
                fixture.store.function_signature_return_annotations.len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(
                fixture
                    .store
                    .interface_method_linked_type(fixture.signatures[0]),
                None,
                "poison case {poison}",
            );
            assert!(!fixture.store.set_function_signature_return_annotation(
                fixture.signatures[0],
                fixture.return_annotations[0],
                false,
            ));
            assert!(
                !fixture
                    .store
                    .set_callable_signature_parameter_types_batch(vec![(
                        fixture.signatures[0],
                        vec![fixture.parameter_types[0]]
                    ),])
            );
            assert_eq!(
                (
                    fixture.store.callable_signature_parameter_types_len(),
                    fixture.store.function_signature_return_annotations.len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
                "poison case {poison}",
            );
        }
    }

    #[test]
    fn global_array_concat_overloads_publish_exact_generic_array_annotations() {
        let parsed = parse_source_file(concat!(
            "interface ConcatArray<T> {} ",
            "interface Array<T> { ",
            "concat(...items: ConcatArray<T>[]): T[]; ",
            "concat(...items: (T | ConcatArray<T>)[]): T[]; ",
            "} ",
            "interface ReadonlyArray<T> {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_043);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/array-concat.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let global_types = context.global_types().clone();
        let (owner, concat_owner, method, declarations, element) = {
            let store = context.store();
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            let owner = store
                .symbol_table(globals)
                .and_then(|globals| globals.get_source("Array"))
                .and_then(|owner| store.get_merged_symbol(owner))
                .unwrap();
            let concat_owner = store
                .symbol_table(globals)
                .and_then(|globals| globals.get_source("ConcatArray"))
                .and_then(|owner| store.get_merged_symbol(owner))
                .unwrap();
            let method = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("concat"))
                .unwrap();
            let declarations = store
                .symbol(method)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            let super::TypeData::Interface(array) =
                store.type_payload(global_types.array_type).unwrap().data()
            else {
                panic!("Array must own one generic interface target")
            };
            let [element] = array.reference.resolved_type_arguments.as_deref().unwrap() else {
                panic!("Array must have exactly one type parameter")
            };
            (owner, concat_owner, method, declarations, *element)
        };
        let concat_target = context.get_declared_type_of_symbol(concat_owner).unwrap();
        let plans = declarations
            .iter()
            .copied()
            .map(|declaration| {
                let NodeData::MethodSignatureDeclaration(signature) =
                    &parsed.arena.get(declaration.node).unwrap().data
                else {
                    panic!("concat must retain its method declarations")
                };
                let parameter = NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    signature.parameters.nodes[0],
                );
                let NodeData::ParameterDeclaration(parameter_data) =
                    &parsed.arena.get(parameter.node).unwrap().data
                else {
                    panic!("concat must retain its binder-owned rest parameters")
                };
                (
                    declaration,
                    context.file(file).unwrap().1.symbol(parameter).unwrap(),
                    NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        parameter_data.type_.unwrap(),
                    ),
                    NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        signature.type_.unwrap(),
                    ),
                )
            })
            .collect::<Vec<_>>();
        let store = context.store_mut_for_test();
        let concat_element =
            create_direct_generic_reference(store, concat_target, &[element], ObjectFlags::NONE)
                .unwrap();
        let combined_element = store
            .expression_union_type_with_global_types(
                &global_types,
                &[element, concat_element],
                UnionReduction::Literal,
            )
            .unwrap();
        let return_type = store
            .create_canonical_array_type(&global_types, element, false)
            .unwrap();
        let parameter_types = [concat_element, combined_element].map(|element| {
            store
                .create_canonical_array_type(&global_types, element, false)
                .unwrap()
        });
        let callable = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let mut signatures = Vec::new();
        let mut return_annotations = Vec::new();
        for ((declaration, parameter, parameter_annotation, return_annotation), parameter_type) in
            plans.iter().copied().zip(parameter_types)
        {
            assert_eq!(
                store.source_direct_type_annotation(declaration),
                Some(return_annotation),
            );
            let parameter_declaration = store
                .symbol(parameter)
                .unwrap()
                .value_declaration()
                .unwrap();
            assert_eq!(
                store.source_direct_type_annotation(parameter_declaration),
                Some(parameter_annotation),
            );
            assert!(store.set_type_node_links(
                parameter_annotation,
                TypeNodeLinks {
                    resolved_type: Some(parameter_type),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(store.set_type_node_links(
                return_annotation,
                TypeNodeLinks {
                    resolved_type: Some(return_type),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(store.set_value_symbol_links(
                parameter,
                ValueSymbolLinks {
                    resolved_type: Some(parameter_type),
                    ..ValueSymbolLinks::default()
                },
            ));
            let signature = store
                .alloc_signature(
                    SignatureFlags::HAS_REST_PARAMETER,
                    Some(declaration),
                    Vec::new(),
                    None,
                    vec![parameter],
                    Some(return_type),
                    None,
                    0,
                )
                .unwrap();
            assert!(store.set_signature_links(
                declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                },
            ));
            signatures.push(signature);
            return_annotations.push(return_annotation);
        }
        assert!(store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(callable),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            callable,
            None,
            None,
            Some(signatures.clone()),
            None,
            None,
        ));
        assert_eq!(
            store.authenticated_interface_method_owner(method),
            Some((owner, global_types.array_type)),
        );
        for (signature, annotation) in signatures.iter().copied().zip(return_annotations) {
            assert_eq!(
                store.interface_method_linked_type(signature),
                Some(callable)
            );
            assert!(store.set_function_signature_return_annotation(signature, annotation, false));
        }
        assert!(
            store.set_callable_signature_parameter_types_batch(
                signatures
                    .iter()
                    .copied()
                    .zip(parameter_types)
                    .map(|(signature, type_)| (signature, vec![type_]))
                    .collect(),
            )
        );

        let warm = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );
        for signature in signatures {
            assert_eq!(
                store.interface_method_linked_type(signature),
                Some(callable)
            );
        }
        assert_eq!(
            (
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn late_bound_unique_symbol_properties_preserve_flags_links_and_warm_identity() {
        for optional in [false, true] {
            let mut fixture = late_bound_property_fixture(optional);
            let expected_name = fixture.store.unique_symbol_name(fixture.key).unwrap();
            let before_symbols = fixture.store.symbol_len();

            let late = fixture
                .store
                .create_late_bound_property_symbol(
                    fixture.owner,
                    fixture.early,
                    fixture.key_type,
                    fixture.members,
                )
                .expect("an authenticated computed property must receive one late symbol");

            assert_eq!(fixture.store.symbol_len(), before_symbols + 1);
            let late_record = fixture.store.symbol(late).unwrap();
            let expected_flags = SymbolFlags::PROPERTY
                | SymbolFlags::TRANSIENT
                | if optional {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                };
            assert_eq!(late_record.flags(), expected_flags);
            assert_eq!(late_record.check_flags(), CheckFlags::LATE);
            assert_eq!(late_record.name(), expected_name.as_ref());
            assert_eq!(late_record.declarations(), Some(&[fixture.declaration][..]));
            assert_eq!(late_record.value_declaration(), Some(fixture.declaration));
            assert_eq!(late_record.parent(), Some(fixture.owner));
            assert_eq!(
                fixture.store.late_bound_links(fixture.early),
                Some(&LateBoundLinks {
                    late_symbol: Some(late),
                }),
            );
            assert_eq!(
                fixture.store.symbol_node_links(fixture.declaration),
                Some(&SymbolNodeLinks {
                    resolved_symbol: Some(late),
                }),
            );
            assert_eq!(
                fixture.store.value_symbol_links(late),
                Some(&ValueSymbolLinks {
                    name_type: Some(fixture.key_type),
                    ..ValueSymbolLinks::default()
                }),
            );
            assert_eq!(
                fixture
                    .store
                    .symbol_table(fixture.members)
                    .and_then(|members| members.get(expected_name.as_ref())),
                Some(late),
            );
            let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
            assert!(fixture.store.set_value_symbol_links(
                late,
                ValueSymbolLinks {
                    resolved_type: Some(number),
                    name_type: Some(fixture.key_type),
                    ..ValueSymbolLinks::default()
                },
            ));
            let warm = (
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert_eq!(
                fixture.store.create_late_bound_property_symbol(
                    fixture.owner,
                    fixture.early,
                    fixture.key_type,
                    fixture.members,
                ),
                Some(late),
            );
            assert_eq!(
                (
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn late_bound_unique_symbol_properties_reject_forged_inputs_without_publication() {
        for poison in 0..4 {
            let mut fixture = late_bound_property_fixture(true);
            let members = if poison == 0 {
                fixture
                    .store
                    .symbol(fixture.owner)
                    .unwrap()
                    .members()
                    .unwrap()
            } else {
                fixture.members
            };
            let key_type = if poison == 1 {
                fixture.store.intrinsic_bootstrap().unwrap().es_symbol_type
            } else {
                fixture.key_type
            };
            if poison == 2 {
                assert!(fixture.store.set_symbol_flags(
                    fixture.early,
                    SymbolFlags::PROPERTY,
                    CheckFlags::NONE,
                ));
            }
            if poison == 3 {
                let name = fixture.store.unique_symbol_name(fixture.key).unwrap();
                assert_eq!(
                    fixture.store.insert_symbol(members, name, fixture.early),
                    Some(None),
                );
            }
            let before = (
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert_eq!(
                fixture.store.create_late_bound_property_symbol(
                    fixture.owner,
                    fixture.early,
                    key_type,
                    members,
                ),
                None,
                "poison case {poison}",
            );
            assert_eq!(
                (
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(fixture.store.late_bound_links(fixture.early).is_none());
            assert!(
                fixture
                    .store
                    .symbol_node_links(fixture.declaration)
                    .is_none()
            );
            assert_eq!(
                fixture.store.symbol(fixture.early).unwrap().name(),
                InternalSymbolName::Computed.as_ref(),
            );
        }
    }

    #[test]
    fn global_interface_method_cache_mutations_invalidate_callable_validation() {
        for poison in 0..6 {
            let mut fixture = global_interface_method_fixture(
                "Number",
                "toFixed(fractionDigits?: number): string;",
            );
            let (_, signature) = publish_global_interface_method_fixture(&mut fixture);
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let number = bootstrap.number_type;
            let string = bootstrap.string_type;
            fixture.store.union_cache_needs_validation = false;

            match poison {
                0 => {
                    assert!(fixture.store.set_value_symbol_links(
                        fixture.parameter.unwrap().0,
                        ValueSymbolLinks {
                            resolved_type: Some(string),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                1 => {
                    assert!(fixture.store.set_value_symbol_links(
                        fixture.method,
                        ValueSymbolLinks {
                            resolved_type: Some(number),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                2 => {
                    assert!(fixture.store.set_type_node_links(
                        fixture.return_annotation,
                        TypeNodeLinks {
                            resolved_type: Some(number),
                            ..TypeNodeLinks::default()
                        },
                    ));
                }
                3 => {
                    assert!(
                        fixture
                            .store
                            .set_signature_resolved_return_type(signature, Some(number),)
                    );
                }
                4 => {
                    let forged = fixture
                        .store
                        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(fixture.method))
                        .unwrap();
                    assert!(fixture.store.set_value_symbol_links(
                        fixture.method,
                        ValueSymbolLinks {
                            resolved_type: Some(forged),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                5 => {
                    let forged = fixture
                        .store
                        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(fixture.owner))
                        .unwrap();
                    assert!(fixture.store.set_structured_type_members(
                        forged,
                        None,
                        None,
                        Some(vec![signature]),
                        None,
                        None,
                    ));
                    assert!(fixture.store.set_value_symbol_links(
                        fixture.method,
                        ValueSymbolLinks {
                            resolved_type: Some(forged),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                _ => unreachable!("poison cases are bounded"),
            }
            assert!(fixture.store.union_cache_needs_validation, "case {poison}");
            assert_eq!(
                fixture
                    .store
                    .global_interface_method_callable_type(signature),
                None,
                "case {poison}",
            );
        }
    }

    #[test]
    fn global_interface_methods_reject_unowned_signatures_and_foreign_globals() {
        let mut fixture = global_interface_method_fixture("String", "toLowerCase(): string;");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let globals = bootstrap.globals;
        let string = bootstrap.string_type;
        let unowned = fixture
            .store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(fixture.declaration),
                Vec::new(),
                None,
                Vec::new(),
                Some(string),
                None,
                0,
            )
            .unwrap();
        assert!(
            !fixture
                .store
                .set_callable_signature_parameter_types_batch(vec![(unowned, Vec::new())]),
        );

        let (_, signature) = publish_global_interface_method_fixture(&mut fixture);
        let forged = fixture
            .store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::INTERFACE,
                EscapedName::source("String"),
            ))
            .unwrap();
        assert!(
            fixture
                .store
                .insert_symbol(globals, EscapedName::source("String"), forged)
                .is_some(),
        );
        assert_eq!(
            fixture
                .store
                .authenticated_global_interface_method(fixture.method),
            None,
        );
        assert_eq!(
            fixture
                .store
                .global_interface_method_callable_type(signature),
            None,
        );
    }

    #[test]
    fn named_interface_keyof_constraints_require_exact_operator_and_cached_keys() {
        let parsed = parse_source_file(concat!(
            "interface Types { first: string; second: number } ",
            "type Keys = keyof Types;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_012);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/named-keyof.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let keyof = node_ref_of_kind(&parsed.arena, file, SyntaxKind::TypeOperator);
        let result = context.get_type_from_type_node(keyof).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;

        assert!(
            context
                .store()
                .source_type_node_result_is_exact(keyof, result, &[])
        );
        assert!(
            context
                .store()
                .source_direct_constraint_has_leaf_base(result, Some(keyof)),
        );
        assert!(
            !context
                .store()
                .source_direct_constraint_has_leaf_base(result, None),
        );

        let store = context.store_mut_for_test();
        store.source_node_facts.get_mut(&keyof.arena).unwrap()[keyof.node.index()]
            .as_mut()
            .unwrap()
            .type_operator = Some(SyntaxKind::ReadonlyKeyword);
        assert!(!store.source_type_node_result_is_exact(keyof, result, &[]));
        store.source_node_facts.get_mut(&keyof.arena).unwrap()[keyof.node.index()]
            .as_mut()
            .unwrap()
            .type_operator = Some(SyntaxKind::KeyOfKeyword);
        assert!(store.set_type_node_links(
            keyof,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(!store.source_type_node_result_is_exact(keyof, result, &[]));
    }

    #[test]
    fn inferred_generic_void_publication_requires_exact_empty_body_proof() {
        let parsed = parse_source_file("function empty<T>() {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_005);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/inferred-generic.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let declaration = node_ref_of_kind(&parsed.arena, file, SyntaxKind::FunctionDeclaration);
        let owner = bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&store, &host, declaration, owner, None).unwrap();
        assert!(plan.type_parameter_syntax.inferred_empty_body_is_exact());
        let parameter = plan.type_parameters[0];
        let type_parameter = execute_type_parameter(&mut store, parameter.symbol);
        let (no_constraint, void) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.no_constraint_type, bootstrap.void_type)
        };
        let resolved = super::ResolvedSourceCallableTypeParameter {
            provenance: super::SourceCallableTypeParameterProvenance {
                declaration: parameter.declaration,
                symbol: parameter.symbol,
                type_parameter,
                constraint: None,
                default_type: None,
            },
            constraint: no_constraint,
            default_type: no_constraint,
        };
        let request = |annotation, parameters, minimum, null_literal, return_parameter| {
            super::PreparedSourceGenericCallablePublication {
                syntax: &plan.type_parameter_syntax,
                family: plan.family,
                declaration,
                owner_symbol: owner,
                owner_parent: plan.owner_parent,
                export_local: plan.export_local,
                type_parameters: vec![resolved],
                query_evidence: None,
                parameters,
                flags: plan.flags,
                min_argument_count: minimum,
                return_annotation: annotation,
                return_null_literal_identity: null_literal,
                generic_return_type_parameter: return_parameter,
                array_targets: plan.array_targets,
            }
        };
        let before = (
            store.type_len(),
            store.signature_len(),
            store.source_callable_provenance_lengths(),
            store.function_signature_return_annotations.len(),
            store.checker_link_allocated_lengths(),
        );

        for invalid in [
            request(None, vec![owner], 0, false, None),
            request(None, Vec::new(), 1, false, None),
            request(None, Vec::new(), 0, true, None),
            request(None, Vec::new(), 0, false, Some(type_parameter)),
            request(Some(plan.body), Vec::new(), 0, false, None),
        ] {
            assert_eq!(store.publish_source_generic_callable(invalid), None);
            assert_eq!(
                (
                    store.type_len(),
                    store.signature_len(),
                    store.source_callable_provenance_lengths(),
                    store.function_signature_return_annotations.len(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }

        let (type_, signature) = store
            .publish_source_generic_callable(request(None, Vec::new(), 0, false, None))
            .unwrap();
        assert_eq!(
            store
                .source_callable_provenance(type_)
                .unwrap()
                .return_provenance,
            super::SourceCallableReturnProvenance::Inferred,
        );
        assert_eq!(store.function_signature_return_annotation(signature), None);
        assert_eq!(
            store.signature(signature).unwrap().type_parameters(),
            [type_parameter]
        );
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            None
        );
        assert!(store.set_structured_type_members(
            type_,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        assert!(store.set_callable_signature_parameter_types_batch(vec![(signature, Vec::new())]));
        assert!(store.set_signature_resolved_return_type(signature, Some(void)));
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            Some(void)
        );
    }

    #[test]
    fn inferred_generic_void_publication_preserves_value_parameter_provenance() {
        let parsed = parse_source_file("function empty<T extends hm>(value: T) {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_017);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/inferred-generic-parameter.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let declaration = node_ref_of_kind(&parsed.arena, file, SyntaxKind::FunctionDeclaration);
        let owner = bound.symbol(declaration).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_source_callable(&store, &host, declaration, owner, None).unwrap();
        let generic = plan.type_parameters[0];
        let value = plan.parameters[0].symbol;
        let type_parameter = execute_type_parameter(&mut store, generic.symbol);
        let (no_constraint, error_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.no_constraint_type, bootstrap.error_type)
        };
        let constraint = generic
            .constraint
            .expect("the supported parameter-bearing generic has an unresolved constraint");
        assert!(store.set_type_node_links(
            constraint,
            TypeNodeLinks {
                resolved_type: Some(error_type),
                ..TypeNodeLinks::default()
            },
        ));
        let resolved = super::ResolvedSourceCallableTypeParameter {
            provenance: super::SourceCallableTypeParameterProvenance {
                declaration: generic.declaration,
                symbol: generic.symbol,
                type_parameter,
                constraint: Some(constraint),
                default_type: None,
            },
            constraint: error_type,
            default_type: no_constraint,
        };
        let (callable, signature) = store
            .publish_source_generic_callable(super::PreparedSourceGenericCallablePublication {
                syntax: &plan.type_parameter_syntax,
                family: plan.family,
                declaration,
                owner_symbol: owner,
                owner_parent: plan.owner_parent,
                export_local: plan.export_local,
                type_parameters: vec![resolved],
                query_evidence: None,
                parameters: vec![value],
                flags: plan.flags,
                min_argument_count: 1,
                return_annotation: None,
                return_null_literal_identity: false,
                generic_return_type_parameter: None,
                array_targets: plan.array_targets,
            })
            .expect("proven empty generic bodies may retain value parameters");
        assert_eq!(
            store
                .source_callable_provenance(callable)
                .unwrap()
                .return_provenance,
            super::SourceCallableReturnProvenance::Inferred,
        );
        let signature = store.signature(signature).unwrap();
        assert_eq!(signature.type_parameters(), [type_parameter]);
        assert_eq!(signature.parameters(), [value]);
        assert_eq!(signature.min_argument_count(), 1);
        assert_eq!(signature.resolved_return_type(), None);
    }

    #[test]
    fn direct_interface_heritage_authenticates_optional_second_base_atomically() {
        fn interface(
            store: &mut CanonicalTypeMapperStore,
            name: &str,
            resolve_members: bool,
        ) -> (crate::semantic::SemanticSymbolId, crate::semantic::TypeId) {
            let symbol = store
                .alloc_symbol(SymbolData::new(
                    SymbolFlags::INTERFACE,
                    EscapedName::source(name),
                ))
                .unwrap();
            let type_ = store
                .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
                .unwrap();
            assert!(store.set_declared_type_links(
                symbol,
                DeclaredTypeLinks {
                    declared_type: Some(type_),
                    ..DeclaredTypeLinks::default()
                },
            ));
            if resolve_members {
                assert!(store.set_interface_base_resolution(type_, true, None, None));
                assert!(store.set_interface_declared_members(type_, true, None, None, None, None,));
                assert!(store.set_structured_type_members(type_, None, None, None, None, None,));
            }
            (symbol, type_)
        }

        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let (owner_symbol, owner_type) = interface(&mut store, "Derived", false);
        let (single_owner, single_type) = interface(&mut store, "Single", false);
        let (base_symbol, base_type) = interface(&mut store, "First", true);
        let (second_symbol, second_type) = interface(&mut store, "Second", true);
        let (unresolved_symbol, unresolved_type) = interface(&mut store, "Unresolved", false);
        let mut foreign = CanonicalTypeMapperStore::new();
        foreign
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let foreign_base = interface(&mut foreign, "Foreign", true);
        let before = (
            store.direct_interface_heritage_provenance.len(),
            store.type_len(),
            store.relation_state_snapshot(),
        );

        for second_base in [
            (base_symbol, base_type),
            (second_symbol, base_type),
            (owner_symbol, owner_type),
            (unresolved_symbol, unresolved_type),
            foreign_base,
        ] {
            assert!(!store.publish_direct_interface_heritage_provenance(
                owner_type,
                super::DirectInterfaceHeritageProvenance {
                    owner_symbol,
                    bases: vec![(base_symbol, base_type), second_base],
                },
            ));
            assert_eq!(
                (
                    store.direct_interface_heritage_provenance.len(),
                    store.type_len(),
                    store.relation_state_snapshot(),
                ),
                before,
            );
        }

        let paired = super::DirectInterfaceHeritageProvenance {
            owner_symbol,
            bases: vec![(base_symbol, base_type), (second_symbol, second_type)],
        };
        assert!(store.try_reserve_direct_interface_heritage_provenance(2));
        assert!(store.publish_direct_interface_heritage_provenance(owner_type, paired.clone()));
        assert_eq!(
            store.direct_interface_heritage_provenance(owner_type),
            Some(&paired)
        );
        assert!(!store.publish_direct_interface_heritage_provenance(owner_type, paired));

        let single = super::DirectInterfaceHeritageProvenance {
            owner_symbol: single_owner,
            bases: vec![(base_symbol, base_type)],
        };
        assert!(store.publish_direct_interface_heritage_provenance(single_type, single.clone()));
        assert_eq!(
            store.direct_interface_heritage_provenance(single_type),
            Some(&single)
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Reuse one real source proof for rejection, restoration, and duplicate publication.
    fn repeated_interface_heritage_publication_keeps_all_source_contributions() {
        let parsed = parse_source_file(concat!(
            "interface Base { inherited: number }\n",
            "interface Other { other: string }\n",
            "interface Derived extends Base {}\n",
            "interface Derived extends Base {}\n",
            "interface Derived extends Base {}\n",
            "interface Derived extends Base {}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_013);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/repeated-base-publication.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let [owner, base, other] = ["Derived", "Base", "Other"].map(|name| {
            context
                .store()
                .symbol_table(context.globals())
                .and_then(|globals| globals.get_source(name))
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap()
        });
        let store = context.store_mut_for_test();
        let [derived, base_type, other_type] = [owner, base, other].map(|symbol| {
            store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .unwrap()
        });
        let original = store
            .direct_interface_heritage_provenance(derived)
            .cloned()
            .unwrap();
        let edge = (base, base_type);
        assert_eq!(original.owner_symbol, owner);
        assert_eq!(original.bases, vec![edge; 4]);
        assert_eq!(
            store.direct_interface_heritage_provenance.remove(&derived),
            Some(original.clone()),
        );
        assert!(store.try_reserve_direct_interface_heritage_provenance(1));
        let snapshot = |store: &CanonicalTypeMapperStore| {
            let TypeData::Interface(interface) = store.type_payload(derived).unwrap().data() else {
                panic!("the source must keep its declared interface");
            };
            assert_eq!(
                interface.resolved_base_types.as_deref(),
                Some(&[base_type; 4][..]),
            );
            (
                store.direct_interface_heritage_provenance(derived).cloned(),
                store.direct_interface_heritage_provenance.len(),
                store.type_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.signature_len(),
                store.index_info_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
                interface.clone(),
            )
        };
        let before = snapshot(store);
        for (candidate_owner, bases) in [
            (owner, Vec::new()),
            (owner, vec![edge; 3]),
            (owner, vec![edge; 5]),
            (other, original.bases.clone()),
            (owner, vec![edge, (other, base_type), edge, edge]),
            (owner, vec![edge, edge, (base, other_type), edge]),
            (owner, vec![edge, (other, other_type), edge, edge]),
        ] {
            assert!(!store.publish_direct_interface_heritage_provenance(
                derived,
                super::DirectInterfaceHeritageProvenance {
                    owner_symbol: candidate_owner,
                    bases,
                },
            ));
            assert_eq!(snapshot(store), before);
        }
        assert!(store.publish_direct_interface_heritage_provenance(derived, original.clone()));
        assert_eq!(
            store.direct_interface_heritage_provenance(derived),
            Some(&original),
        );
        let restored = snapshot(store);
        assert!(!store.publish_direct_interface_heritage_provenance(derived, original.clone()));
        assert_eq!(snapshot(store), restored);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep real global ownership, failed publication, and exact retry together.
    fn secondary_global_base_publication_requires_the_original_owner_proof() {
        let parsed = parse_source_file(concat!(
            "interface First { first: number }\n",
            "interface Second { second: string }\n",
            "declare var Second: unknown;\n",
            "interface Derived extends First, Second {}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(90_014);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/secondary-global-base.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let [owner, first, second] = ["Derived", "First", "Second"].map(|name| {
            context
                .store()
                .symbol_table(context.globals())
                .and_then(|globals| globals.get_source(name))
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap()
        });
        let store = context.store_mut_for_test();
        let [derived, first_type, second_type] = [owner, first, second].map(|symbol| {
            store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .unwrap()
        });
        let flags = store.symbol(second).unwrap().flags();
        assert!(flags.contains(SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE));
        assert_ne!(flags, SymbolFlags::INTERFACE);
        assert!(
            crate::semantic::object_members::authenticated_nongeneric_global_interface_owner(
                store, second,
            )
        );
        let value = store.value_symbol_links(second).cloned().unwrap();
        assert_eq!(
            value.resolved_type,
            Some(store.intrinsic_bootstrap().unwrap().unknown_type),
        );
        assert_ne!(value.resolved_type, Some(second_type));
        let original = store
            .direct_interface_heritage_provenance(derived)
            .cloned()
            .unwrap();
        assert_eq!(original.owner_symbol, owner);
        assert_eq!(original.bases, [(first, first_type), (second, second_type)]);
        assert_eq!(
            store.direct_interface_heritage_provenance.remove(&derived),
            Some(original.clone()),
        );
        assert!(store.try_reserve_direct_interface_heritage_provenance(1));

        let globals = store.source_global_bindings.take().unwrap();
        let missing_proof = format!("{store:?}");
        for _ in 0..2 {
            assert!(
                !store.publish_direct_interface_heritage_provenance(derived, original.clone(),)
            );
            assert_eq!(format!("{store:?}"), missing_proof);
        }
        store.source_global_bindings = Some(globals);
        assert!(
            crate::semantic::object_members::authenticated_nongeneric_global_interface_owner(
                store, second,
            )
        );

        assert!(store.set_symbol_flags(second, flags | SymbolFlags::CLASS, CheckFlags::NONE));
        let damaged_owner = format!("{store:?}");
        for _ in 0..2 {
            assert!(
                !store.publish_direct_interface_heritage_provenance(derived, original.clone(),)
            );
            assert_eq!(format!("{store:?}"), damaged_owner);
        }
        assert!(store.set_symbol_flags(second, flags, CheckFlags::NONE));
        assert!(store.publish_direct_interface_heritage_provenance(derived, original.clone()));
        assert_eq!(
            store.direct_interface_heritage_provenance(derived),
            Some(&original),
        );
        assert_eq!(store.value_symbol_links(second), Some(&value));
        let restored = format!("{store:?}");
        for _ in 0..2 {
            assert!(
                !store.publish_direct_interface_heritage_provenance(derived, original.clone(),)
            );
            assert_eq!(format!("{store:?}"), restored);
        }
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
