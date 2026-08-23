//! Exact dependency-closed fast, primitive-union, property, and function relations.
//!
//! This module ports `isTypeRelatedTo`, `isSimpleTypeRelatedTo`, and their
//! no-diagnostic entry points plus primitive/literal/nullable unions and the
//! property-object and annotated non-generic function slices of
//! `recursiveTypeRelatedTo` for assignable, comparable, subtype, and
//! strict-subtype relations, including fresh excess-property checks,
//! strict/exact optional-property relations, and single call signatures, from pinned
//! `internal/checker/relater.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Unsupported structural paths
//! return [`RelationUnavailable`] instead of being misreported as unrelated.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};

use super::{
    CanonicalGlobalTypeInitializationError, CanonicalGlobalTypes, DeclaredTypeHost,
    ResolvedSignatureState, SignatureLinks,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
    bootstrap::LiteralTypeCacheError,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    callables::{
        CallableFamily, StoredSingleCallableValidation, ValidatedSingleCallable,
        validate_stored_single_callable,
    },
    classes::{ClassHeritageMembersValidation, validate_class_heritage_members},
    derived_types::DerivedObjectLiteralValidation,
    enums,
    ids::{IndexInfoId, SignatureId, TypeId},
    indexed_access_types::{is_template_pattern_index_key, template_pattern_index_matches_name},
    instantiated_members::{GenericInterfaceMemberError, validate_generic_interface_members},
    intersection_types::IntersectionTypeProjection,
    links::{MembersOrExportsResolutionKind, ValueSymbolLinks},
    mapper::TypeMapper,
    relation::{
        ExpandingFlags, IntersectionState, RecursionFlags, RecursionIdentityUnavailable,
        RelationComparisonResult, RelationKeyUnavailable, RelationKind, SignatureCheckMode,
    },
    signatures::{SignatureFlags, Ternary},
    store::{RelationObservationToken, SemanticStore, SourceNodeParent},
    structured_members::{
        InterfaceHeritageMembersValidation, validate_interface_heritage_members,
        validate_planned_interface_heritage_members,
    },
    type_records::{
        CacheHashKey, ConstrainedTypeData, StructuredTypeData, TypeCacheState, TypeData, TypeRecord,
    },
    types::{ObjectFlags, TypeFlags},
};

/// A canonical record or checker capability needed to answer a relation was
/// unavailable. No variant is a negative relation result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelationUnavailable {
    MissingBootstrap,
    Type(TypeId),
    Symbol(SemanticSymbolId),
    MalformedLiteral(TypeId),
    MalformedUnion(TypeId),
    MalformedIntersection(TypeId),
    UnsupportedUnionConstituent(TypeId),
    InvalidUnionAlias(SemanticSymbolId),
    InvalidUnionPreparation(TypeId),
    UnionValidationCapacity(TypeId),
    MalformedStructuredType(TypeId),
    MalformedEnumType(TypeId),
    EnumRelation {
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    },
    LateBoundMembers(SemanticSymbolId),
    InvalidSymbolMembers(SemanticSymbolId),
    RelationKeyType(TypeId),
    RelationKeyTypeReferenceArguments(TypeId),
    RelationKeyTypeReferenceTarget(TypeId),
    RelationKeyTypeParameterConstraint(TypeId),
    RelationKeyCyclicGenericArguments(TypeId),
    InvalidUnknownLikeUnionState(TypeId),
    UnresolvedStructuredMembers(TypeId),
    UnsupportedStructuredType(TypeId),
    InvalidStructuredMembers(TypeId),
    StructuredSignatures(TypeId),
    UnresolvedFunctionType(TypeId),
    UnresolvedSignatureReturn(SignatureId),
    MalformedFunctionType(TypeId),
    StrictFunctionTypesOptionMismatch {
        established: bool,
        requested: bool,
    },
    StructuredIndexInfos(TypeId),
    UnsupportedProperty(SemanticSymbolId),
    UnresolvedPropertyType(SemanticSymbolId),
    StrictOptionalProperty(SemanticSymbolId),
    UnresolvedGlobalObject(SemanticSymbolId),
    CanonicalGlobalType(CanonicalGlobalTypeInitializationError),
    UnavailableCanonicalArrayTarget(TypeId),
    MalformedCanonicalArrayReference(TypeId),
    StructuralRelation {
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
    },
}

impl std::fmt::Display for RelationUnavailable {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingBootstrap => {
                formatter.write_str("type relations require intrinsic checker bootstrap")
            }
            Self::Type(type_id) => write!(formatter, "type {type_id:?} is not store-owned"),
            Self::Symbol(symbol) => write!(formatter, "symbol {symbol:?} is not store-owned"),
            Self::MalformedLiteral(type_id) => {
                write!(formatter, "type {type_id:?} has an invalid literal payload")
            }
            Self::MalformedUnion(type_id) => {
                write!(formatter, "type {type_id:?} is not a canonical union")
            }
            Self::MalformedIntersection(type_id) => {
                write!(
                    formatter,
                    "type {type_id:?} is not a canonical intersection"
                )
            }
            Self::UnsupportedUnionConstituent(type_id) => write!(
                formatter,
                "type {type_id:?} is outside the canonical primitive-union relation domain"
            ),
            Self::InvalidUnionAlias(symbol) => write!(
                formatter,
                "union alias {symbol:?} is not a canonical non-generic alias"
            ),
            Self::InvalidUnionPreparation(type_id) => write!(
                formatter,
                "union relation for {type_id:?} received an invalid prepared query"
            ),
            Self::UnionValidationCapacity(type_id) => write!(
                formatter,
                "validating union type {type_id:?} exceeded representable capacity"
            ),
            Self::MalformedStructuredType(type_id) => {
                write!(
                    formatter,
                    "type {type_id:?} has an invalid structured payload"
                )
            }
            Self::MalformedEnumType(type_id) => {
                write!(formatter, "enum type {type_id:?} has no canonical symbol")
            }
            Self::EnumRelation { source, target } => write!(
                formatter,
                "enum relation between {source:?} and {target:?} requires enum member semantics"
            ),
            Self::LateBoundMembers(symbol) => write!(
                formatter,
                "empty-object classification for {symbol:?} requires late-bound members"
            ),
            Self::InvalidSymbolMembers(symbol) => {
                write!(
                    formatter,
                    "symbol {symbol:?} references an invalid member table"
                )
            }
            Self::RelationKeyType(type_id) => {
                write!(formatter, "relation key cannot read type {type_id:?}")
            }
            Self::RelationKeyTypeReferenceArguments(type_id) => write!(
                formatter,
                "relation key requires resolved arguments for {type_id:?}"
            ),
            Self::RelationKeyTypeReferenceTarget(type_id) => write!(
                formatter,
                "relation key requires a resolved target for {type_id:?}"
            ),
            Self::RelationKeyTypeParameterConstraint(type_id) => write!(
                formatter,
                "relation key requires the constraint state of {type_id:?}"
            ),
            Self::RelationKeyCyclicGenericArguments(type_id) => write!(
                formatter,
                "relation key found cyclic generic arguments at {type_id:?}"
            ),
            Self::InvalidUnknownLikeUnionState(type_id) => write!(
                formatter,
                "type {type_id:?} rejected its unknown-like union cache state"
            ),
            Self::UnresolvedStructuredMembers(type_id) => write!(
                formatter,
                "type {type_id:?} requires resolved structured members"
            ),
            Self::UnsupportedStructuredType(type_id) => write!(
                formatter,
                "type {type_id:?} is outside the property-only object relation domain"
            ),
            Self::InvalidStructuredMembers(type_id) => write!(
                formatter,
                "type {type_id:?} has inconsistent resolved member caches"
            ),
            Self::StructuredSignatures(type_id) => write!(
                formatter,
                "type {type_id:?} requires call or construct signature relations"
            ),
            Self::UnresolvedFunctionType(type_id) => write!(
                formatter,
                "function type {type_id:?} has not finished publishing its signature"
            ),
            Self::UnresolvedSignatureReturn(signature) => write!(
                formatter,
                "signature {signature:?} requires lazy return-type resolution"
            ),
            Self::MalformedFunctionType(type_id) => write!(
                formatter,
                "function type {type_id:?} has inconsistent callable caches"
            ),
            Self::StrictFunctionTypesOptionMismatch {
                established,
                requested,
            } => write!(
                formatter,
                "relation store retained strictFunctionTypes={established}, but the query requested {requested}"
            ),
            Self::StructuredIndexInfos(type_id) => write!(
                formatter,
                "type {type_id:?} requires index-signature relations"
            ),
            Self::UnsupportedProperty(symbol) => write!(
                formatter,
                "property symbol {symbol:?} is outside the ordinary property relation domain"
            ),
            Self::UnresolvedPropertyType(symbol) => write!(
                formatter,
                "property symbol {symbol:?} has no resolved value type"
            ),
            Self::StrictOptionalProperty(symbol) => write!(
                formatter,
                "optional property symbol {symbol:?} requires strict optional-union semantics"
            ),
            Self::UnresolvedGlobalObject(symbol) => write!(
                formatter,
                "global Object symbol {symbol:?} has no resolved declared object type"
            ),
            Self::CanonicalGlobalType(error) => {
                write!(
                    formatter,
                    "canonical relation global is unavailable: {error}"
                )
            }
            Self::UnavailableCanonicalArrayTarget(type_id) => write!(
                formatter,
                "type {type_id:?} is a missing canonical Array target fallback"
            ),
            Self::MalformedCanonicalArrayReference(type_id) => write!(
                formatter,
                "type {type_id:?} is not a canonical Array reference or array-literal clone"
            ),
            Self::StructuralRelation {
                source,
                target,
                relation,
            } => write!(
                formatter,
                "uncached {relation:?} relation from {source:?} to {target:?} requires structural comparison"
            ),
        }
    }
}

impl std::error::Error for RelationUnavailable {}

fn validate_direct_interface_heritage_relation_endpoint(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    type_: TypeId,
) -> Result<(), RelationUnavailable> {
    if store.direct_interface_heritage_provenance(type_).is_some()
        && validate_interface_heritage_members(store, type_)
            != InterfaceHeritageMembersValidation::Valid
    {
        return Err(RelationUnavailable::InvalidStructuredMembers(type_));
    }
    Ok(())
}

fn validate_class_members_relation_endpoint(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    type_: TypeId,
) -> Result<(), RelationUnavailable> {
    if validate_class_heritage_members(store, type_) == ClassHeritageMembersValidation::Malformed {
        return Err(RelationUnavailable::InvalidStructuredMembers(type_));
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct RelationBootstrapFacts {
    strict_null_checks: bool,
    exact_optional_property_types: bool,
    any_type: TypeId,
    void_type: TypeId,
    wildcard_type: TypeId,
    any_function_type: TypeId,
    never_type: TypeId,
    undefined_type: TypeId,
    missing_type: TypeId,
    string_type: TypeId,
    number_type: TypeId,
    bigint_type: TypeId,
}

#[derive(Clone, Copy)]
struct RelationGlobalTypes {
    array_targets: CanonicalArrayTargets,
    string_wrapper: TypeId,
    number_wrapper: TypeId,
    boolean_wrapper: TypeId,
}

impl RelationGlobalTypes {
    const fn from_global_types(global_types: &CanonicalGlobalTypes) -> Self {
        Self {
            array_targets: CanonicalArrayTargets::from_global_types(global_types),
            string_wrapper: global_types.string_type,
            number_wrapper: global_types.number_type,
            boolean_wrapper: global_types.boolean_type,
        }
    }

    fn contains_array_target(self, target: TypeId) -> bool {
        target == self.array_targets.array_type()
            || target == self.array_targets.readonly_array_type()
    }

    fn apparent_primitive_type(self, flags: TypeFlags) -> Option<TypeId> {
        if flags.intersects(TypeFlags::STRING_LIKE) {
            Some(self.string_wrapper)
        } else if flags.intersects(TypeFlags::NUMBER_LIKE) {
            Some(self.number_wrapper)
        } else if flags.intersects(TypeFlags::BOOLEAN_LIKE) {
            Some(self.boolean_wrapper)
        } else {
            None
        }
    }
}

const PINNED_RELATION_STACK_DEPTH: usize = 100;
const PINNED_EXPANDING_DEPTH: usize = 3;

struct ResolvedObjectMembers {
    members: Option<SymbolTableId>,
    properties: Vec<SemanticSymbolId>,
    index_infos: Vec<IndexInfoId>,
    property_origin: ObjectPropertyOrigin,
    call_signature: Option<ValidatedSingleCallable>,
    exact_callable: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CanonicalArrayReferenceArguments {
    Related { source: TypeId, target: TypeId },
    Unrelated,
}

/// One validated own property from the exact property-only object domain.
///
/// This projection deliberately omits apparent/global members and index
/// signatures. Callers can therefore distinguish an absent own property from
/// a member path that the installed semantic slice cannot answer exactly.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ResolvedOwnProperty {
    pub(super) symbol: SemanticSymbolId,
    pub(super) type_: TypeId,
    pub(super) optional: bool,
    pub(super) readonly: bool,
}

#[derive(Clone, Copy)]
enum ObjectPropertyOrigin {
    Declared,
    ValidatedClass,
    GenericReference(TypeId),
    Intersection(TypeId),
    FreshObjectLiteral(SemanticSymbolId),
    DerivedObjectLiteral {
        owner: SemanticSymbolId,
        receiver: TypeId,
    },
}

impl ObjectPropertyOrigin {
    fn is_declared(self) -> bool {
        matches!(self, Self::Declared | Self::ValidatedClass)
    }
}

/// One validated property in a declared property-only object type.
///
/// This is the shared read-only boundary used by contextual typing and object
/// diagnostics. The vector containing these records retains target declaration
/// order; name lookup never observes `HashMap` iteration order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedDeclaredProperty {
    pub(super) symbol: SemanticSymbolId,
    pub(super) name: EscapedName,
    pub(super) type_: TypeId,
    pub(super) optional: bool,
    pub(super) declaration: NodeRef,
}

/// Ordered, name-indexed view of one validated declared property-only object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedDeclaredPropertyObject {
    properties: Vec<ResolvedDeclaredProperty>,
    by_name: HashMap<EscapedName, usize>,
}

impl ResolvedDeclaredPropertyObject {
    pub(super) fn properties(&self) -> &[ResolvedDeclaredProperty] {
        &self.properties
    }

    pub(super) fn get_source(&self, name: &str) -> Option<&ResolvedDeclaredProperty> {
        self.by_name
            .get(&EscapedName::source(name))
            .map(|index| &self.properties[*index])
    }
}

#[derive(Clone, Copy)]
enum CanonicalObjectLiteralRawMembers<'store> {
    Nil,
    Allocated(&'store ts_binder::semantic::SymbolTable),
}

#[derive(Default)]
struct PendingRelationCache {
    latest: HashMap<CacheHashKey, RelationComparisonResult>,
    writes: Vec<(CacheHashKey, RelationComparisonResult)>,
}

impl PendingRelationCache {
    fn get<MapperPayload>(
        &self,
        store: &SemanticStore<TypeRecord, MapperPayload>,
        relation: RelationKind,
        key: CacheHashKey,
    ) -> RelationComparisonResult {
        self.latest
            .get(&key)
            .copied()
            .unwrap_or_else(|| store.relation_cache_get(relation, key))
    }

    fn set(&mut self, key: CacheHashKey, result: RelationComparisonResult) {
        self.latest.insert(key, result);
        self.writes.push((key, result));
    }
}

struct RelaterSession<'store> {
    store: &'store mut SemanticStore<TypeRecord, TypeMapper>,
    relation: RelationKind,
    bootstrap: RelationBootstrapFacts,
    global_types: Option<RelationGlobalTypes>,
    strict_function_types: Option<bool>,
    validated_unions: HashMap<TypeId, Vec<TypeId>>,
    observation: RelationObservationToken,
    pending: PendingRelationCache,
    maybe_keys: Vec<CacheHashKey>,
    maybe_keys_set: HashSet<CacheHashKey>,
    source_stack: Vec<TypeId>,
    target_stack: Vec<TypeId>,
    active_signature_pairs: HashSet<(SignatureId, SignatureId, u32)>,
    expanding_flags: ExpandingFlags,
    overflow: bool,
    relation_count: isize,
    stack_depth_limit: usize,
}

impl<'store> RelaterSession<'store> {
    fn new(
        store: &'store mut SemanticStore<TypeRecord, TypeMapper>,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
    ) -> Self {
        Self::new_with_global_types_and_options(store, relation, bootstrap, None, None)
    }

    fn new_with_global_types(
        store: &'store mut SemanticStore<TypeRecord, TypeMapper>,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
        global_types: Option<RelationGlobalTypes>,
    ) -> Self {
        Self::new_with_global_types_and_options(store, relation, bootstrap, global_types, None)
    }

    fn new_with_global_types_and_options(
        store: &'store mut SemanticStore<TypeRecord, TypeMapper>,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
        global_types: Option<RelationGlobalTypes>,
        strict_function_types: Option<bool>,
    ) -> Self {
        let relation_count = store.relation_comparison_budget(relation);
        Self::new_with_limits_and_global_types(
            store,
            relation,
            bootstrap,
            global_types,
            strict_function_types,
            relation_count,
            PINNED_RELATION_STACK_DEPTH,
        )
    }

    #[cfg(test)]
    fn new_with_limits(
        store: &'store mut SemanticStore<TypeRecord, TypeMapper>,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
        relation_count: isize,
        stack_depth_limit: usize,
    ) -> Self {
        Self::new_with_limits_and_global_types(
            store,
            relation,
            bootstrap,
            None,
            None,
            relation_count,
            stack_depth_limit,
        )
    }

    fn new_with_limits_and_global_types(
        store: &'store mut SemanticStore<TypeRecord, TypeMapper>,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
        global_types: Option<RelationGlobalTypes>,
        strict_function_types: Option<bool>,
        relation_count: isize,
        stack_depth_limit: usize,
    ) -> Self {
        let observation = store
            .begin_relation_read_observation()
            .expect("nested relation read observations are not supported");
        Self {
            store,
            relation,
            bootstrap,
            global_types,
            strict_function_types,
            validated_unions: HashMap::new(),
            observation,
            pending: PendingRelationCache::default(),
            maybe_keys: Vec::new(),
            maybe_keys_set: HashSet::new(),
            source_stack: Vec::new(),
            target_stack: Vec::new(),
            active_signature_pairs: HashSet::new(),
            expanding_flags: ExpandingFlags::NONE,
            overflow: false,
            relation_count,
            stack_depth_limit,
        }
    }

    fn finish(
        mut self,
        source: TypeId,
        target: TypeId,
        result: Ternary,
    ) -> Result<bool, RelationUnavailable> {
        if self.overflow {
            let key = self
                .store
                .relation_key_if_available(
                    source,
                    target,
                    IntersectionState::NONE,
                    self.relation.is_identity(),
                    false,
                )
                .map_err(relation_key_unavailable)?
                .key();
            let overflow = if self.relation_count <= 0 {
                RelationComparisonResult::COMPLEXITY_OVERFLOW
            } else {
                RelationComparisonResult::STACK_DEPTH_OVERFLOW
            };
            self.pending
                .set(key, RelationComparisonResult::FAILED | overflow);
        }
        self.commit_pending_writes();
        Ok(result != Ternary::False)
    }

    fn finish_without_specialized_root_cache(mut self, result: Ternary) -> bool {
        self.commit_pending_writes();
        result != Ternary::False
    }

    fn commit_pending_writes(&mut self) {
        if self.pending.writes.is_empty() {
            // The session's Drop path discards provisional reads from a query
            // that did not publish a physical relation-cache entry.
            return;
        }
        let committed = self.store.commit_relation_cache_writes(
            self.observation,
            self.relation,
            std::mem::take(&mut self.pending.writes),
        );
        assert!(committed, "the active relation observation must commit");
    }

    fn cache_get(&self, key: CacheHashKey) -> RelationComparisonResult {
        if self.strict_function_types.is_none()
            && self.store.claimed_strict_function_types().is_some()
        {
            // A legacy session cannot prove whether a retained entry depended
            // on function variance. It may reuse only writes from this query.
            self.pending
                .latest
                .get(&key)
                .copied()
                .unwrap_or(RelationComparisonResult::NONE)
        } else {
            self.pending.get(self.store, self.relation, key)
        }
    }

    fn cache_set(&mut self, key: CacheHashKey, result: RelationComparisonResult) {
        self.pending.set(key, result);
    }

    fn observe_type_surface(&mut self, type_id: TypeId) {
        self.store.observe_relation_type_read(type_id);
    }

    fn observe_symbol(&mut self, symbol: SemanticSymbolId) {
        self.store.observe_relation_symbol_read(symbol);
    }

    fn observe_symbol_table(&mut self, table: SymbolTableId) {
        self.store.observe_relation_symbol_table_read(table);
    }

    fn observe_merged_symbol_lookup(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Option<SemanticSymbolId> {
        self.store.get_merged_symbol(symbol)
    }

    fn allows_fresh_object_target(&self) -> bool {
        // `removeSubtypes` compares fresh object-literal constituents in both
        // positions. The narrower assignable/comparable entry points retain
        // their existing fail-closed target boundary.
        matches!(
            self.relation,
            RelationKind::Subtype | RelationKind::StrictSubtype
        )
    }

    fn configured_array_reference_targets(
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Option<(TypeId, TypeId)>, RelationUnavailable> {
        configured_array_reference_targets(self.store, self.global_types, source, target)
    }

    fn configured_array_reference_target(
        &self,
        type_id: TypeId,
    ) -> Result<Option<TypeId>, RelationUnavailable> {
        let Some(global_types) = self.global_types else {
            return Ok(None);
        };
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        let TypeData::TypeReference(reference) = record.data() else {
            return Ok(None);
        };
        Ok(reference
            .object
            .target
            .filter(|target| global_types.contains_array_target(*target)))
    }

    fn canonical_array_reference_argument(
        &mut self,
        type_id: TypeId,
        target: TypeId,
    ) -> Result<TypeId, RelationUnavailable> {
        let global_types =
            self.global_types
                .ok_or(RelationUnavailable::MalformedCanonicalArrayReference(
                    type_id,
                ))?;
        let reference = self
            .store
            .canonical_array_reference_with_targets(global_types.array_targets, type_id)
            .map_err(|error| match error {
                ArrayTypeError::GlobalType(error) => {
                    RelationUnavailable::CanonicalGlobalType(error)
                }
                ArrayTypeError::InvalidReference(_)
                    if self
                        .store
                        .intrinsic_bootstrap()
                        .is_some_and(|bootstrap| target == bootstrap.empty_generic_type) =>
                {
                    RelationUnavailable::UnavailableCanonicalArrayTarget(target)
                }
                ArrayTypeError::InvalidReference(_)
                | ArrayTypeError::InvalidArrayLiteralCache { .. }
                | ArrayTypeError::UnsupportedCreationFlags(_)
                | ArrayTypeError::Capacity(_) => {
                    RelationUnavailable::MalformedCanonicalArrayReference(type_id)
                }
            })?
            .ok_or(RelationUnavailable::MalformedCanonicalArrayReference(
                type_id,
            ))?;
        let actual_target = if reference.readonly {
            global_types.array_targets.readonly_array_type()
        } else {
            global_types.array_targets.array_type()
        };
        if actual_target != target {
            return Err(RelationUnavailable::MalformedCanonicalArrayReference(
                type_id,
            ));
        }
        Ok(reference.element_type)
    }

    fn canonical_array_reference_arguments(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Option<CanonicalArrayReferenceArguments>, RelationUnavailable> {
        let Some((source_target, target_target)) =
            self.configured_array_reference_targets(source, target)?
        else {
            return Ok(None);
        };
        let same_target = source_target == target_target;
        let mutable_to_readonly = self.relation != RelationKind::Identity
            && self.global_types.is_some_and(|global_types| {
                source_target == global_types.array_targets.array_type()
                    && target_target == global_types.array_targets.readonly_array_type()
            });
        let source_argument = self.canonical_array_reference_argument(source, source_target)?;
        let target_argument = self.canonical_array_reference_argument(target, target_target)?;
        if !same_target && !mutable_to_readonly {
            return Ok(Some(CanonicalArrayReferenceArguments::Unrelated));
        }
        Ok(Some(CanonicalArrayReferenceArguments::Related {
            source: source_argument,
            target: target_argument,
        }))
    }

    /// The only mixed Array/property-object relation that is independent of
    /// instantiating generic Array members.
    ///
    /// The pinned oracle is surface-sensitive: a sole empty `Array<T>` shell
    /// makes `[[1], {}]` infer `number[][]`, while a shell with required
    /// `length` and the default library infer `{}[]`. Array -> regularized
    /// empty object is always true. The reverse direction is false only when
    /// the authoritative raw target proves a required own property; otherwise
    /// it remains unavailable rather than guessing that a cold shell is empty.
    fn canonical_array_empty_object_relation(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Option<Ternary>, RelationUnavailable> {
        if self.relation != RelationKind::StrictSubtype {
            return Ok(None);
        }
        let source_array = self.configured_array_reference_target(source)?;
        let target_array = self.configured_array_reference_target(target)?;
        let (array, object, result, reverse_requires_property) = match (source_array, target_array)
        {
            (Some(_), None) => (source, target, Ternary::True, false),
            (None, Some(_)) => (target, source, Ternary::False, true),
            _ => return Ok(None),
        };
        let array_target = source_array.or(target_array).expect("one side is an Array");
        self.canonical_array_reference_argument(array, array_target)?;
        let members = self.resolved_object_members(object, true)?;
        if object == self.bootstrap.any_function_type
            || members.exact_callable
            || members.call_signature.is_some()
        {
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }
        if !members.properties.is_empty() {
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }
        if reverse_requires_property
            && !self.canonical_array_target_has_required_own_property(array_target)?
        {
            return Err(RelationUnavailable::UnsupportedStructuredType(array_target));
        }
        Ok(Some(result))
    }

    fn canonical_array_target_has_required_own_property(
        &mut self,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let raw_target = self.store.type_payload(target).and_then(TypeRecord::symbol);
        if let Some(raw_target) = raw_target {
            self.observe_merged_symbol_lookup(raw_target);
            let members = self
                .store
                .symbol(raw_target)
                .and_then(ts_binder::semantic::Symbol::members);
            if let Some(members) = members {
                self.observe_symbol_table(members);
                let symbols = self
                    .store
                    .symbol_table(members)
                    .map(|table| table.iter().map(|(_, symbol)| symbol).collect::<Vec<_>>())
                    .unwrap_or_default();
                for symbol in symbols {
                    self.observe_merged_symbol_lookup(symbol);
                    let parent = self
                        .store
                        .symbol(symbol)
                        .and_then(ts_binder::semantic::Symbol::parent);
                    if let Some(parent) = parent {
                        self.observe_merged_symbol_lookup(parent);
                    }
                }
            }
        }
        let target_record = self
            .store
            .type_payload(target)
            .ok_or(RelationUnavailable::Type(target))?;
        if !target_record
            .object_flags()
            .contains(ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
        {
            return Ok(false);
        }
        let target_symbol = target_record
            .symbol()
            .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?;
        let symbol = self
            .store
            .symbol(target_symbol)
            .ok_or(RelationUnavailable::Symbol(target_symbol))?;
        if self.store.get_merged_symbol(target_symbol) != Some(target_symbol)
            || !symbol.flags().intersects(SymbolFlags::INTERFACE)
            || symbol.check_flags() != CheckFlags::NONE
        {
            return Err(RelationUnavailable::InvalidStructuredMembers(target));
        }
        let Some(table_id) = symbol.members() else {
            return Ok(false);
        };
        let table = self
            .store
            .symbol_table(table_id)
            .ok_or(RelationUnavailable::InvalidSymbolMembers(target_symbol))?;
        let mut seen = HashSet::with_capacity(table.len());
        let mut required = Vec::new();
        for (name, member) in table.iter() {
            if !seen.insert(member) {
                return Err(RelationUnavailable::InvalidStructuredMembers(target));
            }
            let record = self
                .store
                .symbol(member)
                .ok_or(RelationUnavailable::Symbol(member))?;
            if record.name() != name
                || record
                    .parent()
                    .and_then(|parent| self.store.get_merged_symbol(parent))
                    != Some(target_symbol)
            {
                return Err(RelationUnavailable::InvalidStructuredMembers(target));
            }
            // Optional properties and callable/member-like symbols are valid
            // raw surface entries but cannot prove this relation. In
            // particular, overload symbols may legally canonicalize through
            // a merge, so proof-only invariants belong inside this branch.
            if record.flags() == SymbolFlags::PROPERTY {
                if self.store.get_merged_symbol(member) != Some(member)
                    || record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
                    || record.members().is_some()
                    || record.exports().is_some()
                    || record.export_symbol().is_some()
                {
                    return Err(RelationUnavailable::InvalidStructuredMembers(target));
                }
                let Some(declarations) = record
                    .declarations()
                    .filter(|declarations| !declarations.is_empty())
                else {
                    return Err(RelationUnavailable::InvalidStructuredMembers(target));
                };
                let Some(value_declaration) = record.value_declaration() else {
                    return Err(RelationUnavailable::InvalidStructuredMembers(target));
                };
                let mut seen_declarations = HashSet::with_capacity(declarations.len());
                for declaration in declarations {
                    if !seen_declarations.insert(*declaration)
                        || !matches!(
                            self.store.source_node_kind(*declaration),
                            Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
                        )
                    {
                        return Err(RelationUnavailable::InvalidStructuredMembers(target));
                    }
                }
                if !seen_declarations.contains(&value_declaration) {
                    return Err(RelationUnavailable::InvalidStructuredMembers(target));
                }
                required.push(member);
            }
        }
        for property in required {
            let name = self
                .store
                .symbol(property)
                .expect("the raw target table was shallow-validated")
                .name()
                .to_owned();
            if self.global_object_property(name.as_ref())?.is_none() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn preflight_expression_union_array_object_pairs(
        &mut self,
        types: &[TypeId],
    ) -> Result<(), LiteralTypeCacheError> {
        let mut arrays = Vec::with_capacity(types.len());
        for type_id in types {
            let target = self
                .configured_array_reference_target(*type_id)
                .map_err(|_| LiteralTypeCacheError::UnsupportedUnionConstituent(*type_id))?;
            if let Some(target) = target {
                self.canonical_array_reference_argument(*type_id, target)
                    .map_err(|error| {
                        if matches!(
                            error,
                            RelationUnavailable::MalformedCanonicalArrayReference(_)
                        ) && let Err(error) =
                            super::global_types::preflight_generic_global_type_target(
                                self.store, target,
                            )
                        {
                            LiteralTypeCacheError::ArrayType {
                                type_: *type_id,
                                error: ArrayTypeError::GlobalType(error),
                            }
                        } else {
                            array_relation_preflight_error(*type_id, error)
                        }
                    })?;
            }
            arrays.push(target);
        }

        for left in 0..types.len() {
            for right in left + 1..types.len() {
                match (arrays[left], arrays[right]) {
                    (Some(left_target), Some(right_target)) => {
                        if left_target != right_target {
                            return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(
                                types[right],
                            ));
                        }
                    }
                    (Some(_), None) | (None, Some(_)) => {
                        let (array, object, array_target) = if let Some(target) = arrays[left] {
                            (types[left], types[right], target)
                        } else {
                            (
                                types[right],
                                types[left],
                                arrays[right].expect("one side is an Array"),
                            )
                        };
                        let flags = self
                            .store
                            .type_flags(object)
                            .map_err(|error| object_surface_preflight_error(object, error))?;
                        if !flags.intersects(TypeFlags::OBJECT) {
                            continue;
                        }
                        let members = self
                            .resolved_object_members(object, true)
                            .map_err(|error| object_surface_preflight_error(object, error))?;
                        if !members.properties.is_empty() {
                            return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(object));
                        }
                        let required_property = self
                            .canonical_array_target_has_required_own_property(array_target)
                            .map_err(|error| array_surface_preflight_error(array, error))?;
                        if !required_property {
                            return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(array));
                        }
                    }
                    (None, None) => {}
                }
            }
        }
        Ok(())
    }

    fn union_types(&mut self, type_id: TypeId) -> Result<Vec<TypeId>, RelationUnavailable> {
        if let Some(types) = self.validated_unions.get(&type_id) {
            return Ok(types.clone());
        }
        let enum_literal = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?
            .flags()
            .intersects(TypeFlags::ENUM_LITERAL);
        if enum_literal {
            if !enums::is_canonical_enum_union(self.store, type_id) {
                return Err(RelationUnavailable::MalformedUnion(type_id));
            }
        } else {
            let validation = match self.global_types {
                Some(global_types) => self.store.validate_union_constituent_with_array_targets(
                    global_types.array_targets,
                    type_id,
                ),
                None => self.store.validate_union_constituent(type_id),
            };
            validation.map_err(|error| union_validation_unavailable(type_id, error))?;
        }
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if !record.flags().intersects(TypeFlags::UNION) {
            return Err(RelationUnavailable::MalformedUnion(type_id));
        }
        let TypeData::Union(data) = record.data() else {
            return Err(RelationUnavailable::MalformedUnion(type_id));
        };
        let types = data.union.types.clone();
        self.validated_unions.insert(type_id, types.clone());
        Ok(types)
    }

    fn intersection_projection(
        &self,
        type_id: TypeId,
    ) -> Result<IntersectionTypeProjection, RelationUnavailable> {
        self.store
            .validate_intersection_type(type_id)
            .map_err(|_| RelationUnavailable::MalformedIntersection(type_id))
    }

    fn reduced_intersection_type(&self, type_id: TypeId) -> Result<TypeId, RelationUnavailable> {
        let flags = self.store.type_flags(type_id)?;
        if !flags.intersects(TypeFlags::INTERSECTION) {
            return Ok(type_id);
        }
        let projection = self.intersection_projection(type_id)?;
        Ok(if projection.reduced_to_never {
            self.bootstrap.never_type
        } else {
            type_id
        })
    }

    fn union_length_for_cache_choice(&self, type_id: TypeId) -> Result<usize, RelationUnavailable> {
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        Ok(match record.data() {
            TypeData::Union(data) => data.union.types.len(),
            _ => 4,
        })
    }

    #[allow(clippy::too_many_lines)] // Keep the pinned branch order visibly linear.
    fn is_related_to_ex(
        &mut self,
        original_source: TypeId,
        original_target: TypeId,
        recursion_flags: RecursionFlags,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        self.observe_type_surface(original_source);
        if original_target != original_source {
            self.observe_type_surface(original_target);
        }
        validate_direct_interface_heritage_relation_endpoint(self.store, original_source)?;
        validate_class_members_relation_endpoint(self.store, original_source)?;
        if original_target != original_source {
            validate_direct_interface_heritage_relation_endpoint(self.store, original_target)?;
            validate_class_members_relation_endpoint(self.store, original_target)?;
        }
        let original_source = self.reduced_intersection_type(original_source)?;
        let original_target = self.reduced_intersection_type(original_target)?;
        if original_source == original_target {
            return Ok(Ternary::True);
        }

        self.ensure_callable_relation_admission(original_source, true)?;
        if original_target != original_source {
            self.ensure_callable_relation_admission(
                original_target,
                self.allows_fresh_object_target(),
            )?;
        }

        let original_source_flags = self.store.type_flags(original_source)?;
        let original_target_flags = self.store.type_flags(original_target)?;
        if original_source_flags.intersects(TypeFlags::OBJECT)
            && original_target_flags.intersects(TypeFlags::PRIMITIVE)
        {
            let related = (self.relation == RelationKind::Comparable
                && !original_target_flags.intersects(TypeFlags::NEVER)
                && self.store.is_simple_type_related_to(
                    original_target,
                    original_source,
                    self.relation,
                    self.bootstrap,
                )?)
                || self.store.is_simple_type_related_to(
                    original_source,
                    original_target,
                    self.relation,
                    self.bootstrap,
                )?;
            return Ok(bool_to_ternary(related));
        }

        let source = self.store.regular_type_if_fresh(original_source)?;
        let mut target = self.store.regular_type_if_fresh(original_target)?;
        if source == target {
            return Ok(Ternary::True);
        }
        let source_flags = self.store.type_flags(source)?;
        let mut target_flags = self.store.type_flags(target)?;

        if self.relation.is_identity() {
            if source_flags != target_flags {
                return Ok(Ternary::False);
            }
            if source_flags.intersects(TypeFlags::SINGLETON) {
                return Ok(Ternary::True);
            }
            if source_flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
                return self.recursive_type_related_to(
                    source,
                    target,
                    IntersectionState::NONE,
                    recursion_flags,
                );
            }
            if let Some(arguments) = self.canonical_array_reference_arguments(source, target)? {
                return match arguments {
                    CanonicalArrayReferenceArguments::Related { source, target } => self
                        .is_related_to_ex(source, target, RecursionFlags::BOTH, intersection_state),
                    CanonicalArrayReferenceArguments::Unrelated => Ok(Ternary::False),
                };
            }
            if source_flags.intersects(TypeFlags::OBJECT)
                && target_flags.intersects(TypeFlags::OBJECT)
            {
                return self.recursive_type_related_to(
                    source,
                    target,
                    intersection_state,
                    recursion_flags,
                );
            }
            if !source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE) {
                return Ok(Ternary::False);
            }
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }

        if source_flags.intersects(TypeFlags::DEFINITELY_NON_NULLABLE)
            && target_flags.intersects(TypeFlags::UNION)
        {
            let target_types = self.union_types(target)?;
            let candidate = match target_types.as_slice() {
                [nullable, candidate]
                    if self
                        .store
                        .type_flags(*nullable)?
                        .intersects(TypeFlags::NULLABLE) =>
                {
                    Some(*candidate)
                }
                [first_nullable, second_nullable, candidate]
                    if self
                        .store
                        .type_flags(*first_nullable)?
                        .intersects(TypeFlags::NULLABLE)
                        && self
                            .store
                            .type_flags(*second_nullable)?
                            .intersects(TypeFlags::NULLABLE) =>
                {
                    Some(*candidate)
                }
                _ => None,
            };
            if let Some(candidate) = candidate
                && !self
                    .store
                    .type_flags(candidate)?
                    .intersects(TypeFlags::NULLABLE)
            {
                target = self.store.regular_type_if_fresh(candidate)?;
                if source == target {
                    return Ok(Ternary::True);
                }
                target_flags = self.store.type_flags(target)?;
            }
        }

        if let Some(related) =
            self.store
                .authenticated_template_literal_relation(source, target, self.relation)?
        {
            return Ok(bool_to_ternary(related));
        }

        if (self.relation == RelationKind::Comparable
            && !target_flags.intersects(TypeFlags::NEVER)
            && self.store.is_simple_type_related_to(
                target,
                source,
                self.relation,
                self.bootstrap,
            )?)
            || self.store.is_simple_type_related_to(
                source,
                target,
                self.relation,
                self.bootstrap,
            )?
        {
            return Ok(Ternary::True);
        }

        if source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::OBJECT)
            && self
                .store
                .authenticated_declared_construct_pair(
                    source,
                    target,
                    self.relation,
                    self.strict_function_types,
                )?
                .is_some()
        {
            return self.recursive_type_related_to(
                source,
                target,
                intersection_state,
                recursion_flags,
            );
        }

        if source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
            || target_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
        {
            if supports_structured_object_relation(self.relation, self.strict_function_types) {
                if target_flags.intersects(TypeFlags::UNION)
                    && !intersection_state.intersects(IntersectionState::TARGET)
                    && source_flags.intersects(TypeFlags::OBJECT)
                    && self.is_fresh_object_literal(source)?
                    && self.has_excess_union_properties(source, target)?
                {
                    return Ok(Ternary::False);
                }
                if target_flags.intersects(TypeFlags::INTERSECTION)
                    && !intersection_state.intersects(IntersectionState::TARGET)
                    && source_flags.intersects(TypeFlags::OBJECT)
                    && self.is_fresh_object_literal(source)?
                    && self.has_excess_properties(source, target)?
                {
                    return Ok(Ternary::False);
                }
                if source_flags.intersects(TypeFlags::INTERSECTION)
                    && !intersection_state.intersects(IntersectionState::SOURCE)
                    && target_flags.intersects(TypeFlags::OBJECT)
                    && self.relation != RelationKind::Comparable
                    && self.weak_target_lacks_common_properties(source, target)?
                {
                    return Ok(Ternary::False);
                }
            }
            if source_flags.intersects(TypeFlags::INTERSECTION)
                || target_flags.intersects(TypeFlags::INTERSECTION)
            {
                return self.union_or_intersection_related_to(source, target, intersection_state);
            }
            if source_flags.intersects(TypeFlags::PRIMITIVE)
                && target_flags.intersects(TypeFlags::OBJECT)
                && let Some(array_target) = self.configured_array_reference_target(target)?
            {
                self.canonical_array_reference_argument(target, array_target)?;
                return Ok(Ternary::False);
            }
            if self.relation != RelationKind::Identity
                && target_flags.intersects(TypeFlags::OBJECT)
                && let Some(apparent_source) = self
                    .global_types
                    .and_then(|global_types| global_types.apparent_primitive_type(source_flags))
            {
                if self
                    .unresolved_primitive_wrapper_lacks_required_property(apparent_source, target)?
                {
                    return Ok(Ternary::False);
                }
                return self.is_related_to_ex(
                    apparent_source,
                    target,
                    recursion_flags,
                    intersection_state,
                );
            }
            if self.callable_tuple_relation(source, target)? {
                return Ok(Ternary::False);
            }
            if let Some(arguments) = self.canonical_array_reference_arguments(source, target)? {
                return match arguments {
                    CanonicalArrayReferenceArguments::Related { source, target } => self
                        .is_related_to_ex(source, target, RecursionFlags::BOTH, intersection_state),
                    CanonicalArrayReferenceArguments::Unrelated => Ok(Ternary::False),
                };
            }
            if source_flags.intersects(TypeFlags::OBJECT)
                && target_flags.intersects(TypeFlags::OBJECT)
                && let Some(related) = self.canonical_array_empty_object_relation(source, target)?
            {
                return Ok(related);
            }
            if supports_structured_object_relation(self.relation, self.strict_function_types)
                && source_flags.intersects(TypeFlags::OBJECT)
                && target_flags.intersects(TypeFlags::OBJECT)
            {
                if !intersection_state.intersects(IntersectionState::TARGET)
                    && self.is_fresh_object_literal(source)?
                    && self.has_excess_properties(source, target)?
                {
                    return Ok(Ternary::False);
                }
                if self.relation != RelationKind::Comparable
                    && self.weak_target_lacks_common_properties(source, target)?
                {
                    return Ok(Ternary::False);
                }
                return self.recursive_type_related_to(
                    source,
                    target,
                    intersection_state,
                    recursion_flags,
                );
            }

            let source_is_union = source_flags.intersects(TypeFlags::UNION);
            let target_is_union = target_flags.intersects(TypeFlags::UNION);
            if source_is_union || target_is_union {
                let source_union_len = if source_is_union {
                    Some(self.union_length_for_cache_choice(source)?)
                } else {
                    None
                };
                let target_union_len = if target_is_union {
                    Some(self.union_length_for_cache_choice(target)?)
                } else {
                    None
                };
                let skip_caching = source_union_len.is_some_and(|length| length < 4)
                    && !target_is_union
                    || target_union_len.is_some_and(|length| length < 4)
                        && !source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE);
                if skip_caching {
                    return self.union_or_intersection_related_to(
                        source,
                        target,
                        intersection_state,
                    );
                }
                return self.recursive_type_related_to(
                    source,
                    target,
                    intersection_state,
                    recursion_flags,
                );
            }

            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }
        Ok(Ternary::False)
    }

    /// A property-free function cannot satisfy a canonical tuple, and a tuple
    /// cannot satisfy a required call signature.
    fn callable_tuple_relation(
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let source_callable = matches!(
            validate_stored_single_callable(self.store, source),
            StoredSingleCallableValidation::Valid { .. }
        );
        let target_callable = matches!(
            validate_stored_single_callable(self.store, target),
            StoredSingleCallableValidation::Valid { .. }
        );
        if !source_callable && !target_callable {
            return Ok(false);
        }
        let tuple = if source_callable { target } else { source };
        self.store
            .canonical_tuple_shape(tuple)
            .map(|shape| shape.is_some())
            .map_err(|_| RelationUnavailable::InvalidStructuredMembers(tuple))
    }

    fn recursive_type_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        intersection_state: IntersectionState,
        recursion_flags: RecursionFlags,
    ) -> Result<Ternary, RelationUnavailable> {
        if self.overflow {
            return Ok(Ternary::False);
        }
        let built_key = self
            .store
            .relation_key_if_available(
                source,
                target,
                intersection_state,
                self.relation.is_identity(),
                false,
            )
            .map_err(relation_key_unavailable)?;
        let key = built_key.key();
        let entry = self.cache_get(key);
        if !entry.is_empty() {
            return Ok(if entry.intersects(RelationComparisonResult::SUCCEEDED) {
                Ternary::True
            } else {
                Ternary::False
            });
        }
        if self.relation_count <= 0 {
            self.overflow = true;
            return Ok(Ternary::False);
        }
        if self.maybe_keys_set.contains(&key) {
            return Ok(Ternary::Maybe);
        }
        if built_key.constrained() {
            let broadest = self
                .store
                .relation_key_if_available(
                    source,
                    target,
                    intersection_state,
                    self.relation.is_identity(),
                    true,
                )
                .map_err(relation_key_unavailable)?;
            if self.maybe_keys_set.contains(&broadest.key()) {
                return Ok(Ternary::Maybe);
            }
        }
        if self.source_stack.len() == self.stack_depth_limit
            || self.target_stack.len() == self.stack_depth_limit
        {
            self.overflow = true;
            return Ok(Ternary::False);
        }

        // Capability validation is side-effect free. It is intentionally after
        // the pinned cache/active/depth checks, so cached answers remain usable
        // even for structural families outside this slice.
        self.ensure_supported_recursive_pair(source, target)?;

        let maybe_start = self.maybe_keys.len();
        self.maybe_keys.push(key);
        self.maybe_keys_set.insert(key);
        let saved_expanding_flags = self.expanding_flags;
        if recursion_flags.intersects(RecursionFlags::SOURCE) {
            self.source_stack.push(source);
            if !self.expanding_flags.intersects(ExpandingFlags::SOURCE)
                && self.is_deeply_nested_type(source, true, PINNED_EXPANDING_DEPTH)?
            {
                self.expanding_flags |= ExpandingFlags::SOURCE;
            }
        }
        if recursion_flags.intersects(RecursionFlags::TARGET) {
            self.target_stack.push(target);
            if !self.expanding_flags.intersects(ExpandingFlags::TARGET)
                && self.is_deeply_nested_type(target, false, PINNED_EXPANDING_DEPTH)?
            {
                self.expanding_flags |= ExpandingFlags::TARGET;
            }
        }

        let result = if self.expanding_flags == ExpandingFlags::BOTH {
            Ok(Ternary::Maybe)
        } else {
            self.structured_type_related_to(source, target, intersection_state)
        };

        self.unwind_recursion(recursion_flags, saved_expanding_flags);

        let result = match result {
            Ok(result) => result,
            Err(error) => {
                self.reset_maybe_stack(maybe_start, false);
                return Err(error);
            }
        };
        if result == Ternary::False {
            self.cache_set(key, RelationComparisonResult::FAILED);
            self.relation_count -= 1;
            self.reset_maybe_stack(maybe_start, false);
        } else if result == Ternary::True
            || (self.source_stack.is_empty() && self.target_stack.is_empty())
        {
            self.reset_maybe_stack(
                maybe_start,
                result == Ternary::True || result == Ternary::Maybe,
            );
        }
        Ok(result)
    }

    fn unwind_recursion(
        &mut self,
        recursion_flags: RecursionFlags,
        saved_expanding_flags: ExpandingFlags,
    ) {
        if recursion_flags.intersects(RecursionFlags::SOURCE) {
            self.source_stack.pop();
        }
        if recursion_flags.intersects(RecursionFlags::TARGET) {
            self.target_stack.pop();
        }
        self.expanding_flags = saved_expanding_flags;
    }

    fn reset_maybe_stack(&mut self, maybe_start: usize, mark_all_as_succeeded: bool) {
        for index in maybe_start..self.maybe_keys.len() {
            let key = self.maybe_keys[index];
            self.maybe_keys_set.remove(&key);
            if mark_all_as_succeeded {
                self.cache_set(key, RelationComparisonResult::SUCCEEDED);
                self.relation_count -= 1;
            }
        }
        self.maybe_keys.truncate(maybe_start);
    }

    fn is_deeply_nested_type(
        &self,
        type_id: TypeId,
        source: bool,
        max_depth: usize,
    ) -> Result<bool, RelationUnavailable> {
        let stack = if source {
            &self.source_stack
        } else {
            &self.target_stack
        };
        if stack.len() < max_depth {
            return Ok(false);
        }
        let identity = self
            .store
            .recursion_identity_if_available(type_id)
            .map_err(recursion_identity_unavailable)?;
        let mut count = 0;
        let mut last_type_id = 0;
        for candidate in stack {
            let candidate_identity = self
                .store
                .recursion_identity_if_available(*candidate)
                .map_err(recursion_identity_unavailable)?;
            if candidate_identity == identity {
                if candidate.get() >= last_type_id {
                    count += 1;
                    if count >= max_depth {
                        return Ok(true);
                    }
                }
                last_type_id = candidate.get();
            }
        }
        Ok(false)
    }

    fn structured_type_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        let source_flags = self.store.type_flags(source)?;
        let target_flags = self.store.type_flags(target)?;
        if self.relation.is_identity() && source_flags.intersects(TypeFlags::UNION_OR_INTERSECTION)
        {
            let mut result =
                self.each_union_or_intersection_type_related_to_some_type(source, target)?;
            if result != Ternary::False {
                result &=
                    self.each_union_or_intersection_type_related_to_some_type(target, source)?;
            }
            return Ok(result);
        }
        if source_flags.intersects(TypeFlags::UNION)
            || target_flags.intersects(TypeFlags::UNION)
            || source_flags.intersects(TypeFlags::INTERSECTION)
                && !intersection_state.intersects(IntersectionState::SOURCE)
            || target_flags.intersects(TypeFlags::INTERSECTION)
                && !intersection_state.intersects(IntersectionState::TARGET)
        {
            return self.union_or_intersection_related_to(source, target, intersection_state);
        }
        let source_is_object = source_flags.intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION);
        let target_is_object = target_flags.intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION);
        if !supports_structured_object_relation(self.relation, self.strict_function_types)
            || !source_is_object
            || !target_is_object
        {
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }
        if let Some((source_signature, target_signature)) =
            self.store.authenticated_declared_construct_pair(
                source,
                target,
                self.relation,
                self.strict_function_types,
            )?
        {
            return self.compare_signatures_related(
                &source_signature,
                &target_signature,
                SignatureCheckMode::NONE,
                intersection_state,
            );
        }
        let source_members = self.resolved_object_members(source, true)?;
        let allow_fresh_target = self.allows_fresh_object_target();
        let target_members = self.resolved_object_members(target, allow_fresh_target)?;
        if matches!(
            self.relation,
            RelationKind::Subtype | RelationKind::StrictSubtype
        ) && self.is_fresh_object_literal(target)?
            && target_members.properties.is_empty()
            && (!source_members.properties.is_empty()
                || source_members.exact_callable
                || source_members.call_signature.is_some()
                || source == self.bootstrap.any_function_type)
        {
            return Ok(Ternary::False);
        }
        let mut result = if self.relation.is_identity() {
            self.properties_identical_to(target, &source_members, &target_members)?
        } else {
            self.properties_related_to(source, &source_members, &target_members)?
        };
        if result != Ternary::False {
            result &= self.call_signatures_related_to(
                source,
                target,
                source_members.call_signature.as_ref(),
                target_members.call_signature.as_ref(),
                intersection_state,
            )?;
        }
        if result != Ternary::False {
            result &= self.index_signatures_related_to(
                source,
                target,
                &source_members,
                &target_members,
                intersection_state,
            )?;
        }
        Ok(result)
    }

    fn union_or_intersection_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        let source_flags = self.store.type_flags(source)?;
        let target_flags = self.store.type_flags(target)?;
        if source_flags.intersects(TypeFlags::UNION) {
            self.union_types(source)?;
            if target_flags.intersects(TypeFlags::UNION) {
                self.union_types(target)?;
                if self.union_origin_contains_aliased_source(target, source)? {
                    return Ok(Ternary::True);
                }
            }
            if self.relation == RelationKind::Comparable {
                return self.some_type_related_to_type(source, target, intersection_state);
            }
            return self.each_type_related_to_type(source, target, intersection_state);
        }
        if target_flags.intersects(TypeFlags::UNION) {
            let source = self
                .store
                .get_regular_type_of_object_literal(source)
                .map_err(|_| RelationUnavailable::InvalidStructuredMembers(source))?;
            return self.type_related_to_some_type(source, target, intersection_state);
        }
        if target_flags.intersects(TypeFlags::INTERSECTION)
            && !intersection_state.intersects(IntersectionState::TARGET)
        {
            let target_types = self.intersection_projection(target)?.types;
            let mut result = Ternary::True;
            for target_type in target_types {
                let related = self.is_related_to_ex(
                    source,
                    target_type,
                    RecursionFlags::TARGET,
                    intersection_state | IntersectionState::TARGET,
                )?;
                if related == Ternary::False {
                    return Ok(Ternary::False);
                }
                result &= related;
            }
            return Ok(result);
        }
        if source_flags.intersects(TypeFlags::INTERSECTION)
            && !intersection_state.intersects(IntersectionState::SOURCE)
        {
            let source_types = self.intersection_projection(source)?.types;
            for source_type in source_types {
                let related = self.is_related_to_ex(
                    source_type,
                    target,
                    RecursionFlags::SOURCE,
                    intersection_state | IntersectionState::SOURCE,
                )?;
                if related != Ternary::False {
                    return Ok(related);
                }
            }
            if target_flags.intersects(TypeFlags::OBJECT) {
                return self.structured_type_related_to(
                    source,
                    target,
                    intersection_state | IntersectionState::SOURCE,
                );
            }
            return Ok(Ternary::False);
        }
        Err(RelationUnavailable::StructuralRelation {
            source,
            target,
            relation: self.relation,
        })
    }

    fn union_origin_contains_aliased_source(
        &mut self,
        target: TypeId,
        source: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        if self
            .store
            .type_payload(source)
            .ok_or(RelationUnavailable::Type(source))?
            .alias()
            .is_none()
        {
            return Ok(false);
        }
        let target_record = self
            .store
            .type_payload(target)
            .ok_or(RelationUnavailable::Type(target))?;
        let TypeData::Union(target_data) = target_record.data() else {
            return Err(RelationUnavailable::MalformedUnion(target));
        };
        let Some(origin) = target_data.origin else {
            return Ok(false);
        };
        let origin_record = self
            .store
            .type_payload(origin)
            .ok_or(RelationUnavailable::Type(origin))?;
        let TypeData::Union(origin_data) = origin_record.data() else {
            return Err(RelationUnavailable::MalformedUnion(target));
        };
        Ok(origin_data.union.types.contains(&source))
    }

    fn some_type_related_to_type(
        &mut self,
        source: TypeId,
        target: TypeId,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        let source_types = self.union_types(source)?;
        if source_types.contains(&target) {
            return Ok(Ternary::True);
        }
        for source_type in source_types {
            let related = self.is_related_to_ex(
                source_type,
                target,
                RecursionFlags::SOURCE,
                intersection_state,
            )?;
            if related != Ternary::False {
                return Ok(related);
            }
        }
        Ok(Ternary::False)
    }

    fn each_type_related_to_type(
        &mut self,
        source: TypeId,
        target: TypeId,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        let source_types = self.union_types(source)?;
        let target_types = if self.store.type_flags(target)?.intersects(TypeFlags::UNION) {
            Some(self.union_types(target)?)
        } else {
            None
        };
        let stripped_target_types = if let Some(target_types) = target_types.as_ref()
            && !self
                .store
                .type_flags(source_types[0])?
                .intersects(TypeFlags::UNDEFINED)
            && self
                .store
                .type_flags(target_types[0])?
                .intersects(TypeFlags::UNDEFINED)
        {
            let stripped = target_types
                .iter()
                .copied()
                .filter(|candidate| {
                    self.store
                        .type_payload(*candidate)
                        .is_some_and(|record| !record.flags().intersects(TypeFlags::UNDEFINED))
                })
                .collect::<Vec<_>>();
            (stripped.len() >= 2).then_some(stripped)
        } else {
            target_types
        };

        let mut result = Ternary::True;
        for (index, source_type) in source_types.iter().copied().enumerate() {
            if let Some(stripped_types) = stripped_target_types.as_ref()
                && source_types.len() >= stripped_types.len()
                && source_types.len() % stripped_types.len() == 0
            {
                let related = self.is_related_to_ex(
                    source_type,
                    stripped_types[index % stripped_types.len()],
                    RecursionFlags::BOTH,
                    intersection_state,
                )?;
                if related != Ternary::False {
                    result &= related;
                    continue;
                }
            }
            let related = self.is_related_to_ex(
                source_type,
                target,
                RecursionFlags::SOURCE,
                intersection_state,
            )?;
            if related == Ternary::False {
                return Ok(Ternary::False);
            }
            result &= related;
        }
        Ok(result)
    }

    fn type_related_to_some_type(
        &mut self,
        source: TypeId,
        target: TypeId,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        let target_types = self.union_types(target)?;
        if target_types.contains(&source) {
            return Ok(Ternary::True);
        }

        let source_flags = self.store.type_flags(source)?;
        let target_record = self
            .store
            .type_payload(target)
            .ok_or(RelationUnavailable::Type(target))?;
        let primitive_union = target_record
            .object_flags()
            .intersects(ObjectFlags::PRIMITIVE_UNION);
        let literal_fast_path = self.relation != RelationKind::Comparable
            && primitive_union
            && !source_flags.intersects(TypeFlags::ENUM_LITERAL)
            && (source_flags.intersects(
                TypeFlags::STRING_LITERAL | TypeFlags::BOOLEAN_LITERAL | TypeFlags::BIG_INT_LITERAL,
            ) || matches!(
                self.relation,
                RelationKind::Subtype | RelationKind::StrictSubtype
            ) && source_flags.intersects(TypeFlags::NUMBER_LITERAL));
        if literal_fast_path {
            let source_record = self
                .store
                .type_payload(source)
                .ok_or(RelationUnavailable::Type(source))?;
            let TypeData::Literal(literal) = source_record.data() else {
                return Err(RelationUnavailable::MalformedLiteral(source));
            };
            let alternate = if source == literal.regular_type {
                literal.fresh_type
            } else {
                Some(literal.regular_type)
            };
            let primitive = if source_flags.intersects(TypeFlags::STRING_LITERAL) {
                Some(self.bootstrap.string_type)
            } else if source_flags.intersects(TypeFlags::NUMBER_LITERAL) {
                Some(self.bootstrap.number_type)
            } else if source_flags.intersects(TypeFlags::BIG_INT_LITERAL) {
                Some(self.bootstrap.bigint_type)
            } else {
                None
            };
            if primitive.is_some_and(|primitive| target_types.contains(&primitive))
                || alternate.is_some_and(|alternate| target_types.contains(&alternate))
            {
                return Ok(Ternary::True);
            }
            return Ok(Ternary::False);
        }

        for target_type in target_types {
            let related = self.is_related_to_ex(
                source,
                target_type,
                RecursionFlags::TARGET,
                intersection_state,
            )?;
            if related != Ternary::False {
                return Ok(related);
            }
        }
        Ok(Ternary::False)
    }

    fn each_union_or_intersection_type_related_to_some_type(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Ternary, RelationUnavailable> {
        let source_types = self.union_or_intersection_types(source)?;
        let target_types = self.union_or_intersection_types(target)?;
        let mut result = Ternary::True;
        for source_type in source_types {
            if target_types.contains(&source_type) {
                continue;
            }
            let mut related = Ternary::False;
            for target_type in &target_types {
                let candidate = self.is_related_to_ex(
                    source_type,
                    *target_type,
                    RecursionFlags::TARGET,
                    IntersectionState::NONE,
                )?;
                if candidate != Ternary::False {
                    related = candidate;
                    break;
                }
            }
            if related == Ternary::False {
                return Ok(Ternary::False);
            }
            result &= related;
        }
        Ok(result)
    }

    fn union_or_intersection_types(
        &mut self,
        type_: TypeId,
    ) -> Result<Vec<TypeId>, RelationUnavailable> {
        let flags = self.store.type_flags(type_)?;
        if flags.intersects(TypeFlags::UNION) {
            return self.union_types(type_);
        }
        if flags.intersects(TypeFlags::INTERSECTION) {
            return Ok(self.intersection_projection(type_)?.types);
        }
        Err(RelationUnavailable::StructuralRelation {
            source: type_,
            target: type_,
            relation: self.relation,
        })
    }

    fn weak_target_lacks_common_properties(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let allow_fresh_target = self.allows_fresh_object_target();
        let target_members = self.resolved_object_property_surface(target, allow_fresh_target)?;
        if target_members.properties.is_empty() {
            return Ok(false);
        }
        for property in &target_members.properties {
            if !self
                .property_symbol(*property, target_members.property_origin)?
                .flags()
                .intersects(SymbolFlags::OPTIONAL)
            {
                return Ok(false);
            }
        }
        let source_members = self.resolved_object_property_surface(source, true)?;
        let source_is_empty = source_members.properties.is_empty()
            && !source_members.exact_callable
            && source_members.call_signature.is_none();
        if source_is_empty || self.is_direct_global_object_type(source)? {
            return Ok(false);
        }
        let target_members_id = target_members.members;
        let source_names = source_members
            .properties
            .into_iter()
            .map(|property| {
                self.property_symbol(property, source_members.property_origin)
                    .map(|symbol| symbol.name().to_owned())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let target_table = target_members_id
            .and_then(|members| self.store.symbol_table(members))
            .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?;
        for name in source_names {
            if target_table.get(name.as_ref()).is_some() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn is_fresh_object_literal(&self, type_id: TypeId) -> Result<bool, RelationUnavailable> {
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        Ok(record
            .object_flags()
            .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL))
    }

    fn has_excess_properties(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let allow_fresh_target = self.allows_fresh_object_target();
        let target_members = self.resolved_object_property_surface(target, allow_fresh_target)?;

        // Pinned `hasExcessProperties` treats the empty object as an open
        // target and exempts the global Object target only for assignable and
        // comparable relations. Subtype relations retain fresh-literal excess
        // checking against those targets. A validated index signature accepts
        // every property name in its key domain.
        if matches!(
            self.relation,
            RelationKind::Assignable | RelationKind::Comparable
        ) && (target_members.properties.is_empty() && target_members.index_infos.is_empty()
            || self.is_direct_global_object_type(target)?)
        {
            return Ok(false);
        }
        let source_members = self.resolved_object_property_surface(source, true)?;
        if target_members.properties.is_empty() && target_members.index_infos.is_empty() {
            return Ok(!source_members.properties.is_empty());
        }
        let target_members_id = target_members.members;
        let source_names = source_members
            .properties
            .into_iter()
            .map(|property| {
                self.property_symbol(property, source_members.property_origin)
                    .map(|symbol| symbol.name().to_owned())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let target_table = match target_members_id {
            Some(members) => Some(
                self.store
                    .symbol_table(members)
                    .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?,
            ),
            None if target_members.properties.is_empty()
                && !target_members.index_infos.is_empty() =>
            {
                None
            }
            None => return Err(RelationUnavailable::InvalidStructuredMembers(target)),
        };
        for name in source_names {
            if target_table.is_none_or(|table| table.get(name.as_ref()).is_none())
                && !self.index_signature_accepts_name(
                    target,
                    &target_members.index_infos,
                    name.as_ref(),
                )?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Applies union-wide excess checks before regularizing a fresh source.
    ///
    /// A property missing from one constituent stays eligible while another
    /// constituent matches. Discriminant mismatches remove a constituent only
    /// when at least one remaining constituent matches that discriminant.
    fn has_excess_union_properties(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let source_members = self.resolved_object_property_surface(source, true)?;
        let mut targets = Vec::new();
        for constituent in self.union_types(target)? {
            if self
                .store
                .type_flags(constituent)?
                .intersects(TypeFlags::OBJECT)
            {
                targets.push((
                    constituent,
                    self.resolved_object_property_surface(constituent, false)?,
                    true,
                ));
            }
        }
        if targets.is_empty() {
            return Ok(false);
        }

        for source_property in &source_members.properties {
            let (name, source_type) = {
                let record =
                    self.property_symbol(*source_property, source_members.property_origin)?;
                (
                    record.name().to_owned(),
                    self.property_type(*source_property)?,
                )
            };
            let mut property_types = Vec::new();
            let mut property_symbols = Vec::new();
            for (_, members, _) in &targets {
                let Some(members) = members.members else {
                    continue;
                };
                let Some(property) = self
                    .store
                    .symbol_table(members)
                    .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?
                    .get(name.as_ref())
                else {
                    continue;
                };
                property_types.push(self.property_type(property)?);
                property_symbols.push(property);
            }
            let non_uniform = property_types
                .first()
                .is_some_and(|first| property_types.iter().any(|type_| type_ != first));
            let distinct_symbols = property_symbols
                .first()
                .is_some_and(|first| property_symbols.iter().any(|symbol| symbol != first));
            let has_literal = property_types.iter().any(|type_| {
                self.store.type_payload(*type_).is_some_and(|record| {
                    record
                        .flags()
                        .intersects(TypeFlags::UNIT | TypeFlags::BOOLEAN)
                })
            });
            if !non_uniform || !distinct_symbols || !has_literal {
                continue;
            }

            let mut matched = false;
            let mut mismatched = Vec::new();
            for (index, (_, members, included)) in targets.iter().enumerate() {
                if !*included {
                    continue;
                }
                let Some(members) = members.members else {
                    continue;
                };
                let Some(property) = self
                    .store
                    .symbol_table(members)
                    .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?
                    .get(name.as_ref())
                else {
                    continue;
                };
                let target_type = self.property_type(property)?;
                if self.property_types_related(&[source_type], &[target_type])? == Ternary::False {
                    mismatched.push(index);
                } else {
                    matched = true;
                }
            }
            if matched {
                for index in mismatched {
                    targets[index].2 = false;
                }
            }
        }

        for source_property in &source_members.properties {
            let (name, source_type) = {
                let record =
                    self.property_symbol(*source_property, source_members.property_origin)?;
                (
                    record.name().to_owned(),
                    self.property_type(*source_property)?,
                )
            };
            let mut target_types = Vec::new();
            let mut known = false;
            for (_, members, included) in &targets {
                if !*included {
                    continue;
                }
                let property = members
                    .members
                    .and_then(|members| self.store.symbol_table(members))
                    .and_then(|members| members.get(name.as_ref()));
                if let Some(property) = property {
                    known = true;
                    let optional = self
                        .property_symbol(property, members.property_origin)?
                        .flags()
                        .contains(SymbolFlags::OPTIONAL);
                    target_types.extend(
                        self.effective_property_types(self.property_type(property)?, optional)?,
                    );
                } else {
                    target_types.push(self.bootstrap.undefined_type);
                }
            }
            if !known
                || self.property_types_related(&[source_type], &target_types)? == Ternary::False
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn is_direct_global_object_type(
        &mut self,
        type_id: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let Some(global_object) = self.global_object_symbol()? else {
            return Ok(false);
        };
        if self
            .store
            .declared_type_links(global_object)
            .and_then(|links| links.declared_type)
            == Some(type_id)
        {
            return Ok(true);
        }
        let Some(type_symbol) = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?
            .symbol()
        else {
            return Ok(false);
        };
        Ok(self.observe_merged_symbol_lookup(type_symbol) == Some(global_object))
    }

    fn properties_identical_to(
        &mut self,
        target: TypeId,
        source_members: &ResolvedObjectMembers,
        target_members: &ResolvedObjectMembers,
    ) -> Result<Ternary, RelationUnavailable> {
        if source_members.properties.len() != target_members.properties.len() {
            return Ok(Ternary::False);
        }
        if target_members.properties.is_empty() {
            return Ok(Ternary::True);
        }
        let target_table = target_members
            .members
            .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?;
        self.observe_symbol_table(target_table);

        let mut result = Ternary::True;
        for source_property in &source_members.properties {
            let (name, source_optional, source_readonly) = {
                let source =
                    self.property_symbol(*source_property, source_members.property_origin)?;
                (
                    source.name().to_owned(),
                    source.flags().intersects(SymbolFlags::OPTIONAL),
                    source.check_flags().contains(CheckFlags::READONLY),
                )
            };
            let target_property = self
                .store
                .symbol_table(target_table)
                .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?
                .get(name.as_ref());
            let Some(target_property) = target_property else {
                return Ok(Ternary::False);
            };
            let (target_optional, target_readonly) = {
                let target =
                    self.property_symbol(target_property, target_members.property_origin)?;
                (
                    target.flags().intersects(SymbolFlags::OPTIONAL),
                    target.check_flags().contains(CheckFlags::READONLY),
                )
            };
            if source_optional != target_optional || source_readonly != target_readonly {
                return Ok(Ternary::False);
            }
            if *source_property == target_property {
                continue;
            }
            let related = self.is_related_to_ex(
                self.property_type(*source_property)?,
                self.property_type(target_property)?,
                RecursionFlags::BOTH,
                IntersectionState::NONE,
            )?;
            if related == Ternary::False {
                return Ok(Ternary::False);
            }
            result &= related;
        }
        Ok(result)
    }

    fn properties_related_to(
        &mut self,
        source: TypeId,
        source_members: &ResolvedObjectMembers,
        target_members: &ResolvedObjectMembers,
    ) -> Result<Ternary, RelationUnavailable> {
        // Preserve upstream's unmatched-property pass before comparing any
        // property types. This ordering is observable through relation caches.
        for target_property in &target_members.properties {
            let target_symbol =
                self.property_symbol(*target_property, target_members.property_origin)?;
            if !target_symbol.flags().intersects(SymbolFlags::OPTIONAL)
                && self
                    .lookup_source_property(
                        source,
                        source_members,
                        *target_property,
                        target_members.property_origin,
                    )?
                    .is_none()
            {
                return Ok(Ternary::False);
            }
        }

        let mut result = Ternary::True;
        for target_property in &target_members.properties {
            let Some(source_property) = self.lookup_source_property(
                source,
                source_members,
                *target_property,
                target_members.property_origin,
            )?
            else {
                continue;
            };
            if source_property == *target_property {
                continue;
            }
            let related = self.property_related_to(
                source_property,
                source_members.property_origin,
                *target_property,
                target_members.property_origin,
            )?;
            if related == Ternary::False {
                return Ok(Ternary::False);
            }
            result &= related;
        }
        Ok(result)
    }

    fn index_signature_accepts_name(
        &self,
        owner: TypeId,
        indexes: &[IndexInfoId],
        name: ts_binder::EscapedNameRef<'_>,
    ) -> Result<bool, RelationUnavailable> {
        let Some(name) = name.as_utf8() else {
            return Ok(false);
        };
        for index in indexes {
            let info = self
                .store
                .index_info(*index)
                .ok_or(RelationUnavailable::InvalidStructuredMembers(owner))?;
            if info.key_type() == self.bootstrap.string_type
                || info.key_type() == self.bootstrap.number_type
                    && ts_jsnum::from_string(name).to_string() == name
                || template_pattern_index_matches_name(self.store, info.key_type(), name)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn index_signatures_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        source_members: &ResolvedObjectMembers,
        target_members: &ResolvedObjectMembers,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        if self.relation.is_identity()
            && source_members.index_infos.len() != target_members.index_infos.len()
        {
            return Ok(Ternary::False);
        }

        let mut result = Ternary::True;
        for target_index in &target_members.index_infos {
            let target_info = self
                .store
                .index_info(*target_index)
                .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?;
            let target_key = target_info.key_type();
            let target_value = target_info.value_type();
            let target_readonly = target_info.is_readonly();
            if !self.relation.is_identity()
                && self.relation != RelationKind::StrictSubtype
                && target_key == self.bootstrap.string_type
                && self
                    .store
                    .type_flags(target_value)?
                    .intersects(TypeFlags::ANY)
            {
                continue;
            }

            let source_index = source_members.index_infos.iter().find_map(|index| {
                let info = self.store.index_info(*index)?;
                (info.key_type() == target_key
                    || !self.relation.is_identity()
                        && info.key_type() == self.bootstrap.string_type
                        && (target_key == self.bootstrap.number_type
                            || is_template_pattern_index_key(self.store, target_key)))
                .then_some((info.value_type(), info.is_readonly()))
            });
            if let Some((source_value, source_readonly)) = source_index {
                if self.relation.is_identity() && source_readonly != target_readonly {
                    return Ok(Ternary::False);
                }
                let related = self.is_related_to_ex(
                    source_value,
                    target_value,
                    RecursionFlags::BOTH,
                    intersection_state,
                )?;
                if related == Ternary::False {
                    return Ok(Ternary::False);
                }
                result &= related;
                continue;
            }
            if self.relation.is_identity()
                || !source_members.index_infos.is_empty()
                || intersection_state.intersects(IntersectionState::SOURCE)
                || self.relation == RelationKind::StrictSubtype
                    && !self.is_fresh_object_literal(source)?
                || !self
                    .store
                    .type_payload(source)
                    .and_then(TypeRecord::symbol)
                    .and_then(|owner| self.store.symbol(owner))
                    .is_some_and(|owner| {
                        owner
                            .flags()
                            .intersects(SymbolFlags::OBJECT_LITERAL | SymbolFlags::TYPE_LITERAL)
                    })
            {
                return Ok(Ternary::False);
            }

            for property in &source_members.properties {
                let name = self
                    .property_symbol(*property, source_members.property_origin)?
                    .name()
                    .to_owned();
                if !self.index_signature_accepts_name(target, &[*target_index], name.as_ref())? {
                    continue;
                }
                let related = self.is_related_to_ex(
                    self.property_type(*property)?,
                    target_value,
                    RecursionFlags::BOTH,
                    intersection_state,
                )?;
                if related == Ternary::False {
                    return Ok(Ternary::False);
                }
                result &= related;
            }
        }
        Ok(result)
    }

    fn call_signatures_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        source_signature: Option<&ValidatedSingleCallable>,
        target_signature: Option<&ValidatedSingleCallable>,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        if self.relation.is_identity() {
            return match (source_signature, target_signature) {
                (None, None) => Ok(Ternary::True),
                (Some(source), Some(target)) => {
                    self.compare_signatures_identical(source, target, intersection_state)
                }
                _ => Ok(Ternary::False),
            };
        }

        // Pinned `signaturesRelatedTo` treats this intrinsic as a directional
        // wildcard before reading either signature list.
        if source == self.bootstrap.any_function_type {
            return Ok(Ternary::True);
        }
        if target == self.bootstrap.any_function_type {
            return Ok(Ternary::False);
        }
        match (source_signature, target_signature) {
            (_, None) => Ok(Ternary::True),
            (None, Some(_)) => Ok(Ternary::False),
            (Some(source), Some(target)) => {
                let mode = match self.relation {
                    RelationKind::Subtype => SignatureCheckMode::STRICT_TOP_SIGNATURE,
                    RelationKind::StrictSubtype => {
                        SignatureCheckMode::STRICT_TOP_SIGNATURE | SignatureCheckMode::STRICT_ARITY
                    }
                    _ => SignatureCheckMode::NONE,
                };
                self.compare_signatures_related(source, target, mode, intersection_state)
            }
        }
    }

    fn compare_signatures_identical(
        &mut self,
        source: &ValidatedSingleCallable,
        target: &ValidatedSingleCallable,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        if source.signature == target.signature {
            return Ok(Ternary::True);
        }
        if source.parameters.len() != target.parameters.len()
            || source.min_argument_count != target.min_argument_count
        {
            return Ok(Ternary::False);
        }
        let key = (source.signature, target.signature, u32::MAX);
        if !self.active_signature_pairs.insert(key) {
            return Ok(Ternary::Maybe);
        }
        let result = (|| {
            let mut result = Ternary::True;
            for (source_type, target_type) in source.parameters.iter().zip(&target.parameters) {
                let related = self.is_related_to_ex(
                    *target_type,
                    *source_type,
                    RecursionFlags::BOTH,
                    intersection_state,
                )?;
                if related == Ternary::False {
                    return Ok(Ternary::False);
                }
                result &= related;
            }
            let source_return =
                source
                    .return_type
                    .ok_or(RelationUnavailable::UnresolvedSignatureReturn(
                        source.signature,
                    ))?;
            let target_return =
                target
                    .return_type
                    .ok_or(RelationUnavailable::UnresolvedSignatureReturn(
                        target.signature,
                    ))?;
            let returns = self.is_related_to_ex(
                source_return,
                target_return,
                RecursionFlags::BOTH,
                intersection_state,
            )?;
            Ok(result & returns)
        })();
        self.active_signature_pairs.remove(&key);
        result
    }

    #[allow(clippy::too_many_lines)] // Mirrors pinned compareSignaturesRelated branch order.
    fn compare_signatures_related(
        &mut self,
        source: &ValidatedSingleCallable,
        target: &ValidatedSingleCallable,
        check_mode: SignatureCheckMode,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        if source.signature == target.signature {
            return Ok(Ternary::True);
        }
        let key = (source.signature, target.signature, check_mode.bits());
        if !self.active_signature_pairs.insert(key) {
            return Ok(Ternary::Maybe);
        }
        let result =
            self.compare_signatures_related_worker(source, target, check_mode, intersection_state);
        self.active_signature_pairs.remove(&key);
        result
    }

    fn compare_signatures_related_worker(
        &mut self,
        source: &ValidatedSingleCallable,
        target: &ValidatedSingleCallable,
        check_mode: SignatureCheckMode,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        let target_count = target.parameters.len();
        let source_has_more_parameters = if check_mode.intersects(SignatureCheckMode::STRICT_ARITY)
        {
            source.parameters.len() > target_count
        } else {
            source.min_argument_count > target_count
        };
        if source_has_more_parameters {
            return Ok(Ternary::False);
        }

        let strict_variance = !check_mode.intersects(SignatureCheckMode::CALLBACK)
            && !target.strict_variance_exempt
            && self
                .strict_function_types
                .ok_or(RelationUnavailable::StructuredSignatures(target.owner))?;
        let mut result = Ternary::True;
        let parameter_count = source.parameters.len().max(target.parameters.len());
        for index in 0..parameter_count {
            let (Some(source_type), Some(target_type)) = (
                source.parameters.get(index).copied(),
                target.parameters.get(index).copied(),
            ) else {
                continue;
            };
            if source_type == target_type
                && !check_mode.intersects(SignatureCheckMode::STRICT_ARITY)
            {
                continue;
            }

            let (source_callback, source_nullable_facts) =
                if check_mode.intersects(SignatureCheckMode::CALLBACK) {
                    (None, 0)
                } else {
                    self.project_non_nullable_callable_signature(source_type)?
                };
            let (target_callback, target_nullable_facts) =
                if check_mode.intersects(SignatureCheckMode::CALLBACK) {
                    (None, 0)
                } else {
                    self.project_non_nullable_callable_signature(target_type)?
                };
            let mut related = if let (Some(source_callback), Some(target_callback)) =
                (source_callback.as_ref(), target_callback.as_ref())
                && source_nullable_facts == target_nullable_facts
            {
                let callback_mode = check_mode & SignatureCheckMode::STRICT_ARITY
                    | if strict_variance {
                        SignatureCheckMode::STRICT_CALLBACK
                    } else {
                        SignatureCheckMode::BIVARIANT_CALLBACK
                    };
                self.compare_signatures_related(
                    target_callback,
                    source_callback,
                    callback_mode,
                    intersection_state,
                )?
            } else {
                let mut related = Ternary::False;
                if !check_mode.intersects(SignatureCheckMode::CALLBACK) && !strict_variance {
                    related = self.is_related_to_ex(
                        source_type,
                        target_type,
                        RecursionFlags::BOTH,
                        intersection_state,
                    )?;
                }
                if related == Ternary::False {
                    related = self.is_related_to_ex(
                        target_type,
                        source_type,
                        RecursionFlags::BOTH,
                        intersection_state,
                    )?;
                }
                related
            };

            // Pinned strict subtype arity distinguishes an optional source
            // position from a required target position even after the type
            // relation itself succeeds.
            if related != Ternary::False
                && check_mode.intersects(SignatureCheckMode::STRICT_ARITY)
                && index >= source.min_argument_count
                && index < target.min_argument_count
                && self.is_related_to_ex(
                    source_type,
                    target_type,
                    RecursionFlags::BOTH,
                    intersection_state,
                )? != Ternary::False
            {
                related = Ternary::False;
            }
            if related == Ternary::False {
                return Ok(Ternary::False);
            }
            result &= related;
        }

        if check_mode.intersects(SignatureCheckMode::IGNORE_RETURN_TYPES) {
            return Ok(result);
        }
        let target_return =
            target
                .return_type
                .ok_or(RelationUnavailable::UnresolvedSignatureReturn(
                    target.signature,
                ))?;
        if target_return == self.bootstrap.void_type || target_return == self.bootstrap.any_type {
            return Ok(result);
        }
        let source_return =
            source
                .return_type
                .ok_or(RelationUnavailable::UnresolvedSignatureReturn(
                    source.signature,
                ))?;
        let mut related = Ternary::False;
        if check_mode.intersects(SignatureCheckMode::BIVARIANT_CALLBACK) {
            related = self.is_related_to_ex(
                target_return,
                source_return,
                RecursionFlags::BOTH,
                intersection_state,
            )?;
        }
        if related == Ternary::False {
            related = self.is_related_to_ex(
                source_return,
                target_return,
                RecursionFlags::BOTH,
                intersection_state,
            )?;
        }
        Ok(result & related)
    }

    fn property_related_to(
        &mut self,
        source_property: SemanticSymbolId,
        source_origin: ObjectPropertyOrigin,
        target_property: SemanticSymbolId,
        target_origin: ObjectPropertyOrigin,
    ) -> Result<Ternary, RelationUnavailable> {
        let (source_flags, source_readonly) = {
            let source = self.property_symbol(source_property, source_origin)?;
            (
                source.flags(),
                source.check_flags().contains(CheckFlags::READONLY),
            )
        };
        let (target_flags, target_readonly) = {
            let target = self.property_symbol(target_property, target_origin)?;
            (
                target.flags(),
                target.check_flags().contains(CheckFlags::READONLY),
            )
        };
        // Pinned `propertyRelatedTo`: readonly affects only strict subtype
        // ordering. Ordinary assignability remains intentionally symmetric.
        if self.relation == RelationKind::StrictSubtype && source_readonly && !target_readonly {
            return Ok(Ternary::False);
        }
        let source_type = self.property_type(source_property)?;
        let target_type = self.property_type(target_property)?;
        let source_types = self.effective_property_types(
            source_type,
            source_flags.intersects(SymbolFlags::OPTIONAL)
                && self.relation != RelationKind::Comparable,
        )?;
        let target_types = self.effective_property_types(
            target_type,
            target_flags.intersects(SymbolFlags::OPTIONAL),
        )?;
        let related = self.property_types_related(&source_types, &target_types)?;
        if self.relation != RelationKind::Comparable
            && related != Ternary::False
            && source_flags.intersects(SymbolFlags::OPTIONAL)
            && !target_flags.intersects(SymbolFlags::OPTIONAL)
        {
            Ok(Ternary::False)
        } else {
            Ok(related)
        }
    }

    fn effective_property_types(
        &mut self,
        type_id: TypeId,
        optional: bool,
    ) -> Result<Vec<TypeId>, RelationUnavailable> {
        let flags = self.store.type_flags(type_id)?;
        if !self.bootstrap.strict_null_checks || !optional {
            return Ok(vec![type_id]);
        }
        if self.bootstrap.exact_optional_property_types {
            if type_id == self.bootstrap.missing_type {
                return Ok(vec![self.bootstrap.never_type]);
            }
            if flags.intersects(TypeFlags::UNION) {
                let types = self.union_types(type_id)?;
                if types.contains(&self.bootstrap.missing_type) {
                    let mut types = types
                        .into_iter()
                        .filter(|candidate| *candidate != self.bootstrap.missing_type)
                        .collect::<Vec<_>>();
                    if types.is_empty() {
                        types.push(self.bootstrap.never_type);
                    }
                    return Ok(types);
                }
            }
            return Ok(vec![type_id]);
        }
        let contains_undefined = type_id == self.bootstrap.undefined_type
            || flags.intersects(TypeFlags::UNION)
                && self
                    .union_types(type_id)?
                    .contains(&self.bootstrap.undefined_type);
        if contains_undefined {
            return Ok(vec![type_id]);
        }
        // Source construction retains the declared/base annotation and the
        // OPTIONAL symbol bit. Model pinned `T | undefined` here without
        // allocating a relation-owned union or mutating semantic state.
        Ok(vec![self.bootstrap.undefined_type, type_id])
    }

    fn property_types_related(
        &mut self,
        source_types: &[TypeId],
        target_types: &[TypeId],
    ) -> Result<Ternary, RelationUnavailable> {
        if source_types.is_empty() {
            return Ok(Ternary::True);
        }
        if target_types.is_empty() {
            return Ok(Ternary::False);
        }
        let mut result = Ternary::True;
        for source_type in source_types {
            let mut related = Ternary::False;
            for target_type in target_types {
                let candidate = self.is_related_to_ex(
                    *source_type,
                    *target_type,
                    RecursionFlags::BOTH,
                    IntersectionState::NONE,
                )?;
                if candidate != Ternary::False {
                    related = candidate;
                    break;
                }
            }
            if related == Ternary::False {
                return Ok(Ternary::False);
            }
            result &= related;
        }
        Ok(result)
    }

    fn property_type(&self, symbol: SemanticSymbolId) -> Result<TypeId, RelationUnavailable> {
        self.store
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            .ok_or(RelationUnavailable::UnresolvedPropertyType(symbol))
    }

    fn lookup_source_property(
        &mut self,
        source: TypeId,
        source_members: &ResolvedObjectMembers,
        target_property: SemanticSymbolId,
        target_origin: ObjectPropertyOrigin,
    ) -> Result<Option<SemanticSymbolId>, RelationUnavailable> {
        let target_symbol = self.property_symbol(target_property, target_origin)?;
        let name = target_symbol.name().to_owned();
        if let Some(members) = source_members.members {
            self.observe_symbol_table(members);
            let property = self
                .store
                .symbol_table(members)
                .ok_or(RelationUnavailable::InvalidStructuredMembers(source))?
                .get(name.as_ref());
            if let Some(property) = property {
                self.property_symbol(property, source_members.property_origin)?;
                return Ok(Some(property));
            }
        }
        self.global_object_property(name.as_ref())
    }

    fn global_object_property(
        &mut self,
        name: ts_binder::EscapedNameRef<'_>,
    ) -> Result<Option<SemanticSymbolId>, RelationUnavailable> {
        let Some(global_object) = self.global_object_symbol()? else {
            return Ok(None);
        };
        let Some(global_object_type) = self
            .store
            .declared_type_links(global_object)
            .and_then(|links| links.declared_type)
        else {
            return Err(RelationUnavailable::UnresolvedGlobalObject(global_object));
        };
        self.ensure_supported_object_kind(global_object_type, false)?;
        let (object_flags, no_inherited_members, structured) = self
            .store
            .type_payload(global_object_type)
            .map(|record| {
                (
                    record.object_flags(),
                    match record.data() {
                        TypeData::Object(_) => true,
                        TypeData::Interface(interface) => {
                            interface.base_types_resolved
                                && interface.resolved_base_constructor_type.is_none()
                                && interface.resolved_base_types.is_none()
                        }
                        _ => false,
                    },
                    record.data().structured().cloned(),
                )
            })
            .ok_or(RelationUnavailable::Type(global_object_type))?;
        if no_inherited_members && self.raw_symbol_members_prove_absent(global_object, name)? {
            return Ok(None);
        }
        if !object_flags.intersects(ObjectFlags::MEMBERS_RESOLVED) {
            return Err(RelationUnavailable::UnresolvedStructuredMembers(
                global_object_type,
            ));
        }
        let structured = structured.ok_or(RelationUnavailable::MalformedStructuredType(
            global_object_type,
        ))?;
        let properties = structured.properties.unwrap_or_default();
        for property in &properties {
            self.observe_merged_symbol_lookup(*property);
        }
        let mut property_set = HashSet::with_capacity(properties.len());
        for property in &properties {
            if !property_set.insert(*property) || self.store.symbol(*property).is_none() {
                return Err(RelationUnavailable::InvalidStructuredMembers(
                    global_object_type,
                ));
            }
        }
        let Some(members) = structured.members else {
            if properties.is_empty() {
                return Ok(None);
            }
            return Err(RelationUnavailable::InvalidStructuredMembers(
                global_object_type,
            ));
        };
        self.observe_symbol_table(members);
        let table = self.store.symbol_table(members).ok_or(
            RelationUnavailable::InvalidStructuredMembers(global_object_type),
        )?;
        if table.len() != properties.len() {
            return Err(RelationUnavailable::InvalidStructuredMembers(
                global_object_type,
            ));
        }
        for (member_name, property) in table.iter() {
            let symbol = self.store.symbol(property).ok_or(
                RelationUnavailable::InvalidStructuredMembers(global_object_type),
            )?;
            if symbol.name() != member_name || !property_set.contains(&property) {
                return Err(RelationUnavailable::InvalidStructuredMembers(
                    global_object_type,
                ));
            }
        }
        for property in &properties {
            let symbol = self.store.symbol(*property).ok_or(
                RelationUnavailable::InvalidStructuredMembers(global_object_type),
            )?;
            if table.get(symbol.name()) != Some(*property) {
                return Err(RelationUnavailable::InvalidStructuredMembers(
                    global_object_type,
                ));
            }
        }
        let Some(property) = table.get(name) else {
            return Ok(None);
        };
        self.property_symbol(property, ObjectPropertyOrigin::Declared)?;
        Ok(Some(property))
    }

    fn unresolved_primitive_wrapper_lacks_required_property(
        &mut self,
        wrapper: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let (owner, eligible) = {
            let record = self
                .store
                .type_payload(wrapper)
                .ok_or(RelationUnavailable::Type(wrapper))?;
            let TypeData::Interface(interface) = record.data() else {
                return Ok(false);
            };
            let Some(owner) = record.symbol() else {
                return Ok(false);
            };
            (
                owner,
                record.flags() == TypeFlags::OBJECT
                    && record.object_flags().intersects(ObjectFlags::INTERFACE)
                    && !record
                        .object_flags()
                        .intersects(ObjectFlags::CLASS | ObjectFlags::MEMBERS_RESOLVED)
                    && interface.resolved_base_types.is_none()
                    && self
                        .store
                        .direct_interface_heritage_provenance(wrapper)
                        .is_none(),
            )
        };
        if !eligible {
            return Ok(false);
        }
        let owner_record = self
            .store
            .symbol(owner)
            .ok_or(RelationUnavailable::Symbol(owner))?;
        if owner_record.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
            || self.observe_merged_symbol_lookup(owner) != Some(owner)
            || self
                .store
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                != Some(wrapper)
        {
            return Err(RelationUnavailable::InvalidStructuredMembers(wrapper));
        }
        if !self.interface_declarations_prove_no_heritage(owner, wrapper)? {
            return Ok(false);
        }

        let target_members =
            self.resolved_object_property_surface(target, self.allows_fresh_object_target())?;
        for property in target_members.properties {
            let (required, name) = {
                let symbol = self.property_symbol(property, target_members.property_origin)?;
                (
                    !symbol.flags().contains(SymbolFlags::OPTIONAL),
                    symbol.name().to_owned(),
                )
            };
            if required
                && self.raw_symbol_members_prove_absent(owner, name.as_ref())?
                && self.global_object_property(name.as_ref())?.is_none()
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn interface_declarations_prove_no_heritage(
        &self,
        owner: SemanticSymbolId,
        wrapper: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let declarations = self
            .store
            .symbol(owner)
            .and_then(|symbol| symbol.declarations())
            .ok_or(RelationUnavailable::InvalidStructuredMembers(wrapper))?;
        let mut saw_interface = false;
        for declaration in declarations {
            match self.store.source_node_kind(*declaration) {
                Some(SyntaxKind::VariableDeclaration) => continue,
                Some(SyntaxKind::InterfaceDeclaration) => saw_interface = true,
                _ => return Ok(false),
            }

            let mut found_name = false;
            for index in (0..declaration.node.index()).rev() {
                let node = NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    NodeId::new(
                        u32::try_from(index)
                            .map_err(|_| RelationUnavailable::InvalidStructuredMembers(wrapper))?,
                    ),
                );
                if self.store.source_node_parent(node)
                    != Some(SourceNodeParent::Parent(*declaration))
                {
                    continue;
                }
                match self.store.source_node_kind(node) {
                    Some(SyntaxKind::HeritageClause) => return Ok(false),
                    Some(SyntaxKind::Identifier) => {
                        found_name = true;
                        break;
                    }
                    Some(_) => {}
                    None => return Err(RelationUnavailable::InvalidStructuredMembers(wrapper)),
                }
            }
            if !found_name {
                return Err(RelationUnavailable::InvalidStructuredMembers(wrapper));
            }
        }
        Ok(saw_interface)
    }

    fn raw_symbol_members_prove_absent(
        &mut self,
        symbol: SemanticSymbolId,
        name: ts_binder::EscapedNameRef<'_>,
    ) -> Result<bool, RelationUnavailable> {
        self.observe_symbol(symbol);
        let record = self
            .store
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?;
        let Some(members) = record.members() else {
            return Ok(true);
        };
        self.observe_symbol_table(members);
        let table = self
            .store
            .symbol_table(members)
            .ok_or(RelationUnavailable::InvalidSymbolMembers(symbol))?;
        for (member_name, member) in table.iter() {
            let member = self
                .store
                .symbol(member)
                .ok_or(RelationUnavailable::InvalidSymbolMembers(symbol))?;
            if member.name() != member_name {
                return Err(RelationUnavailable::InvalidSymbolMembers(symbol));
            }
        }
        if table.get(InternalSymbolName::Computed.as_ref()).is_some() {
            return Ok(false);
        }
        Ok(table.get(name).is_none())
    }

    fn global_object_symbol(&mut self) -> Result<Option<SemanticSymbolId>, RelationUnavailable> {
        let globals_id = self
            .store
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(RelationUnavailable::MissingBootstrap)?
            .globals;
        let globals = self
            .store
            .symbol_table(globals_id)
            .ok_or(RelationUnavailable::MissingBootstrap)?;
        let Some(global_object) = globals.get_source("Object") else {
            return Ok(None);
        };
        self.observe_merged_symbol_lookup(global_object)
            .map(Some)
            .ok_or(RelationUnavailable::Symbol(global_object))
    }

    fn property_symbol(
        &mut self,
        symbol: SemanticSymbolId,
        origin: ObjectPropertyOrigin,
    ) -> Result<&ts_binder::semantic::Symbol, RelationUnavailable> {
        let record = self
            .store
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?;
        match origin {
            ObjectPropertyOrigin::Intersection(owner) => {
                return if self
                    .intersection_projection(owner)?
                    .properties
                    .contains(&symbol)
                {
                    Ok(record)
                } else {
                    Err(RelationUnavailable::UnsupportedProperty(symbol))
                };
            }
            ObjectPropertyOrigin::FreshObjectLiteral(owner) => {
                return if self.is_canonical_object_literal_property(symbol, record, owner) {
                    Ok(record)
                } else {
                    Err(RelationUnavailable::UnsupportedProperty(symbol))
                };
            }
            ObjectPropertyOrigin::DerivedObjectLiteral { owner, receiver } => {
                // The object-wide warm-cache validator established the full
                // clone/reuse chain before this marker was constructed. A
                // contextual widened union can also borrow an authenticated
                // optional property from a sibling object's owner.
                return if self.store.get_merged_symbol(symbol) == Some(symbol)
                    && (record.parent() == Some(owner)
                        || record.parent().is_some()
                            && record.flags().contains(SymbolFlags::OPTIONAL)
                            && self
                                .store
                                .validate_contextual_widened_object_property(receiver, symbol))
                {
                    Ok(record)
                } else {
                    Err(RelationUnavailable::UnsupportedProperty(symbol))
                };
            }
            ObjectPropertyOrigin::GenericReference(reference)
                if record.flags().contains(SymbolFlags::TRANSIENT) =>
            {
                let Some(validated) = validate_generic_interface_members(
                    self.store,
                    reference,
                    self.global_types.map(|globals| globals.array_targets),
                )
                .map_err(|_| RelationUnavailable::UnsupportedProperty(symbol))?
                else {
                    return Err(RelationUnavailable::UnresolvedStructuredMembers(reference));
                };
                if !validated.properties().contains(&symbol) {
                    return Err(RelationUnavailable::UnsupportedProperty(symbol));
                }
                let Some(links) = self.store.value_symbol_links(symbol) else {
                    return Err(RelationUnavailable::UnsupportedProperty(symbol));
                };
                let Some(target) = links.target else {
                    return Err(RelationUnavailable::UnsupportedProperty(symbol));
                };
                let Some(target_record) = self.store.symbol(target) else {
                    return Err(RelationUnavailable::UnsupportedProperty(symbol));
                };
                let mapper_valid = links.mapper == validated.mapper()
                    && links
                        .mapper
                        .is_some_and(|mapper| self.store.mapper_payload(mapper).is_some());
                let expected_checks = CheckFlags::INSTANTIATED
                    | (target_record.check_flags()
                        & (CheckFlags::READONLY
                            | CheckFlags::LATE
                            | CheckFlags::OPTIONAL_PARAMETER
                            | CheckFlags::REST_PARAMETER));
                let reference_owner = self
                    .store
                    .type_payload(reference)
                    .and_then(TypeRecord::symbol);
                return if record.flags() == target_record.flags() | SymbolFlags::TRANSIENT
                    && record.check_flags() == expected_checks
                    && record.name() == target_record.name()
                    && record.declarations() == target_record.declarations()
                    && record.value_declaration() == target_record.value_declaration()
                    && record.parent() == target_record.parent()
                    && record.parent() == reference_owner
                    && record.members().is_none()
                    && record.exports().is_none()
                    && record.export_symbol().is_none()
                    && mapper_valid
                    && links
                        == &(ValueSymbolLinks {
                            resolved_type: links.resolved_type,
                            target: Some(target),
                            mapper: validated.mapper(),
                            name_type: self
                                .store
                                .value_symbol_links(target)
                                .and_then(|links| links.name_type),
                            ..ValueSymbolLinks::default()
                        })
                    && self.store.get_merged_symbol(symbol) == Some(symbol)
                {
                    Ok(record)
                } else {
                    Err(RelationUnavailable::UnsupportedProperty(symbol))
                };
            }
            ObjectPropertyOrigin::Declared
            | ObjectPropertyOrigin::ValidatedClass
            | ObjectPropertyOrigin::GenericReference(_) => {}
        }
        if matches!(origin, ObjectPropertyOrigin::ValidatedClass)
            && record.flags() == SymbolFlags::METHOD
        {
            self.validated_class_method_callable(symbol)?;
            return Ok(record);
        }
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
        let allowed_checks = CheckFlags::READONLY.bits();
        if !record.flags().contains(SymbolFlags::PROPERTY)
            || record.flags().without(allowed_flags) != SymbolFlags::NONE
            || record.check_flags().bits() & !allowed_checks != 0
            || record.name().is_reserved_member_name()
            || record.name().is_private_identifier()
            || record.name().is_late_bound()
        {
            return Err(RelationUnavailable::UnsupportedProperty(symbol));
        }
        if let Some(parent) = record.parent() {
            let parent = self
                .store
                .symbol(parent)
                .ok_or(RelationUnavailable::Symbol(parent))?;
            let allowed_parent_flags = match origin {
                ObjectPropertyOrigin::ValidatedClass => SymbolFlags::CLASS,
                ObjectPropertyOrigin::Declared | ObjectPropertyOrigin::GenericReference(_) => {
                    SymbolFlags::INTERFACE | SymbolFlags::TYPE_LITERAL
                }
                ObjectPropertyOrigin::FreshObjectLiteral(_)
                | ObjectPropertyOrigin::DerivedObjectLiteral { .. }
                | ObjectPropertyOrigin::Intersection(_) => {
                    unreachable!("literal property origins return before declared validation")
                }
            };
            if !parent.flags().intersects(allowed_parent_flags) {
                return Err(RelationUnavailable::UnsupportedProperty(symbol));
            }
        } else if record
            .declarations()
            .is_some_and(|declarations| !declarations.is_empty())
        {
            return Err(RelationUnavailable::UnsupportedProperty(symbol));
        }
        Ok(record)
    }

    fn validated_class_method_callable(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<ValidatedSingleCallable, RelationUnavailable> {
        let unsupported = || RelationUnavailable::UnsupportedProperty(symbol);
        let method = self.store.symbol(symbol).ok_or_else(unsupported)?;
        let Some([declaration]) = method.declarations() else {
            return Err(unsupported());
        };
        let declaration = *declaration;
        let owner = method.parent().ok_or_else(unsupported)?;
        let class = self.store.symbol(owner).ok_or_else(unsupported)?;
        let Some([class_declaration]) = class.declarations() else {
            return Err(unsupported());
        };
        let instance = self
            .store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .ok_or_else(unsupported)?;
        if method.flags() != SymbolFlags::METHOD
            || method.check_flags() != CheckFlags::NONE
            || method.name().is_reserved_member_name()
            || method.name().is_private_identifier()
            || method.name().is_late_bound()
            || method.value_declaration() != Some(declaration)
            || method.members().is_some()
            || method.exports().is_some()
            || method.export_symbol().is_some()
            || self.store.get_merged_symbol(symbol) != Some(symbol)
            || !class.flags().intersects(SymbolFlags::CLASS)
            || self.store.source_node_kind(declaration) != Some(SyntaxKind::MethodDeclaration)
            || self.store.source_node_parent(declaration)
                != Some(SourceNodeParent::Parent(*class_declaration))
            || validate_class_heritage_members(self.store, instance)
                != ClassHeritageMembersValidation::Valid
        {
            return Err(unsupported());
        }

        let links = self
            .store
            .value_symbol_links(symbol)
            .ok_or_else(unsupported)?;
        let owner_type = links.resolved_type.ok_or_else(unsupported)?;
        if links
            != &(ValueSymbolLinks {
                resolved_type: Some(owner_type),
                ..ValueSymbolLinks::default()
            })
        {
            return Err(unsupported());
        }
        let record = self
            .store
            .type_payload(owner_type)
            .ok_or_else(unsupported)?;
        let TypeData::Object(object) = record.data() else {
            return Err(unsupported());
        };
        let Some([signature]) = object.structured.signatures.as_deref() else {
            return Err(unsupported());
        };
        let signature = *signature;
        let signature_record = self.store.signature(signature).ok_or_else(unsupported)?;
        let return_type = signature_record
            .resolved_return_type()
            .ok_or_else(unsupported)?;
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
            || record.symbol() != Some(symbol)
            || record.alias().is_some()
            || object.target.is_some()
            || object.mapper.is_some()
            || object.instantiations != TypeCacheState::Unallocated
            || object.structured.constrained != ConstrainedTypeData::default()
            || object.structured.members.is_some()
            || object.structured.properties.is_some()
            || object.structured.call_signature_count != 1
            || object.structured.index_infos.is_some()
            || object
                .structured
                .object_type_without_abstract_construct_signatures
                .is_some()
            || signature_record.flags() != SignatureFlags::NONE
            || signature_record.declaration() != Some(declaration)
            || !signature_record.type_parameters().is_empty()
            || !signature_record.parameters().is_empty()
            || signature_record.this_parameter().is_some()
            || signature_record.min_argument_count() != 0
            || signature_record.resolved_min_argument_count() != -1
            || signature_record.resolved_type_predicate().is_some()
            || signature_record.target().is_some()
            || signature_record.mapper().is_some()
            || signature_record.isolated_signature_type().is_some()
            || signature_record.composite().is_some()
            || ![
                self.bootstrap.void_type,
                self.bootstrap.any_type,
                self.bootstrap.undefined_type,
            ]
            .contains(&return_type)
            || self.store.signature_links(declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
        {
            return Err(unsupported());
        }
        Ok(ValidatedSingleCallable {
            owner: owner_type,
            signature,
            parameters: Vec::new(),
            rest_parameter: None,
            min_argument_count: 0,
            return_type: Some(return_type),
            strict_variance_exempt: true,
        })
    }

    fn is_canonical_object_literal_property(
        &self,
        symbol: SemanticSymbolId,
        record: &ts_binder::semantic::Symbol,
        owner: SemanticSymbolId,
    ) -> bool {
        let name = record.name();
        if record.flags() != SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            || record.check_flags() != CheckFlags::NONE
            || name.is_internal()
            || name.is_private_identifier()
            || name.is_late_bound()
            || record.parent() != Some(owner)
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || self.store.get_merged_symbol(symbol) != Some(symbol)
        {
            return false;
        }
        let Some([declaration]) = record.declarations() else {
            return false;
        };
        if record.value_declaration() != Some(*declaration) {
            return false;
        }

        let Some(links) = self.store.value_symbol_links(symbol) else {
            return false;
        };
        let (Some(resolved_type), Some(target)) = (links.resolved_type, links.target) else {
            return false;
        };
        let expected_links = ValueSymbolLinks {
            resolved_type: Some(resolved_type),
            target: Some(target),
            ..ValueSymbolLinks::default()
        };
        if links != &expected_links || self.store.type_payload(resolved_type).is_none() {
            return false;
        }

        let Some(target_record) = self.store.symbol(target) else {
            return false;
        };
        if target_record.flags() != SymbolFlags::PROPERTY
            || target_record.check_flags() != CheckFlags::NONE
            || target_record.name() != name
            || target_record.declarations() != record.declarations()
            || target_record.value_declaration() != record.value_declaration()
            || target_record.parent() != Some(owner)
            || target_record.members().is_some()
            || target_record.exports().is_some()
            || target_record.export_symbol().is_some()
            || self.store.get_merged_symbol(target) != Some(target)
            || self
                .store
                .value_symbol_links(target)
                .is_some_and(|links| links != &ValueSymbolLinks::default())
        {
            return false;
        }

        matches!(
            self.canonical_object_literal_raw_members_unobserved(owner),
            Some(CanonicalObjectLiteralRawMembers::Allocated(members))
                if members.get(name) == Some(target)
        )
    }

    fn canonical_object_literal_raw_members(
        &self,
        owner: SemanticSymbolId,
    ) -> Option<CanonicalObjectLiteralRawMembers<'_>> {
        self.canonical_object_literal_raw_members_unobserved(owner)
    }

    fn canonical_object_literal_raw_members_unobserved(
        &self,
        owner: SemanticSymbolId,
    ) -> Option<CanonicalObjectLiteralRawMembers<'_>> {
        let owner_record = self.store.symbol(owner)?;
        let [owner_declaration] = owner_record.declarations()? else {
            return None;
        };
        if owner_record.flags() != SymbolFlags::OBJECT_LITERAL
            || owner_record.check_flags() != CheckFlags::NONE
            || owner_record.name() != InternalSymbolName::Object.as_ref()
            || owner_record.value_declaration() != Some(*owner_declaration)
            || owner_record.parent().is_some()
            || owner_record.exports().is_some()
            || owner_record.export_symbol().is_some()
            || self.store.get_merged_symbol(owner) != Some(owner)
        {
            return None;
        }
        match owner_record.members() {
            None => Some(CanonicalObjectLiteralRawMembers::Nil),
            Some(members) => self
                .store
                .symbol_table(members)
                .map(CanonicalObjectLiteralRawMembers::Allocated),
        }
    }

    fn ensure_supported_recursive_pair(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<(), RelationUnavailable> {
        let source_flags = self.store.type_flags(source)?;
        let target_flags = self.store.type_flags(target)?;
        let source_is_union = source_flags.intersects(TypeFlags::UNION);
        let target_is_union = target_flags.intersects(TypeFlags::UNION);
        let source_is_intersection = source_flags.intersects(TypeFlags::INTERSECTION);
        let target_is_intersection = target_flags.intersects(TypeFlags::INTERSECTION);
        if source_is_union {
            self.union_types(source)?;
        }
        if target_is_union {
            self.union_types(target)?;
        }
        if source_is_intersection {
            self.intersection_projection(source)?;
        }
        if target_is_intersection {
            self.intersection_projection(target)?;
        }
        if source_is_union || target_is_union || source_is_intersection || target_is_intersection {
            return Ok(());
        }
        if supports_structured_object_relation(self.relation, self.strict_function_types)
            && source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::OBJECT)
        {
            self.ensure_supported_object_kind(source, true)?;
            self.ensure_supported_object_kind(target, self.allows_fresh_object_target())?;
            return Ok(());
        }
        Err(RelationUnavailable::StructuralRelation {
            source,
            target,
            relation: self.relation,
        })
    }

    /// Admits branded function objects before any relation-cache read.
    ///
    /// Function variance is checker-option dependent while relation cache
    /// keys are not. This boundary therefore also prevents legacy callers
    /// without an explicit option from consuming a callable result produced
    /// by an option-aware session. A branded object that passes the callable
    /// validator but fails the generic object proof is one malformed function
    /// cache, not an unsupported property-object family.
    fn ensure_callable_relation_admission(
        &mut self,
        type_id: TypeId,
        allow_fresh_literal: bool,
    ) -> Result<(), RelationUnavailable> {
        let is_function = self
            .store
            .admit_callable_relation_type(type_id, self.strict_function_types)?;
        if is_function {
            self.ensure_supported_object_kind(type_id, allow_fresh_literal)
                .map_err(|_| RelationUnavailable::MalformedFunctionType(type_id))?;
        }
        Ok(())
    }

    fn ensure_supported_object_kind(
        &mut self,
        type_id: TypeId,
        allow_fresh_literal: bool,
    ) -> Result<(), RelationUnavailable> {
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if record.flags() == TypeFlags::INTERSECTION {
            self.intersection_projection(type_id)?;
            return Ok(());
        }
        if record.flags() != TypeFlags::OBJECT || !self.supports_property_object_alias(type_id) {
            return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
        }
        if record.object_flags().intersects(ObjectFlags::REFERENCE) {
            let reference_target = match record.data() {
                TypeData::TypeReference(reference) => reference.object.target,
                TypeData::Interface(interface) => interface.reference.object.target,
                _ => None,
            };
            let configured_array = self.global_types.is_some_and(|globals| {
                reference_target.is_some_and(|target| globals.contains_array_target(target))
            });
            let interface_target = reference_target
                .and_then(|target| self.store.type_payload(target))
                .is_some_and(|target| {
                    matches!(target.data(), TypeData::Interface(_))
                        && target.object_flags().contains(ObjectFlags::INTERFACE)
                        && !target.object_flags().intersects(ObjectFlags::CLASS)
                        && target
                            .symbol()
                            .and_then(|owner| self.store.symbol(owner))
                            .is_some_and(|owner| owner.flags() == SymbolFlags::INTERFACE)
                });
            if !configured_array && interface_target {
                let source_declared_target = reference_target
                    .and_then(|target| self.store.type_payload(target))
                    .and_then(TypeRecord::symbol)
                    .and_then(|owner| self.store.symbol(owner))
                    .and_then(|owner| match owner.declarations() {
                        Some([declaration]) => Some(*declaration),
                        _ => None,
                    })
                    .is_some_and(|declaration| {
                        self.store.source_node_kind(declaration)
                            == Some(SyntaxKind::InterfaceDeclaration)
                    });
                if !source_declared_target {
                    return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
                }
                return match validate_generic_interface_members(
                    self.store,
                    type_id,
                    self.global_types.map(|globals| globals.array_targets),
                ) {
                    Ok(Some(_)) => Ok(()),
                    Ok(None) => Err(RelationUnavailable::UnresolvedStructuredMembers(type_id)),
                    Err(GenericInterfaceMemberError::UnsupportedTarget(_)) => {
                        Err(RelationUnavailable::UnsupportedStructuredType(type_id))
                    }
                    Err(GenericInterfaceMemberError::UnsupportedMember(symbol)) => {
                        Err(RelationUnavailable::UnsupportedProperty(symbol))
                    }
                    Err(GenericInterfaceMemberError::UnsupportedPropertyType(type_)) => {
                        Err(RelationUnavailable::UnsupportedStructuredType(type_))
                    }
                    Err(GenericInterfaceMemberError::Capacity(_)) => {
                        Err(RelationUnavailable::UnionValidationCapacity(type_id))
                    }
                    Err(
                        GenericInterfaceMemberError::Reference(_)
                        | GenericInterfaceMemberError::InvalidTarget(_)
                        | GenericInterfaceMemberError::InvalidMember(_)
                        | GenericInterfaceMemberError::InvalidCachedMembers(_)
                        | GenericInterfaceMemberError::InvalidCachedProperty(_),
                    ) => Err(RelationUnavailable::InvalidStructuredMembers(type_id)),
                };
            }
        }
        match validate_class_heritage_members(self.store, type_id) {
            ClassHeritageMembersValidation::Valid => return Ok(()),
            ClassHeritageMembersValidation::Malformed => {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            }
            ClassHeritageMembersValidation::NotClass => {}
        }
        match self.validate_derived_object_literal(type_id) {
            DerivedObjectLiteralValidation::Valid { .. } => return Ok(()),
            DerivedObjectLiteralValidation::Invalid => {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            }
            DerivedObjectLiteralValidation::NotDerived => {}
        }
        let kind = record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK;
        if kind != ObjectFlags::NONE
            && kind != ObjectFlags::INTERFACE
            && kind != ObjectFlags::ANONYMOUS
        {
            return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
        }
        let fresh_object_literal = ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL;
        let unsupported_flags = ObjectFlags::CLASS
            | ObjectFlags::REFERENCE
            | ObjectFlags::TUPLE
            | ObjectFlags::MAPPED
            | ObjectFlags::REVERSE_MAPPED
            | ObjectFlags::EVOLVING_ARRAY
            | ObjectFlags::INSTANTIATED
            | ObjectFlags::ARRAY_LITERAL
            | ObjectFlags::JSX_ATTRIBUTES
            | ObjectFlags::JS_LITERAL
            | ObjectFlags::CONTAINS_SPREAD
            | ObjectFlags::OBJECT_REST_TYPE
            | ObjectFlags::IS_CLASS_INSTANCE_CLONE
            | ObjectFlags::OBJECT_LITERAL_PATTERN_WITH_COMPUTED_PROPERTIES
            | ObjectFlags::UNRESOLVED_MEMBERS;
        if record.object_flags().intersects(unsupported_flags)
            || record.object_flags().intersects(fresh_object_literal)
                && (!allow_fresh_literal || !record.object_flags().contains(fresh_object_literal))
        {
            return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
        }
        match (kind, record.data()) {
            (ObjectFlags::INTERFACE, TypeData::Interface(interface))
                if interface
                    .all_type_parameters
                    .as_ref()
                    .is_none_or(Vec::is_empty) => {}
            (ObjectFlags::NONE | ObjectFlags::ANONYMOUS, TypeData::Object(_)) => {}
            _ => return Err(RelationUnavailable::UnsupportedStructuredType(type_id)),
        }
        Ok(())
    }

    fn validate_derived_object_literal(&self, type_id: TypeId) -> DerivedObjectLiteralValidation {
        match self.global_types {
            Some(global_types) => self
                .store
                .validate_derived_object_literal_with_array_targets(
                    type_id,
                    global_types.array_targets,
                ),
            None => self
                .store
                .validate_derived_object_literal_for_relation(type_id),
        }
    }

    fn supports_property_object_alias(&self, type_id: TypeId) -> bool {
        let Some(record) = self.store.type_payload(type_id) else {
            return false;
        };
        let Some(alias_id) = record.alias() else {
            return true;
        };
        if !matches!(record.data(), TypeData::Object(_))
            || record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK != ObjectFlags::ANONYMOUS
            || record
                .object_flags()
                .intersects(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL)
        {
            return false;
        }
        let Some(owner) = record.symbol() else {
            return false;
        };
        let Some(owner_record) = self.store.symbol(owner) else {
            return false;
        };
        let Some([_owner_declaration]) = owner_record.declarations() else {
            return false;
        };
        if self.store.get_merged_symbol(owner) != Some(owner)
            || owner_record.flags() != SymbolFlags::TYPE_LITERAL
            || owner_record.check_flags() != CheckFlags::NONE
            || owner_record.name() != InternalSymbolName::Type.as_ref()
            || owner_record.value_declaration().is_some()
            || owner_record.parent().is_some()
            || owner_record.exports().is_some()
            || owner_record.export_symbol().is_some()
        {
            return false;
        }
        let Some(alias) = self.store.type_alias(alias_id) else {
            return false;
        };
        let Some(alias_symbol) = alias.symbol() else {
            return false;
        };
        let Some(alias_record) = self.store.symbol(alias_symbol) else {
            return false;
        };
        if alias.type_arguments().is_some()
            || self.store.get_merged_symbol(alias_symbol) != Some(alias_symbol)
            || alias_record.flags() != SymbolFlags::TYPE_ALIAS
            || alias_record.check_flags() != CheckFlags::NONE
        {
            return false;
        }
        self.store
            .type_alias_links(alias_symbol)
            .is_some_and(|links| {
                links.declared_type == Some(type_id)
                    && links.type_parameters.is_none()
                    && links.instantiations.is_none()
                    && !links.is_constructor_declared_property
            })
    }

    fn project_exact_callable_signature(
        &mut self,
        type_: TypeId,
    ) -> Result<Option<ValidatedSingleCallable>, RelationUnavailable> {
        let mut callable = match validate_stored_single_callable(self.store, type_) {
            StoredSingleCallableValidation::NotCallable => {
                let Some(symbol) = self.store.type_payload(type_).and_then(TypeRecord::symbol)
                else {
                    return Ok(None);
                };
                if self
                    .store
                    .symbol(symbol)
                    .is_none_or(|record| record.flags() != SymbolFlags::METHOD)
                {
                    return Ok(None);
                }
                let callable = self
                    .validated_class_method_callable(symbol)
                    .map_err(|_| RelationUnavailable::MalformedFunctionType(type_))?;
                if callable.owner != type_ {
                    return Err(RelationUnavailable::MalformedFunctionType(type_));
                }
                callable
            }
            StoredSingleCallableValidation::Pending { .. } => {
                return Err(if self.strict_function_types.is_some() {
                    RelationUnavailable::UnresolvedFunctionType(type_)
                } else {
                    RelationUnavailable::StructuredSignatures(type_)
                });
            }
            StoredSingleCallableValidation::Malformed { .. } => {
                return Err(RelationUnavailable::MalformedFunctionType(type_));
            }
            StoredSingleCallableValidation::Valid { callable, .. } => callable,
        };
        if self.strict_function_types.is_none() && !callable.strict_variance_exempt {
            return Err(RelationUnavailable::StructuredSignatures(type_));
        }
        while callable.min_argument_count != 0
            && self.type_contains_void(callable.parameters[callable.min_argument_count - 1])?
        {
            callable.min_argument_count -= 1;
        }
        Ok(Some(callable))
    }

    /// Property-only preflight used before recursive structural comparison.
    ///
    /// Pinned excess/weak checks inspect properties before
    /// `signaturesRelatedTo`. An exact function type therefore contributes an
    /// empty property surface here without consuming the callable capability
    /// (or forcing a lazy return); the full projection is admitted only inside
    /// `structured_type_related_to`, preserving source-first typed boundaries.
    fn resolved_object_property_surface(
        &mut self,
        type_: TypeId,
        allow_fresh_literal: bool,
    ) -> Result<ResolvedObjectMembers, RelationUnavailable> {
        if self
            .store
            .admit_callable_relation_type(type_, self.strict_function_types)?
        {
            self.ensure_supported_object_kind(type_, allow_fresh_literal)
                .map_err(|_| RelationUnavailable::MalformedFunctionType(type_))?;
            return Ok(ResolvedObjectMembers {
                members: None,
                properties: Vec::new(),
                index_infos: Vec::new(),
                property_origin: ObjectPropertyOrigin::Declared,
                call_signature: None,
                exact_callable: true,
            });
        }
        self.resolved_object_members(type_, allow_fresh_literal)
    }

    fn project_non_nullable_callable_signature(
        &mut self,
        type_: TypeId,
    ) -> Result<(Option<ValidatedSingleCallable>, u8), RelationUnavailable> {
        let flags = self.store.type_flags(type_)?;
        if !flags.intersects(TypeFlags::UNION) {
            return Ok((self.project_exact_callable_signature(type_)?, 0));
        }
        let mut nullable_facts = 0u8;
        let mut non_nullable = Vec::new();
        for constituent in self.union_types(type_)? {
            let flags = self.store.type_flags(constituent)?;
            if flags.intersects(TypeFlags::UNDEFINED) {
                nullable_facts |= 1;
            } else if flags.intersects(TypeFlags::NULL) {
                nullable_facts |= 2;
            } else {
                non_nullable.push(constituent);
            }
        }
        let [non_nullable] = non_nullable.as_slice() else {
            return Ok((None, nullable_facts));
        };
        Ok((
            self.project_exact_callable_signature(*non_nullable)?,
            nullable_facts,
        ))
    }

    fn type_contains_void(&mut self, type_: TypeId) -> Result<bool, RelationUnavailable> {
        let flags = self.store.type_flags(type_)?;
        if flags.intersects(TypeFlags::VOID) {
            return Ok(true);
        }
        if !flags.intersects(TypeFlags::UNION) {
            return Ok(false);
        }
        Ok(self.union_types(type_)?.into_iter().any(|constituent| {
            self.store
                .type_payload(constituent)
                .is_some_and(|record| record.flags().intersects(TypeFlags::VOID))
        }))
    }

    fn validated_declared_index_infos(
        &mut self,
        type_id: TypeId,
        owner: Option<SemanticSymbolId>,
        structured: &StructuredTypeData,
    ) -> Result<Vec<IndexInfoId>, RelationUnavailable> {
        let indexes = structured.index_infos.as_deref().unwrap_or_default();
        if indexes.is_empty() {
            return Ok(Vec::new());
        }
        let [index] = indexes else {
            return Err(RelationUnavailable::StructuredIndexInfos(type_id));
        };
        let Some(owner) = owner else {
            return Err(RelationUnavailable::StructuredIndexInfos(type_id));
        };
        let (key_type, value_type, declaration, has_index_symbol, has_components) = {
            let info = self
                .store
                .index_info(*index)
                .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
            let declaration = info
                .declaration()
                .ok_or(RelationUnavailable::StructuredIndexInfos(type_id))?;
            (
                info.key_type(),
                info.value_type(),
                declaration,
                info.index_symbol().is_some(),
                !info.components().is_empty(),
            )
        };
        let (owner_flags, owner_members, owner_declarations) = {
            let owner_record = self
                .store
                .symbol(owner)
                .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
            let Some(declarations) = owner_record
                .declarations()
                .filter(|declarations| !declarations.is_empty())
            else {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            };
            (
                owner_record.flags(),
                owner_record.members(),
                declarations.to_vec(),
            )
        };
        let validated_class = owner_flags == SymbolFlags::CLASS
            && validate_class_heritage_members(self.store, type_id)
                == ClassHeritageMembersValidation::Valid;
        let members = if validated_class {
            owner_members
        } else {
            structured.members
        }
        .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
        self.observe_symbol_table(members);
        let table = self
            .store
            .symbol_table(members)
            .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
        let index_symbol = table
            .get(InternalSymbolName::Index.as_ref())
            .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
        let index_record = self
            .store
            .symbol(index_symbol)
            .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
        let symbol_key = self
            .store
            .intrinsic_bootstrap()
            .ok_or(RelationUnavailable::MissingBootstrap)?
            .es_symbol_type;
        let declaration_parent = self.store.source_node_parent(declaration);
        let supported_key = key_type == self.bootstrap.string_type
            || key_type == self.bootstrap.number_type
            || key_type == symbol_key
            || is_template_pattern_index_key(self.store, key_type);
        if !validated_class
            && owner_flags != SymbolFlags::TYPE_LITERAL
            && owner_flags & SymbolFlags::TYPE != SymbolFlags::INTERFACE
            || owner_members != Some(members)
            || self.store.source_node_kind(declaration) != Some(SyntaxKind::IndexSignature)
            || !owner_declarations.iter().any(|owner_declaration| {
                declaration_parent == Some(SourceNodeParent::Parent(*owner_declaration))
            })
            || !supported_key
            || self.store.type_payload(value_type).is_none()
            || has_index_symbol
            || has_components
            || index_record.flags() != SymbolFlags::SIGNATURE
            || index_record.check_flags() != CheckFlags::NONE
            || index_record.name() != InternalSymbolName::Index.as_ref()
            || index_record
                .declarations()
                .is_none_or(|declarations| !declarations.contains(&declaration))
            || index_record.value_declaration().is_some()
            || index_record.parent() != Some(owner)
            || index_record.members().is_some()
            || index_record.exports().is_some()
            || index_record.export_symbol().is_some()
            || self.store.get_merged_symbol(index_symbol) != Some(index_symbol)
        {
            return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
        }
        Ok(vec![*index])
    }

    fn resolved_object_members(
        &mut self,
        type_id: TypeId,
        allow_fresh_literal: bool,
    ) -> Result<ResolvedObjectMembers, RelationUnavailable> {
        if self
            .store
            .type_flags(type_id)?
            .intersects(TypeFlags::INTERSECTION)
        {
            let projection = self.intersection_projection(type_id)?;
            return Ok(ResolvedObjectMembers {
                members: Some(projection.members),
                properties: projection.properties,
                index_infos: Vec::new(),
                property_origin: ObjectPropertyOrigin::Intersection(type_id),
                call_signature: None,
                exact_callable: false,
            });
        }
        let is_function = self
            .store
            .admit_callable_relation_type(type_id, self.strict_function_types)?;
        self.ensure_supported_object_kind(type_id, allow_fresh_literal)
            .map_err(|error| {
                if is_function {
                    RelationUnavailable::MalformedFunctionType(type_id)
                } else {
                    error
                }
            })?;
        if let Some(call_signature) = self.project_exact_callable_signature(type_id)? {
            let members = self
                .store
                .type_payload(type_id)
                .and_then(|record| record.data().structured())
                .map(|structured| structured.members)
                .ok_or(RelationUnavailable::MalformedFunctionType(type_id))?;
            return Ok(ResolvedObjectMembers {
                members,
                properties: Vec::new(),
                index_infos: Vec::new(),
                property_origin: ObjectPropertyOrigin::Declared,
                call_signature: Some(call_signature),
                exact_callable: true,
            });
        }
        let (record_object_flags, record_symbol, structured, object) = self
            .store
            .type_payload(type_id)
            .map(|record| {
                (
                    record.object_flags(),
                    record.symbol(),
                    record.data().structured().cloned(),
                    match record.data() {
                        TypeData::Object(object) => Some(object.clone()),
                        _ => None,
                    },
                )
            })
            .ok_or(RelationUnavailable::Type(type_id))?;
        let mut property_origin = match self.validate_derived_object_literal(type_id) {
            DerivedObjectLiteralValidation::Valid { owner, .. } => {
                ObjectPropertyOrigin::DerivedObjectLiteral {
                    owner,
                    receiver: type_id,
                }
            }
            DerivedObjectLiteralValidation::Invalid => {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            }
            DerivedObjectLiteralValidation::NotDerived
                if record_object_flags
                    .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL) =>
            {
                ObjectPropertyOrigin::FreshObjectLiteral(
                    record_symbol.ok_or(RelationUnavailable::UnsupportedStructuredType(type_id))?,
                )
            }
            DerivedObjectLiteralValidation::NotDerived
                if record_object_flags.intersects(ObjectFlags::REFERENCE)
                    && !record_object_flags.intersects(ObjectFlags::CLASS)
                    && record_symbol
                        .and_then(|owner| self.store.symbol(owner))
                        .is_some_and(|owner| owner.flags() == SymbolFlags::INTERFACE) =>
            {
                ObjectPropertyOrigin::GenericReference(type_id)
            }
            DerivedObjectLiteralValidation::NotDerived => ObjectPropertyOrigin::Declared,
        };
        if !record_object_flags.intersects(ObjectFlags::MEMBERS_RESOLVED) {
            return Err(RelationUnavailable::UnresolvedStructuredMembers(type_id));
        }
        let structured = structured.ok_or(RelationUnavailable::MalformedStructuredType(type_id))?;
        if structured.call_signature_count != 0
            || structured
                .signatures
                .as_ref()
                .is_some_and(|values| !values.is_empty())
        {
            return Err(RelationUnavailable::StructuredSignatures(type_id));
        }
        let properties = structured.properties.clone().unwrap_or_default();
        let index_infos =
            self.validated_declared_index_infos(type_id, record_symbol, &structured)?;
        let class_members = if property_origin.is_declared() {
            validate_class_heritage_members(self.store, type_id)
        } else {
            ClassHeritageMembersValidation::NotClass
        };
        if class_members == ClassHeritageMembersValidation::Malformed {
            return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
        }
        if class_members == ClassHeritageMembersValidation::Valid {
            property_origin = ObjectPropertyOrigin::ValidatedClass;
        }
        let heritage_members = if property_origin.is_declared()
            && class_members == ClassHeritageMembersValidation::NotClass
        {
            validate_interface_heritage_members(self.store, type_id)
        } else {
            InterfaceHeritageMembersValidation::NotHeritage
        };
        if heritage_members == InterfaceHeritageMembersValidation::Malformed {
            return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
        }
        let mut property_set = HashSet::with_capacity(properties.len());
        let mut property_names = HashMap::with_capacity(properties.len());
        for property in &properties {
            if !property_set.insert(*property) {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            }
            let property_record = self.property_symbol(*property, property_origin)?;
            if property_origin.is_declared()
                && property_record.parent() != record_symbol
                && heritage_members != InterfaceHeritageMembersValidation::Valid
                && class_members != ClassHeritageMembersValidation::Valid
            {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            }
            property_names.insert(*property, property_record.name().to_owned());
        }
        if let ObjectPropertyOrigin::FreshObjectLiteral(owner) = property_origin {
            self.store
                .observe_relation_object_instantiation_map_read(type_id);
            let mut expected_flags = ObjectFlags::ANONYMOUS
                | ObjectFlags::OBJECT_LITERAL
                | ObjectFlags::FRESH_LITERAL
                | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL
                | ObjectFlags::MEMBERS_RESOLVED;
            for property in &properties {
                let property_type = self
                    .store
                    .value_symbol_links(*property)
                    .and_then(|links| links.resolved_type)
                    .ok_or(RelationUnavailable::UnsupportedProperty(*property))?;
                expected_flags |= self
                    .store
                    .type_payload(property_type)
                    .ok_or(RelationUnavailable::Type(property_type))?
                    .object_flags()
                    & ObjectFlags::PROPAGATING_FLAGS;
            }
            if record_object_flags != expected_flags {
                return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
            }
            let Some(object) = object.as_ref() else {
                return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
            };
            if object.target.is_some()
                || object.mapper.is_some()
                || object.instantiations != TypeCacheState::Unallocated
                || object.structured.constrained != ConstrainedTypeData::default()
                || object
                    .structured
                    .object_type_without_abstract_construct_signatures
                    .is_some()
            {
                return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
            }
            let raw_members = self
                .canonical_object_literal_raw_members(owner)
                .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
            let mut raw_targets = HashSet::with_capacity(properties.len());
            for property in &properties {
                let target = self
                    .store
                    .value_symbol_links(*property)
                    .and_then(|links| links.target)
                    .ok_or(RelationUnavailable::UnsupportedProperty(*property))?;
                if !raw_targets.insert(target) {
                    return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                }
            }
            match raw_members {
                CanonicalObjectLiteralRawMembers::Nil if properties.is_empty() => {}
                CanonicalObjectLiteralRawMembers::Allocated(raw_members)
                    if !properties.is_empty() && raw_members.len() == properties.len() =>
                {
                    for (name, target) in raw_members.iter() {
                        let target_record = self
                            .store
                            .symbol(target)
                            .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                        if target_record.name() != name || !raw_targets.contains(&target) {
                            return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                        }
                    }
                }
                CanonicalObjectLiteralRawMembers::Nil
                | CanonicalObjectLiteralRawMembers::Allocated(_) => {
                    return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                }
            }
        }
        match structured.members {
            None if properties.is_empty() && property_origin.is_declared() => {}
            None => return Err(RelationUnavailable::InvalidStructuredMembers(type_id)),
            Some(members) => {
                self.observe_symbol_table(members);
                let table = self
                    .store
                    .symbol_table(members)
                    .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                if table.len() != properties.len() + usize::from(!index_infos.is_empty()) {
                    return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                }
                for (name, property) in table.iter() {
                    if !index_infos.is_empty() && name == InternalSymbolName::Index.as_ref() {
                        continue;
                    }
                    if property_names
                        .get(&property)
                        .is_none_or(|property_name| property_name.as_ref() != name)
                        || !property_set.contains(&property)
                    {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                    }
                }
                for property in &properties {
                    let name = property_names
                        .get(property)
                        .expect("every validated property retained its name");
                    if table.get(name.as_ref()) != Some(*property) {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                    }
                }
            }
        }
        Ok(ResolvedObjectMembers {
            members: structured.members,
            properties,
            index_infos,
            property_origin,
            call_signature: None,
            exact_callable: false,
        })
    }
}

impl Drop for RelaterSession<'_> {
    fn drop(&mut self) {
        self.store
            .discard_relation_read_observation(self.observation);
    }
}

impl SemanticStore<TypeRecord, TypeMapper> {
    fn authenticated_declared_construct_signature(
        &self,
        type_: TypeId,
    ) -> Result<Option<ValidatedSingleCallable>, RelationUnavailable> {
        if !self.type_has_declared_call_set_provenance(type_) {
            return Ok(None);
        }
        let StoredCallableSetValidation::Valid {
            family: CallableFamily::DeclaredCallSignatures,
            projection,
            ..
        } = validate_stored_callable_set(self, type_)
        else {
            return Err(RelationUnavailable::MalformedFunctionType(type_));
        };
        if projection.construct_signatures.is_empty() {
            return Ok(None);
        }
        let [signature] = projection.construct_signatures.as_ref() else {
            return Err(RelationUnavailable::StructuredSignatures(type_));
        };
        if !projection.call_signatures.is_empty() {
            return Err(RelationUnavailable::StructuredSignatures(type_));
        }
        let signature = *signature;
        let record = self
            .signature(signature)
            .ok_or(RelationUnavailable::MalformedFunctionType(type_))?;
        let parameters = self
            .callable_signature_parameter_types(signature)
            .ok_or(RelationUnavailable::MalformedFunctionType(type_))?
            .to_vec();
        let min_argument_count = usize::try_from(record.min_argument_count())
            .map_err(|_| RelationUnavailable::MalformedFunctionType(type_))?;
        let return_type = record
            .resolved_return_type()
            .ok_or(RelationUnavailable::UnresolvedSignatureReturn(signature))?;
        Ok(Some(ValidatedSingleCallable {
            owner: type_,
            signature,
            parameters,
            rest_parameter: None,
            min_argument_count,
            return_type: Some(return_type),
            strict_variance_exempt: false,
        }))
    }

    fn authenticated_declared_construct_pair(
        &self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
        strict_function_types: Option<bool>,
    ) -> Result<Option<(ValidatedSingleCallable, ValidatedSingleCallable)>, RelationUnavailable>
    {
        match (
            self.authenticated_declared_construct_signature(source)?,
            self.authenticated_declared_construct_signature(target)?,
        ) {
            (None, None) => Ok(None),
            (Some(source), Some(target))
                if relation == RelationKind::Assignable && strict_function_types.is_some() =>
            {
                Ok(Some((source, target)))
            }
            (Some(source), _) => Err(RelationUnavailable::StructuredSignatures(source.owner)),
            (None, Some(target)) => Err(RelationUnavailable::StructuredSignatures(target.owner)),
        }
    }

    fn admit_callable_relation_type(
        &self,
        type_: TypeId,
        strict_function_types: Option<bool>,
    ) -> Result<bool, RelationUnavailable> {
        match validate_stored_single_callable(self, type_) {
            StoredSingleCallableValidation::NotCallable => Ok(false),
            StoredSingleCallableValidation::Pending { .. } => {
                Err(if strict_function_types.is_some() {
                    RelationUnavailable::UnresolvedFunctionType(type_)
                } else {
                    RelationUnavailable::StructuredSignatures(type_)
                })
            }
            StoredSingleCallableValidation::Valid { callable, .. } => {
                if strict_function_types.is_some() || callable.strict_variance_exempt {
                    Ok(true)
                } else {
                    Err(RelationUnavailable::StructuredSignatures(type_))
                }
            }
            StoredSingleCallableValidation::Malformed { .. } => {
                Err(RelationUnavailable::MalformedFunctionType(type_))
            }
        }
    }

    /// Looks up one required-or-optional own property without synthesizing an
    /// apparent member, a global `Object` augmentation, or an index result.
    ///
    /// The receiver must already be in the exact declared/fresh/derived
    /// property-only object domain validated by structural relation. A valid
    /// receiver with no such own property returns `None`; unsupported receiver
    /// kinds and malformed warm state retain their typed relation failure.
    pub(super) fn resolved_own_property(
        &mut self,
        type_id: TypeId,
        name: &str,
    ) -> Result<Option<ResolvedOwnProperty>, RelationUnavailable> {
        let bootstrap = self.relation_bootstrap_facts()?;
        let mut session = RelaterSession::new(self, RelationKind::Assignable, bootstrap);
        let resolved = session.resolved_object_members(type_id, true)?;
        if resolved.exact_callable || resolved.call_signature.is_some() {
            return Err(RelationUnavailable::StructuredSignatures(type_id));
        }
        let Some(members) = resolved.members else {
            return Ok(None);
        };
        let property = session
            .store
            .symbol_table(members)
            .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?
            .get_source(name);
        let Some(property) = property else {
            return Ok(None);
        };
        if !resolved.properties.contains(&property) {
            return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
        }
        let (optional, readonly) = {
            let record = session.property_symbol(property, resolved.property_origin)?;
            (
                record.flags().contains(SymbolFlags::OPTIONAL),
                record.check_flags().contains(CheckFlags::READONLY),
            )
        };
        let type_ = session.property_type(property)?;
        Ok(Some(ResolvedOwnProperty {
            symbol: property,
            type_,
            optional,
            readonly,
        }))
    }

    /// Returns the exact ordered property view used when a declared object
    /// supplies context to an object literal.
    ///
    /// Non-object types provide no property context. Object types are accepted
    /// only after the same fail-closed validation used by structural relation;
    /// this function does not compare types or publish relation-cache entries.
    pub(super) fn resolved_declared_property_object(
        &mut self,
        host: &DeclaredTypeHost<'_>,
        type_id: TypeId,
    ) -> Result<Option<ResolvedDeclaredPropertyObject>, RelationUnavailable> {
        let flags = self
            .type_payload(type_id)
            .map(TypeRecord::flags)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if !flags.intersects(TypeFlags::OBJECT) {
            return Ok(None);
        }

        let empty_type_literal = self
            .intrinsic_bootstrap()
            .ok_or(RelationUnavailable::MissingBootstrap)?
            .empty_type_literal_type;
        let plan = if type_id == empty_type_literal {
            None
        } else {
            let record = self
                .type_payload(type_id)
                .ok_or(RelationUnavailable::Type(type_id))?;
            let plan = match record.data() {
                TypeData::Interface(_) => {
                    let owner = record
                        .symbol()
                        .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                    let plan = super::object_members::plan_interface(self, host, owner)
                        .map_err(|_| RelationUnavailable::InvalidStructuredMembers(type_id))?;
                    if plan.heritage.is_some() {
                        if !validate_planned_interface_heritage_members(self, &plan, type_id) {
                            return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                        }
                    } else {
                        let state = super::object_members::interface_state(self, &plan, type_id)
                            .map_err(|_| RelationUnavailable::InvalidStructuredMembers(type_id))?;
                        if !matches!(
                            state,
                            super::object_members::PropertyObjectState::Resolved(resolved)
                                if resolved == type_id
                        ) {
                            return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                        }
                    }
                    plan
                }
                TypeData::Object(_) => {
                    let owner = record
                        .symbol()
                        .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                    let owner_declaration = self
                        .symbol(owner)
                        .and_then(|owner| match owner.declarations() {
                            Some([declaration]) => Some(*declaration),
                            _ => None,
                        })
                        .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                    let alias_symbol = match record.alias() {
                        Some(alias_id) => {
                            let alias = self
                                .type_alias(alias_id)
                                .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                            let alias_symbol = alias
                                .symbol()
                                .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                            let alias_record = self
                                .symbol(alias_symbol)
                                .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                            let alias_declaration = match alias_record.declarations() {
                                Some([declaration]) => *declaration,
                                _ => {
                                    return Err(RelationUnavailable::InvalidStructuredMembers(
                                        type_id,
                                    ));
                                }
                            };
                            let alias_declaration_record = host
                                .node(alias_declaration)
                                .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                            let NodeData::TypeAliasDeclaration(type_alias) =
                                &alias_declaration_record.data
                            else {
                                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                            };
                            let alias_name = NodeRef::new(
                                alias_declaration.arena,
                                alias_declaration.file,
                                type_alias.name,
                            );
                            if alias.type_arguments().is_some()
                                || self.get_merged_symbol(alias_symbol) != Some(alias_symbol)
                                || alias_record.flags() != SymbolFlags::TYPE_ALIAS
                                || alias_record.check_flags() != CheckFlags::NONE
                                || alias_record.value_declaration().is_some()
                                || alias_record.exports().is_some()
                                || alias_record.export_symbol().is_some()
                                || self.source_node_kind(alias_declaration)
                                    != Some(SyntaxKind::TypeAliasDeclaration)
                                || alias_declaration_record.flags.0 != 0
                                || type_alias.flow_node.is_some()
                                || type_alias.local_symbol.is_some()
                                || type_alias.symbol.is_some()
                                || type_alias.type_parameters.is_some()
                                || !host.symbol_matches(self, alias_declaration, alias_symbol)
                                || self.type_alias_links(alias_symbol).is_none_or(|links| {
                                    links.declared_type != Some(type_id)
                                        || links.type_parameters.is_some()
                                        || links.instantiations.is_some()
                                        || links.is_constructor_declared_property
                                })
                                || super::object_members::declared_type_declaration_parent(
                                    self,
                                    host,
                                    alias_declaration,
                                    alias_symbol,
                                    alias_name,
                                    type_alias.modifiers.as_ref(),
                                ) != Ok(alias_record.parent())
                            {
                                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                            }
                            Some(alias_symbol)
                        }
                        None => None,
                    };
                    let plan = super::object_members::plan_type_literal(
                        self,
                        host,
                        owner_declaration,
                        alias_symbol,
                    )
                    .map_err(|_| RelationUnavailable::InvalidStructuredMembers(type_id))?;
                    let state = super::object_members::type_literal_state(self, &plan)
                        .map_err(|_| RelationUnavailable::InvalidStructuredMembers(type_id))?
                        .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                    if !matches!(
                        state,
                        super::object_members::PropertyObjectState::Resolved(resolved)
                            if resolved == type_id
                    ) {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                    }
                    plan
                }
                _ => return Err(RelationUnavailable::UnsupportedStructuredType(type_id)),
            };
            let property_types = plan
                .properties
                .iter()
                .map(|property| {
                    self.value_symbol_links(property.symbol)
                        .and_then(|links| links.resolved_type)
                        .ok_or(RelationUnavailable::UnsupportedProperty(property.symbol))
                })
                .collect::<Result<Vec<_>, _>>()?;
            super::object_members::validate_resolved_property_types(self, &plan, &property_types)
                .map_err(|_| RelationUnavailable::InvalidStructuredMembers(type_id))?;
            Some((plan, property_types))
        };

        let bootstrap = self.relation_bootstrap_facts()?;
        let mut session = RelaterSession::new(self, RelationKind::Assignable, bootstrap);
        let resolved = session.resolved_object_members(type_id, false)?;
        if let Some((plan, property_types)) = plan {
            if plan.heritage.is_some() {
                if !resolved.property_origin.is_declared()
                    || resolved.call_signature.is_some()
                    || resolved.exact_callable
                {
                    return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                }
                let mut properties = Vec::with_capacity(resolved.properties.len());
                let mut by_name = HashMap::with_capacity(resolved.properties.len());
                for property in resolved.properties {
                    let record = session.property_symbol(property, resolved.property_origin)?;
                    let Some([declaration]) = record.declarations() else {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                    };
                    let name = record.name().to_owned();
                    let optional = record.flags().contains(SymbolFlags::OPTIONAL);
                    let declaration = *declaration;
                    let type_ = session.property_type(property)?;
                    let index = properties.len();
                    if by_name.insert(name.clone(), index).is_some() {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                    }
                    properties.push(ResolvedDeclaredProperty {
                        symbol: property,
                        name,
                        type_,
                        optional,
                        declaration,
                    });
                }
                return Ok(Some(ResolvedDeclaredPropertyObject {
                    properties,
                    by_name,
                }));
            }
            if resolved.members != plan.members
                || !resolved.property_origin.is_declared()
                || resolved.properties
                    != plan
                        .properties
                        .iter()
                        .map(|property| property.symbol)
                        .collect::<Vec<_>>()
            {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            }
            let mut properties = Vec::with_capacity(plan.properties.len());
            let mut by_name = HashMap::with_capacity(plan.properties.len());
            for (property, property_type) in plan.properties.into_iter().zip(property_types) {
                let name = EscapedName::source(&property.name);
                let index = properties.len();
                if by_name.insert(name.clone(), index).is_some() {
                    return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                }
                properties.push(ResolvedDeclaredProperty {
                    symbol: property.symbol,
                    name,
                    type_: property_type,
                    optional: property.optional,
                    declaration: property.declaration,
                });
            }
            return Ok(Some(ResolvedDeclaredPropertyObject {
                properties,
                by_name,
            }));
        }

        if !resolved.properties.is_empty()
            || resolved.members.is_some()
            || !resolved.property_origin.is_declared()
        {
            return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
        }
        Ok(Some(ResolvedDeclaredPropertyObject {
            properties: Vec::new(),
            by_name: HashMap::new(),
        }))
    }

    /// Validates every canonical-Array/property-object pair in one expression
    /// union before subtype reduction can publish any directional cache entry.
    ///
    /// The current mixed relation domain contains only empty property objects;
    /// malformed canonical arrays retain their typed invariant error, while a
    /// nonempty property surface remains an unsupported union constituent.
    pub(super) fn preflight_expression_union_array_object_pairs(
        &mut self,
        types: &[TypeId],
        global_types: &CanonicalGlobalTypes,
    ) -> Result<(), LiteralTypeCacheError> {
        let bootstrap = self
            .relation_bootstrap_facts()
            .map_err(|_| LiteralTypeCacheError::BootstrapUninitialized)?;
        let mut session = RelaterSession::new_with_global_types(
            self,
            RelationKind::StrictSubtype,
            bootstrap,
            Some(RelationGlobalTypes::from_global_types(global_types)),
        );
        session.preflight_expression_union_array_object_pairs(types)
    }

    /// Pinned `isTypeIdenticalTo` for the dependency-closed relation domain.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_identical_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::Identity)
    }

    /// Global-aware [`Self::is_type_identical_to`] for canonical `Array` and
    /// `ReadonlyArray` references.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record,
    /// global target, or unported relation capability is unavailable.
    pub fn is_type_identical_to_with_global_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_global_types(
            source,
            target,
            RelationKind::Identity,
            global_types,
        )
    }

    /// Pinned `compareTypesIdentical` for the dependency-closed relation domain.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn compare_types_identical(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Ternary, RelationUnavailable> {
        self.is_type_identical_to(source, target)
            .map(bool_to_ternary)
    }

    /// Pinned `compareTypesAssignableSimple`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn compare_types_assignable_simple(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Ternary, RelationUnavailable> {
        self.is_type_assignable_to(source, target)
            .map(bool_to_ternary)
    }

    /// Pinned `compareTypesAssignableWorker`.
    ///
    /// The pinned worker ignores `reportErrors` and delegates to the same
    /// no-diagnostic entry point, so this dependency-closed port does too.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn compare_types_assignable_worker(
        &mut self,
        source: TypeId,
        target: TypeId,
        _report_errors: bool,
    ) -> Result<Ternary, RelationUnavailable> {
        self.is_type_assignable_to(source, target)
            .map(bool_to_ternary)
    }

    /// Pinned `compareTypesSubtypeOf`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn compare_types_subtype_of(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Ternary, RelationUnavailable> {
        self.is_type_subtype_of(source, target).map(bool_to_ternary)
    }

    /// Pinned `isTypeAssignableTo`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_assignable_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::Assignable)
    }

    /// Global-aware [`Self::is_type_assignable_to`] for canonical `Array` and
    /// `ReadonlyArray` references.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record,
    /// global target, or unported relation capability is unavailable.
    pub fn is_type_assignable_to_with_global_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_global_types(
            source,
            target,
            RelationKind::Assignable,
            global_types,
        )
    }

    /// Option-aware assignability for exact stored callable types.
    ///
    /// `strictFunctionTypes` is checker-context state in the pinned checker.
    /// Because relation keys omit compiler options, the first option-aware
    /// query immutably claims that state for this store and every later query
    /// must supply the same retained value.
    #[cfg(test)]
    pub(super) fn is_type_assignable_to_with_strict_function_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        strict_function_types: bool,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_optional_global_types_and_options(
            source,
            target,
            RelationKind::Assignable,
            None,
            Some(strict_function_types),
        )
    }

    /// Global-aware option-aware assignability for exact stored callables.
    #[allow(dead_code)] // Called by the context wrapper installed with this relation slice.
    pub(super) fn is_type_assignable_to_with_global_types_and_strict_function_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        global_types: &CanonicalGlobalTypes,
        strict_function_types: bool,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_optional_global_types_and_options(
            source,
            target,
            RelationKind::Assignable,
            Some(RelationGlobalTypes::from_global_types(global_types)),
            Some(strict_function_types),
        )
    }

    /// Pinned `isTypeSubtypeOf`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_subtype_of(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::Subtype)
    }

    /// Global-aware [`Self::is_type_subtype_of`] for canonical `Array` and
    /// `ReadonlyArray` references.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record,
    /// global target, or unported relation capability is unavailable.
    pub fn is_type_subtype_of_with_global_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_global_types(
            source,
            target,
            RelationKind::Subtype,
            global_types,
        )
    }

    /// Global-aware, option-aware subtype comparison for overload selection.
    pub(super) fn is_type_subtype_of_with_global_types_and_strict_function_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        global_types: &CanonicalGlobalTypes,
        strict_function_types: bool,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_optional_global_types_and_options(
            source,
            target,
            RelationKind::Subtype,
            Some(RelationGlobalTypes::from_global_types(global_types)),
            Some(strict_function_types),
        )
    }

    /// Pinned `isTypeStrictSubtypeOf`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_strict_subtype_of(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::StrictSubtype)
    }

    /// Global-aware [`Self::is_type_strict_subtype_of`] for canonical `Array`
    /// and `ReadonlyArray` references.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record,
    /// global target, or unported relation capability is unavailable.
    pub fn is_type_strict_subtype_of_with_global_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_global_types(
            source,
            target,
            RelationKind::StrictSubtype,
            global_types,
        )
    }

    /// Pinned `isTypeComparableTo`.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_comparable_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to(source, target, RelationKind::Comparable)
    }

    /// Global-aware [`Self::is_type_comparable_to`] for canonical `Array` and
    /// `ReadonlyArray` references.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record,
    /// global target, or unported relation capability is unavailable.
    pub fn is_type_comparable_to_with_global_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_global_types(
            source,
            target,
            RelationKind::Comparable,
            global_types,
        )
    }

    /// Pinned `areTypesComparable`, including directional short-circuiting.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn are_types_comparable(
        &mut self,
        left: TypeId,
        right: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        if self.is_type_comparable_to(left, right)? {
            return Ok(true);
        }
        self.is_type_comparable_to(right, left)
    }

    /// Global-aware [`Self::are_types_comparable`] for canonical `Array` and
    /// `ReadonlyArray` references.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record,
    /// global target, or unported relation capability is unavailable.
    pub fn are_types_comparable_with_global_types(
        &mut self,
        left: TypeId,
        right: TypeId,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<bool, RelationUnavailable> {
        if self.is_type_comparable_to_with_global_types(left, right, global_types)? {
            return Ok(true);
        }
        self.is_type_comparable_to_with_global_types(right, left, global_types)
    }

    /// Pinned `isTypeRelatedTo` through its exact simple and cache-read paths.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record or
    /// unported relation capability is unavailable.
    pub fn is_type_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_optional_global_types(source, target, relation, None)
    }

    /// Option-aware relation entry point for exact stored callable types.
    #[cfg(test)]
    pub(super) fn is_type_related_to_with_strict_function_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
        strict_function_types: bool,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_optional_global_types_and_options(
            source,
            target,
            relation,
            None,
            Some(strict_function_types),
        )
    }

    /// Pinned `isTypeRelatedTo` with authoritative standard-library identities
    /// for relation families that require them.
    ///
    /// # Errors
    ///
    /// Returns [`RelationUnavailable`] when a required canonical record,
    /// global target, or unported relation capability is unavailable.
    pub fn is_type_related_to_with_global_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_optional_global_types(
            source,
            target,
            relation,
            Some(RelationGlobalTypes::from_global_types(global_types)),
        )
    }

    fn is_type_related_to_with_optional_global_types(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
        global_types: Option<RelationGlobalTypes>,
    ) -> Result<bool, RelationUnavailable> {
        self.is_type_related_to_with_optional_global_types_and_options(
            source,
            target,
            relation,
            global_types,
            None,
        )
    }

    fn is_type_related_to_with_optional_global_types_and_options(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
        global_types: Option<RelationGlobalTypes>,
        strict_function_types: Option<bool>,
    ) -> Result<bool, RelationUnavailable> {
        if let Some(requested) = strict_function_types
            && let Err(established) = self.claim_strict_function_types(requested)
        {
            return Err(RelationUnavailable::StrictFunctionTypesOptionMismatch {
                established,
                requested,
            });
        }
        let bootstrap = self.relation_bootstrap_facts()?;
        let original_source = source;
        let original_target = target;
        let source = self.regular_type_if_fresh(source)?;
        let source = if self.type_flags(source)?.intersects(TypeFlags::INTERSECTION) {
            let projection = self
                .validate_intersection_type(source)
                .map_err(|_| RelationUnavailable::MalformedIntersection(source))?;
            if projection.reduced_to_never {
                bootstrap.never_type
            } else {
                source
            }
        } else {
            source
        };
        let target = self.regular_type_if_fresh(target)?;
        let target = if self.type_flags(target)?.intersects(TypeFlags::INTERSECTION) {
            let projection = self
                .validate_intersection_type(target)
                .map_err(|_| RelationUnavailable::MalformedIntersection(target))?;
            if projection.reduced_to_never {
                bootstrap.never_type
            } else {
                target
            }
        } else {
            target
        };
        validate_direct_interface_heritage_relation_endpoint(self, source)?;
        validate_class_members_relation_endpoint(self, source)?;
        if target != source {
            validate_direct_interface_heritage_relation_endpoint(self, target)?;
            validate_class_members_relation_endpoint(self, target)?;
        }
        self.admit_callable_relation_type(source, strict_function_types)?;
        if target != source {
            self.admit_callable_relation_type(target, strict_function_types)?;
        }
        if source == target {
            return Ok(true);
        }

        let source_flags = self.type_flags(source)?;
        let target_flags = self.type_flags(target)?;
        if source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::PRIMITIVE)
        {
            let related = (relation == RelationKind::Comparable
                && !target_flags.intersects(TypeFlags::NEVER)
                && self.is_simple_type_related_to(target, source, relation, bootstrap)?)
                || self.is_simple_type_related_to(source, target, relation, bootstrap)?;
            return Ok(related);
        }
        if !relation.is_identity() {
            if let Some(related) =
                self.authenticated_template_literal_relation(source, target, relation)?
            {
                return Ok(related);
            }
            if (relation == RelationKind::Comparable
                && !target_flags.intersects(TypeFlags::NEVER)
                && self.is_simple_type_related_to(target, source, relation, bootstrap)?)
                || self.is_simple_type_related_to(source, target, relation, bootstrap)?
            {
                return Ok(true);
            }
        } else if !(source_flags | target_flags).intersects(
            TypeFlags::UNION_OR_INTERSECTION
                | TypeFlags::INDEXED_ACCESS
                | TypeFlags::CONDITIONAL
                | TypeFlags::SUBSTITUTION,
        ) {
            if source_flags != target_flags {
                return Ok(false);
            }
            if source_flags.intersects(TypeFlags::SINGLETON) {
                return Ok(true);
            }
        }

        if source_flags.intersects(TypeFlags::OBJECT) && target_flags.intersects(TypeFlags::OBJECT)
        {
            self.authenticated_declared_construct_pair(
                source,
                target,
                relation,
                strict_function_types,
            )?;
        }

        let supported_array_relation = source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::OBJECT)
            && configured_array_reference_targets(self, global_types, source, target)?.is_some();
        let supported_apparent_primitive_relation = relation != RelationKind::Identity
            && target_flags.intersects(TypeFlags::OBJECT)
            && global_types
                .and_then(|global_types| global_types.apparent_primitive_type(source_flags))
                .is_some();
        if source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::OBJECT)
            && !supported_array_relation
            && (strict_function_types.is_some() || self.claimed_strict_function_types().is_none())
        {
            let key = self
                .relation_key_if_available(
                    source,
                    target,
                    IntersectionState::NONE,
                    relation.is_identity(),
                    false,
                )
                .map_err(relation_key_unavailable)?;
            let related = self.relation_cache_get(relation, key.key());
            if !related.is_empty() {
                return Ok(related.intersects(RelationComparisonResult::SUCCEEDED));
            }
        }

        if source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
            || target_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
        {
            let union_relation = source_flags.intersects(TypeFlags::UNION_OR_INTERSECTION)
                || target_flags.intersects(TypeFlags::UNION_OR_INTERSECTION);
            let supported_object_relation =
                supports_structured_object_relation(relation, strict_function_types)
                    && source_flags.intersects(TypeFlags::OBJECT)
                    && target_flags.intersects(TypeFlags::OBJECT);
            if union_relation
                || supported_object_relation
                || supported_array_relation
                || supported_apparent_primitive_relation
            {
                let mut session = RelaterSession::new_with_global_types_and_options(
                    self,
                    relation,
                    bootstrap,
                    global_types,
                    strict_function_types,
                );
                session.observe_type_surface(original_source);
                session.observe_type_surface(original_target);
                let result = session.is_related_to_ex(
                    source,
                    target,
                    RecursionFlags::BOTH,
                    IntersectionState::NONE,
                )?;
                return if supported_array_relation || supported_apparent_primitive_relation {
                    Ok(session.finish_without_specialized_root_cache(result))
                } else {
                    session.finish(source, target, result)
                };
            }
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation,
            });
        }
        Ok(false)
    }

    fn authenticated_template_literal_relation(
        &self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
    ) -> Result<Option<bool>, RelationUnavailable> {
        if relation.is_identity() {
            return Ok(None);
        }
        let source_flags = self.type_flags(source)?;
        let target_flags = self.type_flags(target)?;
        let (source, target) = if target_flags.intersects(TypeFlags::TEMPLATE_LITERAL)
            && source_flags.intersects(TypeFlags::STRING_LITERAL | TypeFlags::TEMPLATE_LITERAL)
        {
            (source, target)
        } else if relation == RelationKind::Comparable
            && source_flags.intersects(TypeFlags::TEMPLATE_LITERAL)
            && target_flags.intersects(TypeFlags::STRING_LITERAL)
        {
            (target, source)
        } else {
            return Ok(None);
        };

        self.authenticate_template_literal_type(target)?;
        let source_record = self
            .type_payload(source)
            .ok_or(RelationUnavailable::Type(source))?;
        if source_record.flags().intersects(TypeFlags::STRING_LITERAL) {
            if source_record.flags().intersects(TypeFlags::ENUM_LITERAL) {
                if enums::canonical_enum_type_owner(self, source).is_none() {
                    return Err(RelationUnavailable::MalformedLiteral(source));
                }
            } else {
                self.validate_union_constituent(source)
                    .map_err(|error| union_validation_unavailable(source, error))?;
            }
        } else {
            self.authenticate_template_literal_type(source)?;
        }

        self.is_type_matched_by_template_literal_type(source, target)
            .map(Some)
            .map_err(|_| RelationUnavailable::MalformedStructuredType(target))
    }

    fn authenticate_template_literal_type(&self, type_: TypeId) -> Result<(), RelationUnavailable> {
        let record = self
            .type_payload(type_)
            .ok_or(RelationUnavailable::Type(type_))?;
        let TypeData::TemplateLiteral(template) = record.data() else {
            return Err(RelationUnavailable::MalformedStructuredType(type_));
        };
        if record.flags() != TypeFlags::TEMPLATE_LITERAL
            || self
                .cached_resolved_template_literal_type(&template.texts, &template.types)
                .map_err(|_| RelationUnavailable::MalformedStructuredType(type_))?
                != Some(type_)
            || !self
                .is_type_matched_by_template_literal_type(type_, type_)
                .map_err(|_| RelationUnavailable::MalformedStructuredType(type_))?
        {
            return Err(RelationUnavailable::MalformedStructuredType(type_));
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)] // Keep the pinned branch order visibly linear.
    fn is_simple_type_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
    ) -> Result<bool, RelationUnavailable> {
        let source_flags = self.type_flags(source)?;
        let target_flags = self.type_flags(target)?;
        if target_flags.intersects(TypeFlags::ANY)
            || source_flags.intersects(TypeFlags::NEVER)
            || source == bootstrap.wildcard_type
        {
            return Ok(true);
        }
        if target_flags.intersects(TypeFlags::UNKNOWN)
            && !(relation == RelationKind::StrictSubtype && source_flags.intersects(TypeFlags::ANY))
        {
            return Ok(true);
        }
        if target_flags.intersects(TypeFlags::NEVER) {
            return Ok(false);
        }
        if source_flags.intersects(TypeFlags::STRING_LIKE)
            && target_flags.intersects(TypeFlags::STRING)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::STRING_LITERAL)
            && source_flags.intersects(TypeFlags::ENUM_LITERAL)
            && target_flags.intersects(TypeFlags::STRING_LITERAL)
            && !target_flags.intersects(TypeFlags::ENUM_LITERAL)
            && self.literal_values_equal(source, target)?
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::NUMBER_LIKE)
            && target_flags.intersects(TypeFlags::NUMBER)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::NUMBER_LITERAL)
            && source_flags.intersects(TypeFlags::ENUM_LITERAL)
            && target_flags.intersects(TypeFlags::NUMBER_LITERAL)
            && !target_flags.intersects(TypeFlags::ENUM_LITERAL)
            && self.literal_values_equal(source, target)?
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::BIG_INT_LIKE)
            && target_flags.intersects(TypeFlags::BIG_INT)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::BOOLEAN_LIKE)
            && target_flags.intersects(TypeFlags::BOOLEAN)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::ES_SYMBOL_LIKE)
            && target_flags.intersects(TypeFlags::ES_SYMBOL)
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::ENUM) && target_flags.intersects(TypeFlags::ENUM) {
            let source_symbol = self.enum_symbol(source)?;
            let target_symbol = self.enum_symbol(target)?;
            let names_equal =
                self.symbol_name(source_symbol)? == self.symbol_name(target_symbol)?;
            if names_equal && self.enum_types_related_if_available(source_symbol, target_symbol)? {
                return Ok(true);
            }
        }
        if source_flags.intersects(TypeFlags::ENUM_LITERAL)
            && target_flags.intersects(TypeFlags::ENUM_LITERAL)
        {
            if source_flags.intersects(TypeFlags::UNION)
                && target_flags.intersects(TypeFlags::UNION)
            {
                let source_symbol = self.enum_symbol(source)?;
                let target_symbol = self.enum_symbol(target)?;
                if self.enum_types_related_if_available(source_symbol, target_symbol)? {
                    return Ok(true);
                }
            }
            if source_flags.intersects(TypeFlags::LITERAL)
                && target_flags.intersects(TypeFlags::LITERAL)
                && self.literal_values_equal(source, target)?
            {
                let source_symbol = self.enum_symbol(source)?;
                let target_symbol = self.enum_symbol(target)?;
                if self.enum_types_related_if_available(source_symbol, target_symbol)? {
                    return Ok(true);
                }
            }
        }
        if source_flags.intersects(TypeFlags::UNDEFINED)
            && ((!bootstrap.strict_null_checks
                && !target_flags.intersects(TypeFlags::UNION_OR_INTERSECTION))
                || target_flags.intersects(TypeFlags::UNDEFINED | TypeFlags::VOID))
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::NULL)
            && ((!bootstrap.strict_null_checks
                && !target_flags.intersects(TypeFlags::UNION_OR_INTERSECTION))
                || target_flags.intersects(TypeFlags::NULL))
        {
            return Ok(true);
        }
        if source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::NON_PRIMITIVE)
        {
            let rejected_empty_strict_subtype = relation == RelationKind::StrictSubtype
                && self.is_empty_anonymous_object_type(source, bootstrap.any_function_type)?
                && !self
                    .type_payload(source)
                    .ok_or(RelationUnavailable::Type(source))?
                    .object_flags()
                    .intersects(ObjectFlags::FRESH_LITERAL);
            if !rejected_empty_strict_subtype {
                return Ok(true);
            }
        }
        if relation == RelationKind::Assignable || relation == RelationKind::Comparable {
            if source_flags.intersects(TypeFlags::ANY) {
                return Ok(true);
            }
            if source_flags.intersects(TypeFlags::NUMBER)
                && (target_flags.intersects(TypeFlags::ENUM)
                    || target_flags.intersects(TypeFlags::NUMBER_LITERAL)
                        && target_flags.intersects(TypeFlags::ENUM_LITERAL))
            {
                return Ok(true);
            }
            if source_flags.intersects(TypeFlags::NUMBER_LITERAL)
                && !source_flags.intersects(TypeFlags::ENUM_LITERAL)
                && (target_flags.intersects(TypeFlags::ENUM)
                    || target_flags.intersects(TypeFlags::NUMBER_LITERAL)
                        && target_flags.intersects(TypeFlags::ENUM_LITERAL)
                        && self.literal_values_equal(source, target)?)
            {
                return Ok(true);
            }
            if self.is_unknown_like_union_type(target, bootstrap)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn relation_bootstrap_facts(&self) -> Result<RelationBootstrapFacts, RelationUnavailable> {
        let bootstrap = self
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(RelationUnavailable::MissingBootstrap)?;
        Ok(RelationBootstrapFacts {
            strict_null_checks: bootstrap.options.strict_null_checks,
            exact_optional_property_types: bootstrap.options.exact_optional_property_types,
            any_type: bootstrap.any_type,
            void_type: bootstrap.void_type,
            wildcard_type: bootstrap.wildcard_type,
            any_function_type: bootstrap.any_function_type,
            never_type: bootstrap.never_type,
            undefined_type: bootstrap.undefined_type,
            missing_type: bootstrap.missing_type,
            string_type: bootstrap.string_type,
            number_type: bootstrap.number_type,
            bigint_type: bootstrap.bigint_type,
        })
    }

    #[cfg(test)]
    fn is_type_assignable_to_with_test_limits(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation_count: isize,
        stack_depth_limit: usize,
    ) -> Result<bool, RelationUnavailable> {
        let bootstrap = self.relation_bootstrap_facts()?;
        let mut session = RelaterSession::new_with_limits(
            self,
            RelationKind::Assignable,
            bootstrap,
            relation_count,
            stack_depth_limit,
        );
        let result = session.is_related_to_ex(
            source,
            target,
            RecursionFlags::BOTH,
            IntersectionState::NONE,
        )?;
        session.finish(source, target, result)
    }

    fn type_flags(&self, type_id: TypeId) -> Result<TypeFlags, RelationUnavailable> {
        self.type_payload(type_id)
            .map(TypeRecord::flags)
            .ok_or(RelationUnavailable::Type(type_id))
    }

    fn regular_type_if_fresh(&self, type_id: TypeId) -> Result<TypeId, RelationUnavailable> {
        let record = self
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if !record.flags().intersects(TypeFlags::FRESHABLE) {
            return Ok(type_id);
        }
        let TypeData::Literal(literal) = record.data() else {
            return Err(RelationUnavailable::MalformedLiteral(type_id));
        };
        if literal.fresh_type != Some(type_id) {
            return Ok(type_id);
        }
        let regular = self
            .type_payload(literal.regular_type)
            .ok_or(RelationUnavailable::Type(literal.regular_type))?;
        let TypeData::Literal(regular_literal) = regular.data() else {
            return Err(RelationUnavailable::MalformedLiteral(literal.regular_type));
        };
        if regular.flags() != record.flags()
            || regular_literal.regular_type != literal.regular_type
            || regular_literal.fresh_type != Some(type_id)
            || regular_literal.value != literal.value
        {
            return Err(RelationUnavailable::MalformedLiteral(type_id));
        }
        Ok(literal.regular_type)
    }

    fn literal_values_equal(
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let source = self
            .type_payload(source)
            .ok_or(RelationUnavailable::Type(source))?;
        let target = self
            .type_payload(target)
            .ok_or(RelationUnavailable::Type(target))?;
        let TypeData::Literal(source) = source.data() else {
            return Err(RelationUnavailable::MalformedLiteral(source.id()));
        };
        let TypeData::Literal(target) = target.data() else {
            return Err(RelationUnavailable::MalformedLiteral(target.id()));
        };
        Ok(source.value == target.value)
    }

    fn enum_symbol(&self, type_id: TypeId) -> Result<SemanticSymbolId, RelationUnavailable> {
        self.type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?
            .symbol()
            .ok_or(RelationUnavailable::MalformedEnumType(type_id))
    }

    fn symbol_name(&self, symbol: SemanticSymbolId) -> Result<&[u8], RelationUnavailable> {
        self.symbol(symbol)
            .map(|symbol| symbol.name().as_bytes())
            .ok_or(RelationUnavailable::Symbol(symbol))
    }

    fn enum_types_related_if_available(
        &mut self,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    ) -> Result<bool, RelationUnavailable> {
        let source = self.enum_parent_or_self(source)?;
        let target = self.enum_parent_or_self(target)?;
        if source == target {
            return Ok(true);
        }
        let source_symbol = self
            .symbol(source)
            .ok_or(RelationUnavailable::Symbol(source))?;
        let target_symbol = self
            .symbol(target)
            .ok_or(RelationUnavailable::Symbol(target))?;
        if source_symbol.name() != target_symbol.name()
            || !source_symbol.flags().intersects(SymbolFlags::REGULAR_ENUM)
            || !target_symbol.flags().intersects(SymbolFlags::REGULAR_ENUM)
        {
            return Ok(false);
        }
        let cached = self
            .enum_relation_cache_get(source, target)
            .ok_or(RelationUnavailable::Symbol(source))?;
        if cached.is_empty() {
            return Err(RelationUnavailable::EnumRelation { source, target });
        }
        Ok(cached.intersects(RelationComparisonResult::SUCCEEDED))
    }

    fn enum_parent_or_self(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, RelationUnavailable> {
        let record = self
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?;
        if record.flags().intersects(SymbolFlags::ENUM_MEMBER) {
            return self
                .get_parent_of_symbol(symbol)
                .ok_or(RelationUnavailable::Symbol(symbol));
        }
        Ok(symbol)
    }

    fn is_empty_anonymous_object_type(
        &self,
        type_id: TypeId,
        any_function_type: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let record = self
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if !record.object_flags().intersects(ObjectFlags::ANONYMOUS) {
            return Ok(false);
        }
        if record
            .object_flags()
            .intersects(ObjectFlags::MEMBERS_RESOLVED)
        {
            let structured = record
                .data()
                .structured()
                .ok_or(RelationUnavailable::MalformedStructuredType(type_id))?;
            let is_empty_resolved = type_id != any_function_type
                && structured.properties.as_ref().is_none_or(Vec::is_empty)
                && structured.signatures.as_ref().is_none_or(Vec::is_empty)
                && structured.index_infos.as_ref().is_none_or(Vec::is_empty);
            if is_empty_resolved {
                return Ok(true);
            }
        }
        let Some(symbol) = record.symbol() else {
            return Ok(false);
        };
        let symbol_record = self
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?;
        if !symbol_record.flags().intersects(SymbolFlags::TYPE_LITERAL) {
            return Ok(false);
        }
        if symbol_record
            .flags()
            .intersects(SymbolFlags::LATE_BINDING_CONTAINER)
        {
            let members = self
                .members_and_exports_links(symbol)
                .and_then(|links| links.table(MembersOrExportsResolutionKind::ResolvedMembers))
                .ok_or(RelationUnavailable::LateBoundMembers(symbol))?;
            return self
                .symbol_table(members)
                .map(ts_binder::semantic::SymbolTable::is_empty)
                .ok_or(RelationUnavailable::InvalidSymbolMembers(symbol));
        }
        match symbol_record.members() {
            None => Ok(true),
            Some(members) => self
                .symbol_table(members)
                .map(ts_binder::semantic::SymbolTable::is_empty)
                .ok_or(RelationUnavailable::InvalidSymbolMembers(symbol)),
        }
    }

    fn is_unknown_like_union_type(
        &mut self,
        type_id: TypeId,
        bootstrap: RelationBootstrapFacts,
    ) -> Result<bool, RelationUnavailable> {
        let record = self
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if !bootstrap.strict_null_checks
            || !record.flags().intersects(TypeFlags::UNION)
            || record.flags().intersects(TypeFlags::ENUM_LITERAL)
        {
            return Ok(false);
        }
        if record
            .object_flags()
            .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED)
        {
            return Ok(record
                .object_flags()
                .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION));
        }
        let TypeData::Union(union) = record.data() else {
            return Err(RelationUnavailable::MalformedStructuredType(type_id));
        };
        let types = union.union.types.clone();
        let is_unknown_like = if types.len() >= 3
            && self.type_flags(types[0])?.intersects(TypeFlags::UNDEFINED)
            && self.type_flags(types[1])?.intersects(TypeFlags::NULL)
        {
            let mut found_empty = false;
            for constituent in &types {
                if self.is_empty_anonymous_object_type(*constituent, bootstrap.any_function_type)? {
                    found_empty = true;
                    break;
                }
            }
            found_empty
        } else {
            false
        };
        let cache_flags = ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED
            | if is_unknown_like {
                ObjectFlags::IS_UNKNOWN_LIKE_UNION
            } else {
                ObjectFlags::NONE
            };
        if !self.add_type_object_flags(type_id, cache_flags) {
            return Err(RelationUnavailable::InvalidUnknownLikeUnionState(type_id));
        }
        Ok(is_unknown_like)
    }
}

fn configured_array_reference_targets(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    global_types: Option<RelationGlobalTypes>,
    source: TypeId,
    target: TypeId,
) -> Result<Option<(TypeId, TypeId)>, RelationUnavailable> {
    let Some(global_types) = global_types else {
        return Ok(None);
    };
    let source_record = store
        .type_payload(source)
        .ok_or(RelationUnavailable::Type(source))?;
    let target_record = store
        .type_payload(target)
        .ok_or(RelationUnavailable::Type(target))?;
    let (TypeData::TypeReference(source_reference), TypeData::TypeReference(target_reference)) =
        (source_record.data(), target_record.data())
    else {
        return Ok(None);
    };
    let Some(source_target) = source_reference.object.target else {
        return Ok(None);
    };
    let Some(target_target) = target_reference.object.target else {
        return Ok(None);
    };
    Ok((global_types.contains_array_target(source_target)
        && global_types.contains_array_target(target_target))
    .then_some((source_target, target_target)))
}

const fn array_relation_preflight_error(
    type_: TypeId,
    error: RelationUnavailable,
) -> LiteralTypeCacheError {
    match error {
        RelationUnavailable::CanonicalGlobalType(error) => LiteralTypeCacheError::ArrayType {
            type_,
            error: ArrayTypeError::GlobalType(error),
        },
        RelationUnavailable::MalformedCanonicalArrayReference(malformed) => {
            LiteralTypeCacheError::ArrayType {
                type_: malformed,
                error: ArrayTypeError::InvalidReference(malformed),
            }
        }
        RelationUnavailable::UnavailableCanonicalArrayTarget(_) | RelationUnavailable::Type(_) => {
            LiteralTypeCacheError::ArrayType {
                type_,
                error: ArrayTypeError::InvalidReference(type_),
            }
        }
        _ => LiteralTypeCacheError::UnsupportedUnionConstituent(type_),
    }
}

const fn array_surface_preflight_error(
    type_: TypeId,
    error: RelationUnavailable,
) -> LiteralTypeCacheError {
    match error {
        RelationUnavailable::Type(_)
        | RelationUnavailable::Symbol(_)
        | RelationUnavailable::InvalidSymbolMembers(_)
        | RelationUnavailable::InvalidStructuredMembers(_) => LiteralTypeCacheError::ArrayType {
            type_,
            error: ArrayTypeError::InvalidReference(type_),
        },
        _ => LiteralTypeCacheError::UnsupportedUnionConstituent(type_),
    }
}

const fn object_surface_preflight_error(
    type_: TypeId,
    error: RelationUnavailable,
) -> LiteralTypeCacheError {
    match error {
        RelationUnavailable::Type(_)
        | RelationUnavailable::Symbol(_)
        | RelationUnavailable::MalformedStructuredType(_)
        | RelationUnavailable::InvalidSymbolMembers(_)
        | RelationUnavailable::InvalidStructuredMembers(_) => {
            LiteralTypeCacheError::InvalidCachedUnion(type_)
        }
        _ => LiteralTypeCacheError::UnsupportedUnionConstituent(type_),
    }
}

const fn bool_to_ternary(value: bool) -> Ternary {
    if value { Ternary::True } else { Ternary::False }
}

const fn supports_property_object_relation(relation: RelationKind) -> bool {
    matches!(
        relation,
        RelationKind::Assignable
            | RelationKind::Subtype
            | RelationKind::StrictSubtype
            | RelationKind::Comparable
    )
}

const fn supports_structured_object_relation(
    relation: RelationKind,
    _strict_function_types: Option<bool>,
) -> bool {
    supports_property_object_relation(relation) || relation.is_identity()
}

pub(super) const fn union_validation_unavailable(
    union: TypeId,
    error: LiteralTypeCacheError,
) -> RelationUnavailable {
    match error {
        LiteralTypeCacheError::BootstrapUninitialized => RelationUnavailable::MissingBootstrap,
        LiteralTypeCacheError::InvalidValue | LiteralTypeCacheError::InvalidCachedUnion(_) => {
            RelationUnavailable::MalformedUnion(union)
        }
        LiteralTypeCacheError::InvalidCachedLiteral(type_id) => {
            RelationUnavailable::MalformedLiteral(type_id)
        }
        LiteralTypeCacheError::UnsupportedUnionConstituent(type_id) => {
            RelationUnavailable::UnsupportedUnionConstituent(type_id)
        }
        LiteralTypeCacheError::ArrayType { error, .. } => match error {
            ArrayTypeError::GlobalType(error) => RelationUnavailable::CanonicalGlobalType(error),
            ArrayTypeError::InvalidReference(type_id)
            | ArrayTypeError::InvalidArrayLiteralCache {
                cached: type_id, ..
            } => RelationUnavailable::MalformedCanonicalArrayReference(type_id),
            ArrayTypeError::UnsupportedCreationFlags(_) => {
                RelationUnavailable::InvalidUnionPreparation(union)
            }
            ArrayTypeError::Capacity(_) => RelationUnavailable::UnionValidationCapacity(union),
        },
        LiteralTypeCacheError::InvalidUnionAlias(symbol) => {
            RelationUnavailable::InvalidUnionAlias(symbol)
        }
        LiteralTypeCacheError::InvalidPreparedQuery => {
            RelationUnavailable::InvalidUnionPreparation(union)
        }
        LiteralTypeCacheError::Capacity => RelationUnavailable::UnionValidationCapacity(union),
    }
}

const fn relation_key_unavailable(error: RelationKeyUnavailable) -> RelationUnavailable {
    match error {
        RelationKeyUnavailable::Type(type_id) => RelationUnavailable::RelationKeyType(type_id),
        RelationKeyUnavailable::TypeReferenceArguments(type_id) => {
            RelationUnavailable::RelationKeyTypeReferenceArguments(type_id)
        }
        RelationKeyUnavailable::TypeReferenceTarget(type_id) => {
            RelationUnavailable::RelationKeyTypeReferenceTarget(type_id)
        }
        RelationKeyUnavailable::TypeParameterConstraint(type_id) => {
            RelationUnavailable::RelationKeyTypeParameterConstraint(type_id)
        }
        RelationKeyUnavailable::CyclicGenericArguments(type_id) => {
            RelationUnavailable::RelationKeyCyclicGenericArguments(type_id)
        }
    }
}

const fn recursion_identity_unavailable(
    error: RecursionIdentityUnavailable,
) -> RelationUnavailable {
    match error {
        RecursionIdentityUnavailable::Type(type_id)
        | RecursionIdentityUnavailable::TypeReferenceTarget(type_id)
        | RecursionIdentityUnavailable::ConditionalRoot(type_id) => {
            RelationUnavailable::UnsupportedStructuredType(type_id)
        }
        RecursionIdentityUnavailable::Symbol(symbol) => RelationUnavailable::Symbol(symbol),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeArena, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        AstScope, BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, CheckFlags, EscapedName,
        InternalSymbolName, SemanticSymbolId, SymbolData, SymbolFlags,
    };
    use ts_jsnum::{Number, PseudoBigInt};
    use ts_parser::{ParseResult, parse_source_file};

    use super::{
        ArrayTypeError, LiteralTypeCacheError, RelationGlobalTypes, RelationUnavailable,
        ResolvedOwnProperty,
    };
    use crate::semantic::{
        CanonicalCheckerDiagnostics, CanonicalGlobalTypeInitializationError,
        CanonicalTypeMapperStore, DeclaredTypeHost, DeclaredTypeLinks, IntrinsicBootstrapOptions,
        MembersAndExportsLinks, MembersOrExportsResolutionKind, RelationComparisonResult,
        RelationKind, SignatureId, SignatureLinks, TypeAliasLinks, TypeId, TypeNodeLinks,
        ValueSymbolLinks,
        array_types::CanonicalArrayTargets,
        classes::{
            ClassMembers, execute_nongeneric_class_member_query, plan_nongeneric_class_member_query,
        },
        declared::type_list_key,
        global_types::create_type_from_generic_global_type,
        production::GlobalMergeCompletion,
        signatures::{SignatureFlags, Ternary},
        type_nodes::{CanonicalTypeQuery, CanonicalTypeQueryOptions},
        type_records::{LiteralValue, RegularLiteralLink, TypeData, TypeRecord},
        types::{ObjectFlags, TypeFlags},
    };

    type TestStore = CanonicalTypeMapperStore;

    fn initialized(strict_null_checks: bool) -> TestStore {
        initialized_with_options(strict_null_checks, false)
    }

    fn initialized_with_options(
        strict_null_checks: bool,
        exact_optional_property_types: bool,
    ) -> TestStore {
        let mut store = TestStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks,
                exact_optional_property_types,
            })
            .unwrap();
        store
    }

    struct FunctionRelationFixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: TestStore,
    }

    fn function_relation_fixture(source: &str) -> FunctionRelationFixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(97);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/signature-relations.ts\""),
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
        let mut store = TestStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            })
            .unwrap();
        let bound = files.get(&file).unwrap();
        let locals = bound.locals(bound.source_file()).unwrap();
        let mut symbols = store
            .symbol_table(locals)
            .unwrap()
            .iter()
            .map(|(name, symbol)| (name.as_bytes().to_vec(), symbol))
            .collect::<Vec<_>>();
        symbols.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        for (_, symbol) in symbols {
            store.merge_global_symbol(globals, symbol).unwrap();
        }
        FunctionRelationFixture {
            parsed,
            file,
            files,
            store,
        }
    }

    fn relation_host<'a>(arena: &'a NodeArena, bound: &'a BoundFile) -> DeclaredTypeHost<'a> {
        DeclaredTypeHost::new_after_global_merge(
            [(arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap()
    }

    fn alias_function_node(fixture: &FunctionRelationFixture, name: &str) -> NodeRef {
        fixture
            .parsed
            .arena
            .iter()
            .find_map(|(_node, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &fixture
                    .parsed
                    .arena
                    .get(alias.name)
                    .expect("alias name belongs to the arena")
                    .data
                else {
                    return None;
                };
                (record.kind == SyntaxKind::TypeAliasDeclaration && identifier.text == name)
                    .then(|| NodeRef::new(fixture.parsed.arena.id(), fixture.file, alias.type_))
            })
            .unwrap_or_else(|| panic!("missing function alias {name}"))
    }

    fn query_function_alias(
        fixture: &mut FunctionRelationFixture,
        name: &str,
    ) -> (TypeId, SignatureId) {
        let node = alias_function_node(fixture, name);
        assert_eq!(
            fixture.parsed.arena.get(node.node).unwrap().kind,
            SyntaxKind::FunctionType
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = {
            let host = relation_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(node)
            .unwrap()
        };
        assert!(diagnostics.is_empty());
        let signature = fixture
            .store
            .signature_links(node)
            .and_then(|links| links.resolved_signature.signature())
            .expect("the function type has a resolved signature");
        (type_, signature)
    }

    fn query_type_alias(fixture: &mut FunctionRelationFixture, name: &str) -> TypeId {
        let node = alias_function_node(fixture, name);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = {
            let host = relation_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(node)
            .unwrap()
        };
        assert!(diagnostics.is_empty());
        type_
    }

    fn query_class_members(fixture: &mut FunctionRelationFixture, name: &str) -> ClassMembers {
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let symbol = fixture
            .store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source(name))
            .unwrap_or_else(|| panic!("missing class {name}"));
        let host = relation_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let plan = plan_nongeneric_class_member_query(&fixture.store, &host, symbol).unwrap();
        execute_nongeneric_class_member_query(&mut fixture.store, &host, &plan).unwrap()
    }

    fn query_declared_interface(fixture: &mut FunctionRelationFixture, name: &str) -> TypeId {
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let symbol = fixture
            .store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source(name))
            .unwrap_or_else(|| panic!("missing interface {name}"));
        let host = relation_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap()
    }

    fn query_declared_relation_alias(fixture: &mut FunctionRelationFixture, name: &str) -> TypeId {
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let symbol = fixture
            .store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source(name))
            .unwrap_or_else(|| panic!("missing declared alias {name}"));
        let host = relation_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(symbol)
        .unwrap();
        assert!(diagnostics.is_empty());
        type_
    }

    fn resolve_all_function_returns(fixture: &mut FunctionRelationFixture) {
        let signatures = fixture
            .parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::FunctionType)
            .map(|(node, _)| NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            .filter_map(|node| {
                fixture
                    .store
                    .signature_links(node)
                    .and_then(|links| links.resolved_signature.signature())
            })
            .collect::<Vec<_>>();
        for signature in signatures {
            resolve_function_return(fixture, signature);
        }
    }

    fn resolve_function_return(fixture: &mut FunctionRelationFixture, signature: SignatureId) {
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let host = relation_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_return_type_of_signature(signature)
        .unwrap();
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn validated_class_methods_compare_structurally_without_function_variance_options() {
        let mut fixture = function_relation_fixture(concat!(
            "class Left { run(): void {} } ",
            "class Right { run(): void {} } ",
            "class UndefinedReturn { run(): undefined {} } ",
            "class DynamicReturn { run(): any {} }",
        ));
        let left = query_class_members(&mut fixture, "Left")
            .shells()
            .instance_type();
        let right = query_class_members(&mut fixture, "Right")
            .shells()
            .instance_type();
        let undefined = query_class_members(&mut fixture, "UndefinedReturn")
            .shells()
            .instance_type();
        let dynamic = query_class_members(&mut fixture, "DynamicReturn")
            .shells()
            .instance_type();

        assert_eq!(fixture.store.is_type_assignable_to(left, right), Ok(true));
        assert_eq!(fixture.store.is_type_identical_to(left, right), Ok(true));
        assert_eq!(
            fixture.store.is_type_assignable_to(undefined, left),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(left, undefined),
            Ok(false)
        );
        assert_eq!(
            fixture.store.is_type_identical_to(left, undefined),
            Ok(false)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(dynamic, undefined),
            Ok(true)
        );
    }

    #[test]
    fn only_variance_exempt_callables_are_admitted_without_function_variance_options() {
        let mut fixture = function_relation_fixture(concat!(
            "class Method { run(): void {} } ",
            "type Callback = () => void;",
        ));
        let method = query_class_members(&mut fixture, "Method");
        let method_type = fixture
            .store
            .value_symbol_links(method.instance_properties()[0])
            .and_then(|links| links.resolved_type)
            .unwrap();
        let (callback, signature) = query_function_alias(&mut fixture, "Callback");
        resolve_function_return(&mut fixture, signature);

        assert_eq!(
            fixture
                .store
                .admit_callable_relation_type(method_type, None),
            Ok(true)
        );
        assert_eq!(
            fixture.store.admit_callable_relation_type(callback, None),
            Err(RelationUnavailable::StructuredSignatures(callback))
        );
    }

    #[test]
    fn inherited_and_static_class_methods_retain_callable_relation_semantics() {
        let mut fixture = function_relation_fixture(concat!(
            "class Base { run(): void {} static shared(): void {} } ",
            "class Derived extends Base { own(): void {} } ",
            "class Shape { run(): void {} } ",
            "class StaticShape { static shared(): undefined {} }",
        ));
        let derived = query_class_members(&mut fixture, "Derived");
        let base = query_class_members(&mut fixture, "Base");
        let shape = query_class_members(&mut fixture, "Shape");
        let static_shape = query_class_members(&mut fixture, "StaticShape");

        assert_eq!(
            derived.instance_properties()[1],
            base.instance_properties()[0]
        );
        assert_eq!(derived.static_properties()[0], base.static_properties()[0]);
        assert_eq!(
            fixture.store.is_type_assignable_to(
                derived.shells().instance_type(),
                shape.shells().instance_type(),
            ),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(
                shape.shells().instance_type(),
                derived.shells().instance_type(),
            ),
            Ok(false)
        );

        let inherited_static = fixture
            .store
            .value_symbol_links(derived.static_properties()[0])
            .and_then(|links| links.resolved_type)
            .unwrap();
        let undefined_static = fixture
            .store
            .value_symbol_links(static_shape.static_properties()[0])
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to(inherited_static, undefined_static),
            Ok(false)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to(undefined_static, inherited_static),
            Ok(true)
        );
    }

    #[test]
    fn class_method_values_compare_with_branded_zero_argument_callbacks() {
        let mut fixture = function_relation_fixture(concat!(
            "class Method { run(): void {} } ",
            "type Callback = () => void;",
        ));
        let method = query_class_members(&mut fixture, "Method");
        let method_type = fixture
            .store
            .value_symbol_links(method.instance_properties()[0])
            .and_then(|links| links.resolved_type)
            .unwrap();
        let (callback, signature) = query_function_alias(&mut fixture, "Callback");
        resolve_function_return(&mut fixture, signature);

        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(method_type, callback, true),
            Ok(true)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(callback, method_type, true),
            Ok(true)
        );
    }

    #[test]
    fn poisoned_class_method_signatures_invalidate_warmed_structural_relations() {
        let mut fixture = function_relation_fixture(concat!(
            "class Source { run(): void {} } ",
            "class Target { run(): void {} }",
        ));
        let source = query_class_members(&mut fixture, "Source");
        let target = query_class_members(&mut fixture, "Target");
        let source_type = source.shells().instance_type();
        let target_type = target.shells().instance_type();
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to(source_type, target_type),
            Ok(true)
        );
        let root_key = fixture
            .store
            .relation_key_if_available(
                source_type,
                target_type,
                super::IntersectionState::NONE,
                false,
                false,
            )
            .unwrap()
            .key();
        assert!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );

        let method_type = fixture
            .store
            .value_symbol_links(target.instance_properties()[0])
            .and_then(|links| links.resolved_type)
            .unwrap();
        let signature = fixture
            .store
            .type_payload(method_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .and_then(|signatures| signatures.first().copied())
            .unwrap();
        let invalid = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(
            fixture
                .store
                .set_signature_resolved_return_type(signature, Some(invalid))
        );
        assert_eq!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE
        );
        let stale = fixture.store.relation_state_snapshot();
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to(source_type, target_type),
            Err(RelationUnavailable::InvalidStructuredMembers(target_type))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), stale);
    }

    #[test]
    fn validated_class_string_indexes_compare_with_maps_and_fresh_objects() {
        let mut fixture = function_relation_fixture(concat!(
            "class Indexed { [name: string]: number; constructor() {} } ",
            "type Numbers = { [name: string]: number }; ",
            "type Strings = { [name: string]: string }; ",
            "type Actions = { [name: `do-${string}`]: number };",
        ));
        let indexed = query_class_members(&mut fixture, "Indexed")
            .shells()
            .instance_type();
        let numbers = query_declared_relation_alias(&mut fixture, "Numbers");
        let strings = query_declared_relation_alias(&mut fixture, "Strings");
        let actions = query_declared_relation_alias(&mut fixture, "Actions");
        let (number, string) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let matching = alloc_typed_property(&mut fixture.store, "value", number, false);
        let valid = alloc_fresh_property_object(&mut fixture.store, vec![matching]);
        let mismatching = alloc_typed_property(&mut fixture.store, "value", string, false);
        let invalid = alloc_fresh_property_object(&mut fixture.store, vec![mismatching]);

        assert_eq!(
            fixture.store.is_type_assignable_to(indexed, numbers),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(numbers, indexed),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(indexed, actions),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(indexed, strings),
            Ok(false)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(valid, indexed),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(invalid, indexed),
            Ok(false)
        );
    }

    #[test]
    fn poisoned_indexed_class_graph_is_rejected_before_warmed_relation_cache() {
        let mut fixture = function_relation_fixture(concat!(
            "class Indexed { [name: string]: number; constructor() {} } ",
            "type Numbers = { [name: string]: number };",
        ));
        let class = query_class_members(&mut fixture, "Indexed");
        let indexed = class.shells().instance_type();
        let numbers = query_declared_relation_alias(&mut fixture, "Numbers");
        assert_eq!(
            fixture.store.is_type_assignable_to(indexed, numbers),
            Ok(true)
        );
        let key = fixture
            .store
            .relation_key_if_available(
                indexed,
                numbers,
                super::IntersectionState::NONE,
                false,
                false,
            )
            .unwrap()
            .key();
        assert!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, key)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );

        let index = fixture
            .store
            .type_payload(indexed)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .and_then(|indexes| indexes.first().copied())
            .unwrap();
        let index_symbol = fixture
            .store
            .symbol(class.shells().symbol())
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
            .unwrap();
        assert!(
            fixture
                .store
                .set_index_info_symbol(index, Some(index_symbol))
        );
        let poisoned = fixture.store.relation_state_snapshot();

        assert_eq!(
            fixture.store.is_type_assignable_to(indexed, numbers),
            Err(RelationUnavailable::InvalidStructuredMembers(indexed))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), poisoned);
    }

    #[test]
    fn authenticated_declared_construct_signatures_follow_callable_assignability() {
        let mut fixture = function_relation_fixture(concat!(
            "type Narrow = { new(value: \"fixed\"): string }; ",
            "type Wide = { new(value: string): string }; ",
            "type LiteralReturn = { new(value: string): \"fixed\" }; ",
            "type NumericReturn = { new(value: string): number }; ",
            "type Zero = { new(): string }; ",
            "interface InterfaceWide { new(value: string): string; }",
        ));
        let narrow = query_declared_relation_alias(&mut fixture, "Narrow");
        let wide = query_declared_relation_alias(&mut fixture, "Wide");
        let literal_return = query_declared_relation_alias(&mut fixture, "LiteralReturn");
        let numeric_return = query_declared_relation_alias(&mut fixture, "NumericReturn");
        let zero = query_declared_relation_alias(&mut fixture, "Zero");
        let interface_wide = query_declared_relation_alias(&mut fixture, "InterfaceWide");

        for (source, target, expected) in [
            (wide, narrow, true),
            (narrow, wide, false),
            (literal_return, wide, true),
            (wide, literal_return, false),
            (numeric_return, wide, false),
            (wide, zero, false),
            (zero, wide, true),
            (wide, interface_wide, true),
            (interface_wide, wide, true),
        ] {
            assert_eq!(
                fixture
                    .store
                    .is_type_assignable_to_with_strict_function_types(source, target, true),
                Ok(expected)
            );
        }

        let mut bivariant = function_relation_fixture(concat!(
            "type Narrow = { new(value: \"fixed\"): string }; ",
            "type Wide = { new(value: string): string };",
        ));
        let narrow = query_declared_relation_alias(&mut bivariant, "Narrow");
        let wide = query_declared_relation_alias(&mut bivariant, "Wide");
        assert_eq!(
            bivariant
                .store
                .is_type_assignable_to_with_strict_function_types(narrow, wide, false),
            Ok(true)
        );
    }

    #[test]
    fn declared_construct_relation_boundaries_do_not_publish_partial_results() {
        let mut fixture = function_relation_fixture(concat!(
            "type Left = { new(value: string): string }; ",
            "type Right = { new(value: string): string }; ",
            "type Overloaded = { new(value: string): string; new(value: number): number }; ",
            "type Callable = { (value: string): string };",
        ));
        let left = query_declared_relation_alias(&mut fixture, "Left");
        let right = query_declared_relation_alias(&mut fixture, "Right");
        let overloaded = query_declared_relation_alias(&mut fixture, "Overloaded");
        let callable = query_declared_relation_alias(&mut fixture, "Callable");
        let before = fixture.store.relation_state_snapshot();

        assert_eq!(
            fixture.store.is_type_assignable_to(left, right),
            Err(RelationUnavailable::StructuredSignatures(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
        assert_eq!(
            fixture.store.is_type_related_to_with_strict_function_types(
                left,
                right,
                RelationKind::Subtype,
                true,
            ),
            Err(RelationUnavailable::StructuredSignatures(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(overloaded, right, true),
            Err(RelationUnavailable::StructuredSignatures(overloaded))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(left, callable, true),
            Err(RelationUnavailable::StructuredSignatures(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
    }

    #[test]
    fn poisoned_declared_construct_signature_invalidates_a_warmed_relation() {
        let mut fixture = function_relation_fixture(concat!(
            "type Left = { new(value: string): string }; ",
            "type Right = { new(value: string): string };",
        ));
        let left = query_declared_relation_alias(&mut fixture, "Left");
        let right = query_declared_relation_alias(&mut fixture, "Right");
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(left, right, true),
            Ok(true)
        );
        let key = fixture
            .store
            .relation_key_if_available(left, right, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, key)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );

        let signature = fixture
            .store
            .type_payload(left)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .and_then(|signatures| signatures.first().copied())
            .unwrap();
        assert!(
            fixture
                .store
                .set_signature_flags(signature, SignatureFlags::NONE)
        );
        assert_eq!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, key),
            RelationComparisonResult::NONE
        );
        let poisoned = fixture.store.relation_state_snapshot();

        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(left, right, true),
            Err(RelationUnavailable::MalformedFunctionType(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), poisoned);
    }

    #[test]
    fn exact_function_aliases_compare_identically_after_lazy_returns_resolve() {
        let mut fixture = function_relation_fixture(
            r"
                type Left = (value: string) => number;
                type Right = (value: string) => number;
                type Optional = (value?: string) => number;
            ",
        );
        let (left, _) = query_function_alias(&mut fixture, "Left");
        let (right, _) = query_function_alias(&mut fixture, "Right");
        let (optional, _) = query_function_alias(&mut fixture, "Optional");
        resolve_all_function_returns(&mut fixture);

        assert_eq!(
            fixture.store.is_type_related_to_with_strict_function_types(
                left,
                right,
                RelationKind::Identity,
                true,
            ),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_related_to_with_strict_function_types(
                left,
                optional,
                RelationKind::Identity,
                true,
            ),
            Ok(false)
        );
    }

    #[test]
    fn strict_function_option_is_explicit_and_changes_parameter_variance() {
        fn relation(strict_function_types: bool) -> bool {
            let mut fixture = function_relation_fixture(
                r#"
                    type Narrow = (value: "fixed") => void;
                    type Wide = (value: string) => void;
                "#,
            );
            let (narrow, _) = query_function_alias(&mut fixture, "Narrow");
            let (wide, _) = query_function_alias(&mut fixture, "Wide");
            resolve_all_function_returns(&mut fixture);
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(
                    narrow,
                    wide,
                    strict_function_types,
                )
                .unwrap()
        }

        assert!(!relation(true));
        assert!(relation(false));

        let mut fixture =
            function_relation_fixture("type Left = () => void; type Right = () => void;");
        let (left, _) = query_function_alias(&mut fixture, "Left");
        let (right, _) = query_function_alias(&mut fixture, "Right");
        resolve_all_function_returns(&mut fixture);
        assert_eq!(
            fixture.store.is_type_assignable_to(left, right),
            Err(RelationUnavailable::StructuredSignatures(left)),
            "store-only callers must opt into immutable checker option state"
        );
    }

    #[test]
    fn strict_function_option_claim_precedes_callable_cache_access() {
        let mut fixture =
            function_relation_fixture("type Left = () => void; type Right = () => void;");
        let (left, _) = query_function_alias(&mut fixture, "Left");
        let (right, _) = query_function_alias(&mut fixture, "Right");
        resolve_all_function_returns(&mut fixture);
        let left_property = alloc_typed_property(&mut fixture.store, "callback", left, false);
        let left_wrapper = alloc_property_object(&mut fixture.store, vec![left_property]);
        let right_property = alloc_typed_property(&mut fixture.store, "callback", right, false);
        let right_wrapper = alloc_property_object(&mut fixture.store, vec![right_property]);

        assert_eq!(fixture.store.claimed_strict_function_types(), None);
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(
                    left_wrapper,
                    right_wrapper,
                    true,
                ),
            Ok(true)
        );
        assert_eq!(fixture.store.claimed_strict_function_types(), Some(true));
        let cached = fixture.store.relation_state_snapshot();

        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(
                    left_wrapper,
                    right_wrapper,
                    false,
                ),
            Err(RelationUnavailable::StrictFunctionTypesOptionMismatch {
                established: true,
                requested: false,
            })
        );
        assert_eq!(fixture.store.relation_state_snapshot(), cached);
        assert_eq!(fixture.store.claimed_strict_function_types(), Some(true));

        assert_eq!(
            fixture
                .store
                .is_type_assignable_to(left_wrapper, right_wrapper),
            Err(RelationUnavailable::StructuredSignatures(left)),
            "a legacy query cannot consume a wrapper cache whose nested relation was callable"
        );
        assert_eq!(fixture.store.relation_state_snapshot(), cached);
        assert_eq!(
            fixture.store.is_type_assignable_to(left, right),
            Err(RelationUnavailable::StructuredSignatures(left)),
            "a legacy query cannot consume the option-aware callable cache"
        );
        assert_eq!(fixture.store.relation_state_snapshot(), cached);
    }

    #[test]
    fn warmed_wrapper_relation_revalidates_nested_callable_links() {
        let mut fixture =
            function_relation_fixture("type Left = () => string; type Right = () => string;");
        let left_node = alias_function_node(&fixture, "Left");
        let (left, left_signature) = query_function_alias(&mut fixture, "Left");
        let (right, _) = query_function_alias(&mut fixture, "Right");
        resolve_all_function_returns(&mut fixture);
        let left_property = alloc_typed_property(&mut fixture.store, "callback", left, false);
        let source = alloc_property_object(&mut fixture.store, vec![left_property]);
        let right_property = alloc_typed_property(&mut fixture.store, "callback", right, false);
        let target = alloc_property_object(&mut fixture.store, vec![right_property]);
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Ok(true)
        );
        let root_key = fixture
            .store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );

        let exact_signature_links = fixture.store.signature_links(left_node).unwrap().clone();
        assert!(
            fixture
                .store
                .set_signature_links(left_node, exact_signature_links.clone())
        );
        let warmed = fixture.store.relation_state_snapshot();
        assert!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key)
                .intersects(RelationComparisonResult::SUCCEEDED),
            "an equal signature-link publication must preserve the root cache"
        );
        assert!(
            fixture
                .store
                .set_signature_links(left_node, SignatureLinks::default())
        );
        assert_eq!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE,
        );
        assert!(matches!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Err(RelationUnavailable::UnresolvedFunctionType(type_)
                | RelationUnavailable::MalformedFunctionType(type_))
                if type_ == left
        ));
        assert_eq!(fixture.store.relation_state_snapshot(), warmed);

        assert!(
            fixture
                .store
                .set_signature_links(left_node, exact_signature_links)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Ok(true)
        );
        let rewarmed = fixture.store.relation_state_snapshot();
        let exact_type_node_links = fixture.store.type_node_links(left_node).unwrap().clone();
        assert!(
            fixture
                .store
                .set_type_node_links(left_node, exact_type_node_links.clone())
        );
        assert_eq!(fixture.store.relation_state_snapshot(), rewarmed);
        assert!(
            fixture
                .store
                .set_type_node_links(left_node, TypeNodeLinks::default())
        );
        assert_eq!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE,
        );
        assert!(matches!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Err(RelationUnavailable::UnresolvedFunctionType(type_)
                | RelationUnavailable::MalformedFunctionType(type_))
                if type_ == left
        ));
        assert_eq!(fixture.store.relation_state_snapshot(), rewarmed);

        assert!(
            fixture
                .store
                .set_type_node_links(left_node, exact_type_node_links)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Ok(true)
        );
        let arity_warmed = fixture.store.relation_state_snapshot();
        assert_eq!(
            fixture
                .store
                .signature(left_signature)
                .unwrap()
                .resolved_min_argument_count(),
            -1
        );
        assert!(
            fixture
                .store
                .set_signature_resolved_min_argument_count(left_signature, 0)
        );
        assert_eq!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE,
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Err(RelationUnavailable::MalformedFunctionType(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), arity_warmed);

        assert!(
            fixture
                .store
                .set_signature_resolved_min_argument_count(left_signature, -1)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Ok(true)
        );
        let isolated_warmed = fixture.store.relation_state_snapshot();
        assert!(
            fixture
                .store
                .set_signature_isolated_type(left_signature, Some(right))
        );
        assert_eq!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE,
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Err(RelationUnavailable::MalformedFunctionType(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), isolated_warmed);

        assert!(
            fixture
                .store
                .set_signature_isolated_type(left_signature, None)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Ok(true)
        );
        let payload_warmed = fixture.store.relation_state_snapshot();
        assert!(
            fixture
                .store
                .set_resolved_base_constraint(left, Some(right))
        );
        assert_eq!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE,
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Err(RelationUnavailable::MalformedFunctionType(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), payload_warmed);

        assert!(fixture.store.set_resolved_base_constraint(left, None));
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Ok(true)
        );
        let merge_warmed = fixture.store.relation_state_snapshot();
        let left_owner = fixture.store.type_payload(left).unwrap().symbol().unwrap();
        let right_owner = fixture.store.type_payload(right).unwrap().symbol().unwrap();
        assert_eq!(
            fixture.store.record_merged_symbol(right_owner, left_owner),
            Ok(None)
        );
        assert_eq!(
            fixture
                .store
                .relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE,
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(source, target, true),
            Err(RelationUnavailable::MalformedFunctionType(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), merge_warmed);
    }

    #[test]
    fn warmed_relation_revalidates_first_type_symbol_and_alias_publication() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source_property = alloc_typed_property(&mut store, "value", string, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let target_property = alloc_typed_property(&mut store, "value", string, false);
        let target = alloc_property_object(&mut store, vec![target_property]);
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        let root_key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        let symbol_warmed = store.relation_state_snapshot();
        let owner = alloc_symbol(&mut store, SymbolFlags::TYPE_LITERAL, "owner");
        assert!(store.set_type_symbol(source, Some(owner)));
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE
        );
        assert_eq!(
            store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::InvalidStructuredMembers(source))
        );
        assert_eq!(store.relation_state_snapshot(), symbol_warmed);

        assert!(store.set_type_symbol(source, None));
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        let alias_warmed = store.relation_state_snapshot();
        let alias = store.alloc_type_alias(None).unwrap();
        assert!(store.set_type_alias(source, Some(alias)));
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE
        );
        assert_eq!(
            store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnsupportedStructuredType(source))
        );
        assert_eq!(store.relation_state_snapshot(), alias_warmed);
    }

    #[test]
    fn warmed_relation_revalidates_first_synthetic_property_flag_change() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source_property = alloc_typed_property(&mut store, "value", string, true);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let target_property = alloc_typed_property(&mut store, "value", string, true);
        let target = alloc_property_object(&mut store, vec![target_property]);
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        let root_key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert!(store.set_symbol_flags(
            target_property,
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL,
            CheckFlags::NONE,
        ));
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, root_key)
                .intersects(RelationComparisonResult::SUCCEEDED),
            "an equal observed-symbol write preserves the warmed relation"
        );
        assert!(store.set_symbol_flags(target_property, SymbolFlags::PROPERTY, CheckFlags::NONE,));
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE
        );
        assert_eq!(store.is_type_assignable_to(source, target), Ok(false));
    }

    #[test]
    fn warmed_wrapper_relation_revalidates_literal_and_union_cache_links() {
        let mut store = initialized(true);
        let (regular_false, fresh_false, string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.regular_false_type,
                bootstrap.false_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let source_property = alloc_typed_property(&mut store, "value", fresh_false, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let target_property = alloc_typed_property(&mut store, "value", regular_false, false);
        let target = alloc_property_object(&mut store, vec![target_property]);
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        let literal_key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        let literal_warmed = store.relation_state_snapshot();
        assert!(store.set_literal_links(regular_false, None, regular_false));
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, literal_key),
            RelationComparisonResult::NONE
        );
        assert!(matches!(
            store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::MalformedLiteral(type_))
                if type_ == fresh_false || type_ == regular_false
        ));
        assert_eq!(store.relation_state_snapshot(), literal_warmed);

        assert!(store.set_literal_links(regular_false, Some(fresh_false), regular_false));
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        let union = canonical_union(&mut store, &[string, number]);
        let union_source_property = alloc_typed_property(&mut store, "value", union, false);
        let union_source = alloc_property_object(&mut store, vec![union_source_property]);
        let union_target_property = alloc_typed_property(&mut store, "value", union, false);
        let union_target = alloc_property_object(&mut store, vec![union_target_property]);
        assert_eq!(
            store.is_type_assignable_to(union_source, union_target),
            Ok(true)
        );
        let union_key = store
            .relation_key_if_available(
                union_source,
                union_target,
                super::IntersectionState::NONE,
                false,
                false,
            )
            .unwrap()
            .key();
        let (reduced, regular, key_property_name, constituent_map) = {
            let TypeData::Union(data) = store.type_payload(union).unwrap().data() else {
                panic!("canonical union must retain union data");
            };
            (
                data.resolved_reduced_type,
                data.regular_type,
                data.key_property_name.clone(),
                data.constituent_map.clone(),
            )
        };
        assert!(store.set_union_caches(
            union,
            reduced,
            regular,
            Some(string),
            key_property_name,
            constituent_map,
        ));
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, union_key),
            RelationComparisonResult::NONE
        );
    }

    #[test]
    fn generic_interface_relations_revalidate_proxy_mappers_and_cached_types() {
        let mut fixture =
            function_relation_fixture("interface Box<T> { value: T; readonly label: string }");
        let owner = {
            let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
            fixture
                .store
                .symbol_table(globals)
                .unwrap()
                .get_source("Box")
                .unwrap()
        };
        let target = {
            let host = relation_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(owner)
            .unwrap()
        };
        let (parameter, string, number) = {
            let TypeData::Interface(interface) = fixture.store.type_payload(target).unwrap().data()
            else {
                panic!("Box must retain its generic interface target")
            };
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                interface
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap()[0],
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let plan = {
            let host = relation_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            super::super::object_members::plan_generic_interface(&fixture.store, &host, owner)
                .unwrap()
        };
        assert!(fixture.store.publish_interface_no_base_resolution(target));
        super::super::object_members::publish_generic_interface_declared_members(
            &mut fixture.store,
            &plan,
            target,
            &[parameter, string],
        )
        .unwrap();
        fixture
            .store
            .resolve_generic_interface_members(target, None)
            .unwrap();
        let reference = fixture
            .store
            .create_direct_generic_reference_type(target, &[string])
            .unwrap();
        let proxy = fixture
            .store
            .resolve_generic_interface_property(reference, "value", None)
            .unwrap()
            .unwrap()
            .symbol();
        let value = alloc_typed_property(&mut fixture.store, "value", string, false);
        let label = alloc_typed_property(&mut fixture.store, "label", string, false);
        let expected = alloc_property_object(&mut fixture.store, vec![value, label]);
        assert_eq!(
            fixture.store.is_type_assignable_to(reference, expected),
            Ok(true)
        );

        let original = fixture.store.value_symbol_links(proxy).unwrap().clone();
        let wrong_mapper = fixture
            .store
            .new_type_mapper(vec![parameter], vec![number])
            .unwrap();
        assert!(fixture.store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                mapper: Some(wrong_mapper),
                ..original.clone()
            },
        ));
        let before = fixture.store.relation_state_snapshot();
        assert_eq!(
            fixture.store.is_type_assignable_to(reference, expected),
            Err(RelationUnavailable::InvalidStructuredMembers(reference))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);

        assert!(
            fixture
                .store
                .set_value_symbol_links(proxy, original.clone())
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(reference, expected),
            Ok(true)
        );
        assert!(fixture.store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..original
            },
        ));
        let before = fixture.store.relation_state_snapshot();
        assert_eq!(
            fixture.store.is_type_assignable_to(reference, expected),
            Err(RelationUnavailable::InvalidStructuredMembers(reference))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
    }

    #[test]
    fn warmed_large_union_observes_validator_only_constituents_after_a_match() {
        let mut store = initialized(true);
        let literals = ["alpha", "beta", "gamma", "delta"]
            .into_iter()
            .map(|value| store.regular_string_literal_type(value.into()).unwrap())
            .collect::<Vec<_>>();
        let target = canonical_union(&mut store, &literals);
        let ordered = match store.type_payload(target).unwrap().data() {
            TypeData::Union(data) => data.union.types.clone(),
            _ => panic!("four literals must retain a union"),
        };
        assert!(ordered.len() >= 4);
        let source = ordered[0];
        let validator_only = *ordered.last().unwrap();

        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        let root_key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, root_key)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );

        assert!(store.set_literal_links(validator_only, Some(validator_only), validator_only,));
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE,
            "union validation read the later constituent before comparison short-circuited"
        );
        let stale = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::MalformedLiteral(validator_only))
        );
        assert_eq!(
            store.relation_state_snapshot(),
            stale,
            "failed revalidation must not publish a replacement relation"
        );
    }

    #[test]
    fn signature_arity_distinguishes_required_optional_and_strict_subtypes() {
        let mut fixture = function_relation_fixture(
            r"
                type Zero = () => void;
                type Required = (value: string) => void;
                type Optional = (value?: string) => void;
                type VoidParameter = (value: void) => void;
            ",
        );
        let (zero, _) = query_function_alias(&mut fixture, "Zero");
        let (required, _) = query_function_alias(&mut fixture, "Required");
        let (optional, _) = query_function_alias(&mut fixture, "Optional");
        let (void_parameter, _) = query_function_alias(&mut fixture, "VoidParameter");
        resolve_all_function_returns(&mut fixture);

        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(required, zero, true),
            Ok(false)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(optional, zero, true),
            Ok(true)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(void_parameter, zero, true),
            Ok(true)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(zero, required, true),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_related_to_with_strict_function_types(
                optional,
                zero,
                RelationKind::StrictSubtype,
                true,
            ),
            Ok(false)
        );
    }

    #[test]
    fn signature_returns_are_covariant_with_void_and_any_targets() {
        let mut fixture = function_relation_fixture(
            r#"
                type Literal = () => "fixed";
                type Wide = () => string;
                type Number = () => number;
                type Void = () => void;
                type Any = () => any;
            "#,
        );
        let (literal, _) = query_function_alias(&mut fixture, "Literal");
        let (wide, _) = query_function_alias(&mut fixture, "Wide");
        let (number, _) = query_function_alias(&mut fixture, "Number");
        let (void, _) = query_function_alias(&mut fixture, "Void");
        let (any, _) = query_function_alias(&mut fixture, "Any");
        resolve_all_function_returns(&mut fixture);

        for (source, target, expected) in [
            (literal, wide, true),
            (wide, literal, false),
            (number, void, true),
            (number, any, true),
        ] {
            assert_eq!(
                fixture
                    .store
                    .is_type_assignable_to_with_strict_function_types(source, target, true),
                Ok(expected)
            );
        }
    }

    #[test]
    fn nested_callback_parameters_use_the_pinned_reversed_comparison() {
        let mut fixture = function_relation_fixture(
            r#"
                type WideCallback = (value: string) => void;
                type NarrowCallback = (value: "fixed") => void;
                type WideOuter = (callback: WideCallback) => void;
                type NarrowOuter = (callback: NarrowCallback) => void;
                type WideOptional = (callback?: WideCallback) => void;
                type NarrowOptional = (callback?: NarrowCallback) => void;
            "#,
        );
        let (wide_outer, _) = query_function_alias(&mut fixture, "WideOuter");
        let (narrow_outer, _) = query_function_alias(&mut fixture, "NarrowOuter");
        let (wide_optional, _) = query_function_alias(&mut fixture, "WideOptional");
        let (narrow_optional, _) = query_function_alias(&mut fixture, "NarrowOptional");
        resolve_all_function_returns(&mut fixture);

        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(wide_outer, narrow_outer, true),
            Ok(false)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(narrow_outer, wide_outer, true),
            Ok(true)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(
                    wide_optional,
                    narrow_optional,
                    true,
                ),
            Ok(false)
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(
                    narrow_optional,
                    wide_optional,
                    true,
                ),
            Ok(true)
        );
    }

    #[test]
    fn function_empty_object_and_any_function_relations_are_directional() {
        let mut fixture = function_relation_fixture("type Callable = () => void;");
        let (callable, _) = query_function_alias(&mut fixture, "Callable");
        let (empty, any_function) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.empty_object_type, bootstrap.any_function_type)
        };

        for (source, target, expected) in [
            (callable, empty, true),
            (empty, callable, false),
            (any_function, callable, true),
            (callable, any_function, false),
        ] {
            assert_eq!(
                fixture
                    .store
                    .is_type_assignable_to_with_strict_function_types(source, target, true),
                Ok(expected)
            );
        }
    }

    #[test]
    fn canonical_tuples_and_property_free_functions_are_never_related() {
        let mut fixture = function_relation_fixture(
            "type Callable = () => void; type Single = [string]; type Empty = [];",
        );
        let (callable, _) = query_function_alias(&mut fixture, "Callable");
        let single = query_type_alias(&mut fixture, "Single");
        let empty = query_type_alias(&mut fixture, "Empty");

        for tuple in [single, empty] {
            for relation in [
                RelationKind::Assignable,
                RelationKind::Subtype,
                RelationKind::StrictSubtype,
                RelationKind::Comparable,
            ] {
                assert_eq!(
                    fixture.store.is_type_related_to_with_strict_function_types(
                        callable, tuple, relation, true,
                    ),
                    Ok(false)
                );
                assert_eq!(
                    fixture.store.is_type_related_to_with_strict_function_types(
                        tuple, callable, relation, true,
                    ),
                    Ok(false)
                );
            }
        }
    }

    #[test]
    fn callable_sources_participate_in_weak_and_fresh_empty_preflights() {
        let mut fixture = function_relation_fixture("type Callable = () => void;");
        let (callable, _) = query_function_alias(&mut fixture, "Callable");
        let (string, any_function) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.any_function_type)
        };
        let weak_property = alloc_typed_property(&mut fixture.store, "expected", string, true);
        let weak_target = alloc_property_object(&mut fixture.store, vec![weak_property]);
        let fresh_empty = alloc_fresh_property_object(&mut fixture.store, Vec::new());
        let ordinary_empty = alloc_property_object(&mut fixture.store, Vec::new());

        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(callable, weak_target, true),
            Ok(false),
            "an exact call signature makes the source nonempty for weak-target overlap"
        );
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(any_function, weak_target, true),
            Ok(true),
            "the intrinsic anyFunction has no upstream signature list for the weak check"
        );

        for source in [callable, any_function] {
            assert_eq!(
                fixture.store.is_type_related_to_with_strict_function_types(
                    source,
                    fresh_empty,
                    RelationKind::StrictSubtype,
                    true,
                ),
                Ok(false),
                "callable sources are nonempty for the fresh-empty subtype shortcut"
            );
        }
        assert_eq!(
            fixture.store.is_type_related_to_with_strict_function_types(
                ordinary_empty,
                fresh_empty,
                RelationKind::StrictSubtype,
                true,
            ),
            Ok(true)
        );
    }

    #[test]
    fn canonical_array_empty_object_shortcut_rejects_callable_surfaces() {
        let mut fixture = function_relation_fixture("type Callable = () => void;");
        let (callable, _) = query_function_alias(&mut fixture, "Callable");
        let (number, empty_object, any_function) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.empty_object_type,
                bootstrap.any_function_type,
            )
        };
        let array = alloc_canonical_array_target(&mut fixture.store, "Array");
        let global_types = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(array.target, array.target),
            string_wrapper: empty_object,
            number_wrapper: empty_object,
            boolean_wrapper: empty_object,
        };
        let array_number = canonical_array_reference(&mut fixture.store, array.target, number);
        let signature = fixture
            .store
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
            .unwrap();
        let call_signature_object = alloc_object_shell(&mut fixture.store);
        assert!(fixture.store.set_structured_type_members(
            call_signature_object,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        let before = fixture.store.relation_state_snapshot();

        for (source, target) in [
            (array_number, callable),
            (callable, array_number),
            (array_number, any_function),
            (any_function, array_number),
        ] {
            assert_eq!(
                fixture
                    .store
                    .is_type_related_to_with_optional_global_types_and_options(
                        source,
                        target,
                        RelationKind::StrictSubtype,
                        Some(global_types),
                        Some(true),
                    ),
                Err(RelationUnavailable::StructuralRelation {
                    source,
                    target,
                    relation: RelationKind::StrictSubtype,
                })
            );
            assert_eq!(fixture.store.relation_state_snapshot(), before);
        }

        for (source, target) in [
            (array_number, call_signature_object),
            (call_signature_object, array_number),
        ] {
            assert_eq!(
                fixture
                    .store
                    .is_type_related_to_with_optional_global_types_and_options(
                        source,
                        target,
                        RelationKind::StrictSubtype,
                        Some(global_types),
                        Some(true),
                    ),
                Err(RelationUnavailable::StructuredSignatures(
                    call_signature_object
                ))
            );
            assert_eq!(fixture.store.relation_state_snapshot(), before);
        }
    }

    #[test]
    fn unresolved_signature_return_rolls_back_nested_relation_writes() {
        let mut fixture = function_relation_fixture(
            r"
                type Left = (value: { item: string }) => string;
                type Right = (value: { item: string }) => string;
            ",
        );
        let (left, left_signature) = query_function_alias(&mut fixture, "Left");
        let (right, right_signature) = query_function_alias(&mut fixture, "Right");
        resolve_function_return(&mut fixture, left_signature);
        let before = fixture.store.relation_state_snapshot();

        {
            let bootstrap = fixture.store.relation_bootstrap_facts().unwrap();
            let mut session = super::RelaterSession::new_with_global_types_and_options(
                &mut fixture.store,
                RelationKind::Assignable,
                bootstrap,
                None,
                Some(true),
            );
            assert_eq!(
                session.is_related_to_ex(
                    left,
                    right,
                    super::RecursionFlags::BOTH,
                    super::IntersectionState::NONE,
                ),
                Err(RelationUnavailable::UnresolvedSignatureReturn(
                    right_signature
                ))
            );
            assert!(
                !session.pending.writes.is_empty(),
                "the resolved object-parameter comparison must enqueue a nested result"
            );
        }
        assert_eq!(fixture.store.relation_state_snapshot(), before);

        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(left, right, true),
            Err(RelationUnavailable::UnresolvedSignatureReturn(
                right_signature
            ))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);

        resolve_function_return(&mut fixture, right_signature);
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(left, right, true),
            Ok(true)
        );
    }

    #[test]
    fn recursive_callback_comparison_propagates_maybe_before_root_commit() {
        let mut fixture = function_relation_fixture(
            r"
                type Left = (next: Left) => void;
                type Right = (next: Right) => void;
            ",
        );
        let (left, _) = query_function_alias(&mut fixture, "Left");
        let (right, _) = query_function_alias(&mut fixture, "Right");
        resolve_all_function_returns(&mut fixture);
        let bootstrap = fixture.store.relation_bootstrap_facts().unwrap();
        let mut session = super::RelaterSession::new_with_global_types_and_options(
            &mut fixture.store,
            RelationKind::Assignable,
            bootstrap,
            None,
            Some(true),
        );
        let result = session
            .is_related_to_ex(
                left,
                right,
                super::RecursionFlags::BOTH,
                super::IntersectionState::NONE,
            )
            .unwrap();
        assert_eq!(result, Ternary::Maybe);
        assert!(session.finish(left, right, result).unwrap());
    }

    #[test]
    fn malformed_function_signature_fails_closed_without_relation_writes() {
        let mut fixture =
            function_relation_fixture("type Left = () => string; type Right = () => string;");
        let (left, left_signature) = query_function_alias(&mut fixture, "Left");
        let (right, _) = query_function_alias(&mut fixture, "Right");
        resolve_all_function_returns(&mut fixture);
        assert!(
            fixture
                .store
                .set_signature_flags(left_signature, SignatureFlags::ABSTRACT)
        );
        let before = fixture.store.relation_state_snapshot();
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(left, right, true),
            Err(RelationUnavailable::MalformedFunctionType(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
    }

    #[test]
    fn malformed_function_alias_is_classified_before_property_object_rejection() {
        let mut fixture =
            function_relation_fixture("type Left = () => string; type Right = () => string;");
        let (left, _) = query_function_alias(&mut fixture, "Left");
        let (right, _) = query_function_alias(&mut fixture, "Right");
        resolve_all_function_returns(&mut fixture);
        let alias = fixture
            .store
            .type_payload(left)
            .and_then(TypeRecord::alias)
            .expect("the named function type retains its alias record");
        let alias_symbol = fixture
            .store
            .type_alias(alias)
            .expect("the named function type retains its alias record")
            .symbol()
            .expect("the named function type retains its alias symbol");
        assert!(fixture.store.set_type_alias_links(
            alias_symbol,
            TypeAliasLinks {
                declared_type: Some(right),
                ..TypeAliasLinks::default()
            },
        ));

        let before = fixture.store.relation_state_snapshot();
        assert_eq!(
            fixture
                .store
                .is_type_assignable_to_with_strict_function_types(left, right, true),
            Err(RelationUnavailable::MalformedFunctionType(left))
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
    }

    fn alloc_symbol(store: &mut TestStore, flags: SymbolFlags, name: &str) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap()
    }

    fn alloc_literal(store: &mut TestStore, flags: TypeFlags, value: LiteralValue) -> TypeId {
        store
            .alloc_literal_type(flags, value, RegularLiteralLink::SelfType)
            .unwrap()
    }

    fn canonical_union(store: &mut TestStore, types: &[TypeId]) -> TypeId {
        store.literal_union_type(types, None).unwrap()
    }

    fn named_canonical_union(store: &mut TestStore, name: &str, types: &[TypeId]) -> TypeId {
        let symbol = alloc_symbol(store, SymbolFlags::TYPE_ALIAS, name);
        store.literal_union_type(types, Some(symbol)).unwrap()
    }

    fn alloc_resolved_object(
        store: &mut TestStore,
        object_flags: ObjectFlags,
        properties: Option<Vec<SemanticSymbolId>>,
    ) -> TypeId {
        let object = store.alloc_plain_object_type(object_flags, None).unwrap();
        assert!(store.set_structured_type_members(object, None, properties, None, None, None));
        object
    }

    fn alloc_typed_property(
        store: &mut TestStore,
        name: &str,
        type_id: TypeId,
        optional: bool,
    ) -> SemanticSymbolId {
        let flags = SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let symbol = alloc_symbol(store, flags, name);
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_id),
                ..ValueSymbolLinks::default()
            },
        ));
        symbol
    }

    fn alloc_object_shell(store: &mut TestStore) -> TypeId {
        store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap()
    }

    fn set_object_properties(
        store: &mut TestStore,
        object: TypeId,
        properties: Vec<SemanticSymbolId>,
    ) {
        let members = if properties.is_empty() {
            None
        } else {
            let members = store.alloc_symbol_table();
            for property in &properties {
                let name = store
                    .symbol(*property)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
                    .to_owned();
                assert_eq!(
                    store.insert_symbol(members, EscapedName::source(&name), *property),
                    Some(None)
                );
            }
            Some(members)
        };
        let properties = (!properties.is_empty()).then_some(properties);
        assert!(store.set_structured_type_members(object, members, properties, None, None, None,));
    }

    fn alloc_property_object(store: &mut TestStore, properties: Vec<SemanticSymbolId>) -> TypeId {
        let object = alloc_object_shell(store);
        set_object_properties(store, object, properties);
        object
    }

    struct FreshPropertyObjectFixture {
        type_: TypeId,
        owner: SemanticSymbolId,
        raw_properties: Vec<SemanticSymbolId>,
        properties: Vec<SemanticSymbolId>,
    }

    fn alloc_fresh_property_object_fixture(
        store: &mut TestStore,
        properties: Vec<SemanticSymbolId>,
    ) -> FreshPropertyObjectFixture {
        let property_facts = properties
            .iter()
            .map(|property| {
                let record = store.symbol(*property).unwrap();
                assert_eq!(record.flags(), SymbolFlags::PROPERTY);
                assert_eq!(record.check_flags(), CheckFlags::NONE);
                assert!(record.declarations().is_none());
                assert!(record.value_declaration().is_none());
                assert!(record.parent().is_none());
                let name = record.name().as_utf8().unwrap().to_owned();
                let type_ = store
                    .value_symbol_links(*property)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                (name, type_)
            })
            .collect::<Vec<_>>();
        let source = format!(
            "const value = {{ {} }};",
            property_facts
                .iter()
                .map(|(name, _)| format!("{name:?}: 0"))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(
            u32::try_from(store.symbol_len())
                .unwrap()
                .checked_add(10_000)
                .unwrap(),
        );
        let scope = AstScope::new(file, &parsed.arena);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let object_literal = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression)
                    .then(|| scope.node_ref(node).unwrap())
            })
            .unwrap();
        let mut assignments = parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::PropertyAssignment)
            .map(|(node, record)| (record.range.start, scope.node_ref(node).unwrap()))
            .collect::<Vec<_>>();
        assignments.sort_by_key(|(start, _)| *start);
        assert_eq!(assignments.len(), properties.len());

        let mut owner_data = SymbolData::new(
            SymbolFlags::OBJECT_LITERAL,
            EscapedName::internal(InternalSymbolName::Object),
        );
        owner_data.declarations = Some(vec![object_literal]);
        owner_data.value_declaration = Some(object_literal);
        let owner = store.alloc_symbol(owner_data).unwrap();
        let raw_members = store.alloc_symbol_table();
        let members = store.alloc_symbol_table();
        let mut synthetic_properties = Vec::with_capacity(properties.len());
        let mut object_flags = ObjectFlags::ANONYMOUS
            | ObjectFlags::OBJECT_LITERAL
            | ObjectFlags::FRESH_LITERAL
            | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
        for (((raw, (name, property_type)), (_, declaration)), index) in properties
            .iter()
            .zip(&property_facts)
            .zip(&assignments)
            .zip(0..)
        {
            assert_eq!(index, synthetic_properties.len());
            assert!(store.set_symbol_declarations(
                *raw,
                Some(vec![*declaration]),
                Some(*declaration),
            ));
            assert!(store.set_symbol_relationships(*raw, None, None, Some(owner), None));
            assert!(store.set_value_symbol_links(*raw, ValueSymbolLinks::default()));
            assert_eq!(
                store.insert_symbol(raw_members, EscapedName::source(name), *raw),
                Some(None)
            );

            let property = store.alloc_transient_symbol(
                SymbolFlags::PROPERTY,
                EscapedName::source(name),
                CheckFlags::NONE,
            );
            assert!(store.set_symbol_declarations(
                property,
                Some(vec![*declaration]),
                Some(*declaration),
            ));
            assert!(store.set_symbol_relationships(property, None, None, Some(owner), None));
            assert!(store.set_value_symbol_links(
                property,
                ValueSymbolLinks {
                    resolved_type: Some(*property_type),
                    target: Some(*raw),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert_eq!(
                store.insert_symbol(members, EscapedName::source(name), property),
                Some(None)
            );
            object_flags |= store.type_payload(*property_type).unwrap().object_flags()
                & ObjectFlags::PROPAGATING_FLAGS;
            synthetic_properties.push(property);
        }
        let raw_members = (!properties.is_empty()).then_some(raw_members);
        assert!(store.set_symbol_relationships(owner, raw_members, None, None, None));
        let object = store
            .alloc_plain_object_type(object_flags, Some(owner))
            .unwrap();
        let structured_properties =
            (!synthetic_properties.is_empty()).then(|| synthetic_properties.clone());
        assert!(store.set_structured_type_members(
            object,
            Some(members),
            structured_properties,
            None,
            None,
            None,
        ));
        FreshPropertyObjectFixture {
            type_: object,
            owner,
            raw_properties: properties,
            properties: synthetic_properties,
        }
    }

    fn alloc_fresh_property_object(
        store: &mut TestStore,
        properties: Vec<SemanticSymbolId>,
    ) -> TypeId {
        alloc_fresh_property_object_fixture(store, properties).type_
    }

    fn alloc_synthetic_type_literal_object(store: &mut TestStore, type_id: TypeId) -> TypeId {
        let parsed = parse_source_file(&format!(
            "type Shape{} = {{ x: string }};",
            store.symbol_len()
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(
            u32::try_from(store.symbol_len())
                .unwrap()
                .checked_add(30_000)
                .unwrap(),
        );
        let scope = AstScope::new(file, &parsed.arena);
        assert!(store.register_ast_scope(scope));
        let node_of_kind = |kind| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == kind).then(|| scope.node_ref(node).unwrap())
                })
                .unwrap_or_else(|| panic!("fixture is missing {kind:?}"))
        };
        let type_literal = node_of_kind(SyntaxKind::TypeLiteral);
        let property_declaration = node_of_kind(SyntaxKind::PropertyDeclaration);

        let mut owner_data = SymbolData::new(
            SymbolFlags::TYPE_LITERAL,
            EscapedName::internal(InternalSymbolName::Type),
        );
        owner_data.declarations = Some(vec![type_literal]);
        let owner = store.alloc_symbol(owner_data).unwrap();
        let property = alloc_typed_property(store, "x", type_id, false);
        assert!(store.set_symbol_declarations(
            property,
            Some(vec![property_declaration]),
            Some(property_declaration),
        ));
        assert!(store.set_symbol_relationships(property, None, None, Some(owner), None,));
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(owner))
            .unwrap();
        set_object_properties(store, object, vec![property]);
        object
    }

    fn attach_direct_type_alias(
        store: &mut TestStore,
        object: TypeId,
        symbol: Option<SemanticSymbolId>,
        type_arguments: Option<Vec<TypeId>>,
        declared_type: Option<TypeId>,
    ) {
        let alias = store.alloc_type_alias(symbol).unwrap();
        if type_arguments.is_some() {
            assert!(store.set_type_alias_arguments(alias, type_arguments));
        }
        assert!(store.set_type_alias(object, Some(alias)));
        if let Some(symbol) = symbol
            && let Some(declared_type) = declared_type
        {
            assert!(store.set_type_alias_links(
                symbol,
                TypeAliasLinks {
                    declared_type: Some(declared_type),
                    ..TypeAliasLinks::default()
                },
            ));
        }
    }

    fn install_global_object(store: &mut TestStore, object_type: TypeId) -> SemanticSymbolId {
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let raw_properties = store
            .type_payload(object_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.clone())
            .unwrap_or_default();
        let raw_members = if raw_properties.is_empty() {
            None
        } else {
            let members = store.alloc_symbol_table();
            for property in raw_properties {
                let name = store
                    .symbol(property)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
                    .to_owned();
                assert_eq!(
                    store.insert_symbol(members, EscapedName::source(&name), property),
                    Some(None)
                );
            }
            Some(members)
        };
        let object_symbol = alloc_symbol(store, SymbolFlags::INTERFACE, "Object");
        assert!(store.set_symbol_relationships(object_symbol, raw_members, None, None, None,));
        assert_eq!(
            store.insert_symbol(globals, EscapedName::source("Object"), object_symbol),
            Some(None)
        );
        assert!(store.set_declared_type_links(
            object_symbol,
            DeclaredTypeLinks {
                declared_type: Some(object_type),
                ..DeclaredTypeLinks::default()
            },
        ));
        object_symbol
    }

    fn alloc_global_property_query(store: &mut TestStore) -> (TypeId, TypeId) {
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source = alloc_property_object(store, Vec::new());
        let target_property = alloc_typed_property(store, "custom", string, false);
        let target = alloc_property_object(store, vec![target_property]);
        (source, target)
    }

    fn alloc_enum_type(store: &mut TestStore, symbol: SemanticSymbolId) -> TypeId {
        let enum_type = alloc_literal(store, TypeFlags::ENUM, LiteralValue::ComputedEnum);
        assert!(store.set_type_symbol(enum_type, Some(symbol)));
        enum_type
    }

    fn alloc_reference(store: &mut TestStore, target: TypeId, arguments: Vec<TypeId>) -> TypeId {
        let reference = store.alloc_type_reference(ObjectFlags::NONE, None).unwrap();
        assert!(store.set_object_target_and_mapper(reference, Some(target), None));
        assert!(store.set_type_reference_resolution(reference, None, Some(arguments)));
        reference
    }

    #[derive(Clone, Copy)]
    struct CanonicalArrayTargetFixture {
        target: TypeId,
        symbol: SemanticSymbolId,
    }

    fn alloc_canonical_array_target(
        store: &mut TestStore,
        name: &str,
    ) -> CanonicalArrayTargetFixture {
        let symbol = alloc_symbol(store, SymbolFlags::INTERFACE, name);
        let parameter_symbol = alloc_symbol(store, SymbolFlags::TYPE_PARAMETER, "T");
        let parameter = store.alloc_type_parameter(Some(parameter_symbol)).unwrap();
        assert!(store.set_declared_type_links(
            parameter_symbol,
            DeclaredTypeLinks {
                declared_type: Some(parameter),
                ..DeclaredTypeLinks::default()
            },
        ));
        let target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .unwrap();
        let this_type = store.alloc_type_parameter(Some(symbol)).unwrap();
        assert!(store.initialize_interface_type_parameters(
            target,
            vec![parameter, this_type],
            0,
            this_type,
            type_list_key(&[parameter]),
        ));
        CanonicalArrayTargetFixture { target, symbol }
    }

    fn add_required_array_property(
        store: &mut TestStore,
        target: CanonicalArrayTargetFixture,
        name: &str,
    ) -> SemanticSymbolId {
        let parsed = parse_source_file(&format!("interface Array<T> {{ {name}: number }}"));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(
            u32::try_from(store.symbol_len())
                .unwrap()
                .checked_add(20_000)
                .unwrap(),
        );
        let scope = AstScope::new(file, &parsed.arena);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(
                    record.kind,
                    SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature
                )
                .then(|| scope.node_ref(node).unwrap())
            })
            .unwrap();
        let mut data = SymbolData::new(SymbolFlags::PROPERTY, EscapedName::source(name));
        data.declarations = Some(vec![declaration]);
        data.value_declaration = Some(declaration);
        let property = store.alloc_symbol(data).unwrap();
        assert!(store.set_symbol_relationships(property, None, None, Some(target.symbol), None,));
        let members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source(name), property),
            Some(None)
        );
        assert!(store.set_symbol_relationships(target.symbol, Some(members), None, None, None,));
        property
    }

    fn canonical_array_reference(
        store: &mut TestStore,
        target: TypeId,
        argument: TypeId,
    ) -> TypeId {
        create_type_from_generic_global_type(store, target, argument, ObjectFlags::NONE).unwrap()
    }

    fn alloc_array_literal_clone(
        store: &mut TestStore,
        target: CanonicalArrayTargetFixture,
        argument: TypeId,
    ) -> TypeId {
        let base = canonical_array_reference(store, target.target, argument);
        let flags = (store.type_payload(base).unwrap().object_flags()
            & !ObjectFlags::MEMBERS_RESOLVED)
            | ObjectFlags::ARRAY_LITERAL
            | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
        let clone = store
            .alloc_type_reference(flags, Some(target.symbol))
            .unwrap();
        assert!(store.set_object_target_and_mapper(clone, Some(target.target), None));
        assert!(store.set_type_reference_resolution(clone, None, Some(vec![argument]),));
        assert_eq!(
            store.derived_types.array_literal_types.insert(base, clone),
            None
        );
        clone
    }

    fn cache_resolved_members(
        store: &mut TestStore,
        symbol: SemanticSymbolId,
        members: ts_binder::SymbolTableId,
    ) {
        let mut links = MembersAndExportsLinks::default();
        links.tables[MembersOrExportsResolutionKind::ResolvedMembers as usize] = Some(members);
        assert!(store.set_members_and_exports_links(symbol, links));
    }

    #[test]
    fn entrypoints_require_bootstrap_and_reject_foreign_types_atomically() {
        let mut uninitialized = TestStore::new();
        let string = uninitialized
            .alloc_intrinsic_type(TypeFlags::STRING, "string")
            .unwrap();
        assert_eq!(
            uninitialized.is_type_assignable_to(string, string),
            Err(RelationUnavailable::MissingBootstrap)
        );

        let mut store = initialized(true);
        let foreign = initialized(true);
        let local_string = store.intrinsic_bootstrap().unwrap().string_type;
        let foreign_string = foreign.intrinsic_bootstrap().unwrap().string_type;
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(local_string, foreign_string),
            Err(RelationUnavailable::Type(foreign_string))
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn fresh_literals_singletons_and_advanced_identity_follow_pinned_fast_path() {
        let mut store = initialized(true);
        let (regular_false, fresh_false, any, auto, string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.regular_false_type,
                bootstrap.false_type,
                bootstrap.any_type,
                bootstrap.auto_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        assert_eq!(
            store.is_type_identical_to(fresh_false, regular_false),
            Ok(true)
        );
        assert_eq!(store.is_type_identical_to(any, auto), Ok(true));
        assert_eq!(store.is_type_identical_to(string, number), Ok(false));
        assert_eq!(store.compare_types_identical(any, auto), Ok(Ternary::True));

        let left = store
            .alloc_union_type(ObjectFlags::NONE, vec![string, number])
            .unwrap();
        let right = store
            .alloc_union_type(ObjectFlags::NONE, vec![string, number])
            .unwrap();
        assert_eq!(
            store.is_type_identical_to(left, right),
            Err(RelationUnavailable::MalformedUnion(left))
        );
    }

    #[test]
    fn canonical_primitive_unions_follow_pinned_some_each_and_identity_rules() {
        let mut store = initialized(true);
        let (any, unknown, never, string, number, bigint, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.unknown_type,
                bootstrap.never_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
            )
        };
        let string_number = canonical_union(&mut store, &[string, number]);

        assert_eq!(store.is_type_assignable_to(string, string_number), Ok(true));
        assert_eq!(
            store.is_type_strict_subtype_of(string, string_number),
            Ok(true)
        );
        assert_eq!(
            store.is_type_assignable_to(bigint, string_number),
            Ok(false)
        );
        assert_eq!(
            store.is_type_assignable_to(string_number, string),
            Ok(false)
        );
        assert_eq!(
            store.is_type_strict_subtype_of(string_number, string),
            Ok(false)
        );
        assert_eq!(store.is_type_comparable_to(string_number, number), Ok(true));
        assert_eq!(
            store.is_type_comparable_to(string_number, boolean),
            Ok(false)
        );
        assert_eq!(
            store.is_type_assignable_to(string_number, unknown),
            Ok(true)
        );
        assert_eq!(store.is_type_assignable_to(never, string_number), Ok(true));
        assert_eq!(store.is_type_assignable_to(any, string_number), Ok(true));
        assert_eq!(
            store.is_type_assignable_to(unknown, string_number),
            Ok(false)
        );

        let string_literal = store.regular_string_literal_type("value".into()).unwrap();
        let other_string_literal = store.regular_string_literal_type("other".into()).unwrap();
        let literal_target = canonical_union(&mut store, &[other_string_literal, number]);
        assert_eq!(
            store.is_type_assignable_to(string_literal, string_number),
            Ok(true),
            "the primitive-union literal fast path recognizes the base primitive"
        );
        assert_eq!(
            store.is_type_assignable_to(string_literal, literal_target),
            Ok(false),
            "an unrelated literal has neither a base primitive nor alternate form in the target"
        );

        let left = named_canonical_union(&mut store, "Left", &[string, number]);
        let right = named_canonical_union(&mut store, "Right", &[string, number]);
        let different = named_canonical_union(&mut store, "Different", &[string, bigint]);
        assert_ne!(left, right);
        assert_eq!(store.is_type_identical_to(left, right), Ok(true));
        assert_eq!(store.is_type_identical_to(left, different), Ok(false));
        assert_eq!(store.is_type_assignable_to(left, right), Ok(true));

        let one = store.regular_number_literal_type(Number::new(1.0)).unwrap();
        let two = store.regular_number_literal_type(Number::new(2.0)).unwrap();
        let three = store.regular_number_literal_type(Number::new(3.0)).unwrap();
        let numeric_left = named_canonical_union(&mut store, "NumericLeft", &[one, two]);
        let numeric_right = named_canonical_union(&mut store, "NumericRight", &[one, three]);
        assert_eq!(
            store.is_type_identical_to(numeric_left, numeric_right),
            Ok(false),
            "different number literals are exact negative identity results"
        );
    }

    #[test]
    fn nullable_primitive_unions_preserve_strict_and_loose_branch_order() {
        let mut strict = initialized(true);
        let (undefined, null, string, number) = {
            let bootstrap = strict.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let nullable_string = canonical_union(&mut strict, &[null, string]);
        let optional_string = canonical_union(&mut strict, &[undefined, string]);
        let nullish_string = canonical_union(&mut strict, &[undefined, null, string]);
        let string_number = canonical_union(&mut strict, &[string, number]);

        assert_eq!(
            strict.is_type_assignable_to(string, nullable_string),
            Ok(true)
        );
        assert_eq!(
            strict.is_type_assignable_to(string, nullish_string),
            Ok(true)
        );
        assert_eq!(
            strict.is_type_assignable_to(number, nullable_string),
            Ok(false)
        );
        assert_eq!(
            strict.is_type_assignable_to(nullable_string, string),
            Ok(false)
        );
        assert_eq!(
            strict.is_type_assignable_to(undefined, optional_string),
            Ok(true)
        );
        assert_eq!(
            strict.is_type_assignable_to(undefined, string_number),
            Ok(false)
        );
        assert_eq!(strict.relation_cache_size(RelationKind::Assignable), 0);

        let mut loose = initialized(false);
        let (undefined, string, number) = {
            let bootstrap = loose.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let string_number = canonical_union(&mut loose, &[string, number]);
        assert_eq!(
            loose.is_type_assignable_to(undefined, string_number),
            Ok(true)
        );
        assert_eq!(loose.relation_cache_size(RelationKind::Assignable), 0);
    }

    #[test]
    fn primitive_union_cache_policy_is_directional_symmetric_and_owner_isolated() {
        let mut store = initialized(true);
        let (undefined, null, string, number, bigint, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
            )
        };
        let small = canonical_union(&mut store, &[string, number]);
        assert_eq!(store.is_type_assignable_to(small, string), Ok(false));
        assert_eq!(store.is_type_assignable_to(string, small), Ok(true));
        assert_eq!(store.relation_cache_size(RelationKind::Assignable), 0);

        let large = canonical_union(&mut store, &[undefined, null, string, number]);
        assert_eq!(store.is_type_assignable_to(large, bigint), Ok(false));
        assert_eq!(store.relation_cache_size(RelationKind::Assignable), 1);
        let after_large = store.relation_state_snapshot();
        assert_eq!(store.is_type_assignable_to(large, bigint), Ok(false));
        assert_eq!(store.relation_state_snapshot(), after_large);

        let left = named_canonical_union(&mut store, "CacheLeft", &[string, boolean]);
        let right = named_canonical_union(&mut store, "CacheRight", &[string, boolean]);
        assert_eq!(
            store.relation_state_snapshot(),
            after_large,
            "initializing fresh union identities must preserve unrelated relation entries"
        );
        assert_eq!(store.is_type_assignable_to(left, right), Ok(true));
        assert_eq!(store.relation_cache_size(RelationKind::Assignable), 2);
        assert_eq!(store.relation_cache_size(RelationKind::Subtype), 0);
        assert_eq!(store.is_type_subtype_of(left, right), Ok(true));
        assert_eq!(store.relation_cache_size(RelationKind::Assignable), 2);
        assert_eq!(store.relation_cache_size(RelationKind::Subtype), 1);
        assert_eq!(store.relation_cache_size(RelationKind::StrictSubtype), 0);
        assert_eq!(store.is_type_strict_subtype_of(left, right), Ok(true));
        assert_eq!(store.relation_cache_size(RelationKind::StrictSubtype), 1);
        assert_eq!(store.relation_cache_size(RelationKind::Comparable), 0);
        assert_eq!(store.is_type_comparable_to(left, right), Ok(true));
        assert_eq!(store.relation_cache_size(RelationKind::Comparable), 1);

        assert_eq!(store.is_type_identical_to(left, right), Ok(true));
        assert_eq!(store.relation_cache_size(RelationKind::Identity), 1);
        let after_identity = store.relation_state_snapshot();
        assert_eq!(store.is_type_identical_to(right, left), Ok(true));
        assert_eq!(store.relation_state_snapshot(), after_identity);
    }

    #[test]
    fn malformed_union_errors_are_atomic_but_existing_cache_entries_win() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let malformed_source = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![string, number])
            .unwrap();
        let malformed_target = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![string, number])
            .unwrap();
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(malformed_source, malformed_target),
            Err(RelationUnavailable::MalformedUnion(malformed_source))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let key = store
            .relation_key_if_available(
                malformed_source,
                malformed_target,
                super::IntersectionState::NONE,
                false,
                false,
            )
            .unwrap()
            .key();
        store.relation_cache_set(
            RelationKind::Assignable,
            key,
            RelationComparisonResult::SUCCEEDED,
        );
        let cached = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(malformed_source, malformed_target),
            Ok(true)
        );
        assert_eq!(store.relation_state_snapshot(), cached);
    }

    #[test]
    fn union_structural_escape_rolls_back_the_root_pending_relation() {
        let mut store = initialized(true);
        let (undefined, null, string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let source = canonical_union(&mut store, &[undefined, null, string, number]);
        let target = alloc_property_object(&mut store, Vec::new());
        let before = store.relation_state_snapshot();
        let result = store.is_type_assignable_to(source, target);
        assert!(matches!(
            result,
            Err(RelationUnavailable::StructuralRelation {
                target: found_target,
                relation: RelationKind::Assignable,
                ..
            }) if found_target == target
        ));
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn top_bottom_wildcard_and_primitive_widening_matrix_is_exact_and_uncached() {
        let mut store = initialized(true);
        let (any, unknown, never, wildcard, string, number, bigint, boolean, es_symbol, true_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.unknown_type,
                bootstrap.never_type,
                bootstrap.wildcard_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
                bootstrap.es_symbol_type,
                bootstrap.true_type,
            )
        };
        let string_literal = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL,
            LiteralValue::String("value".into()),
        );
        let number_literal = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        let bigint_literal = alloc_literal(
            &mut store,
            TypeFlags::BIG_INT_LITERAL,
            LiteralValue::BigInt(PseudoBigInt::new("1", false)),
        );
        let unique_symbol = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "unique");
        let unique_symbol_type = store.alloc_unique_es_symbol_type(unique_symbol).unwrap();
        let before = store.relation_state_snapshot();

        assert_eq!(store.is_type_assignable_to(string, any), Ok(true));
        assert_eq!(store.is_type_subtype_of(never, number), Ok(true));
        assert_eq!(store.is_type_assignable_to(wildcard, never), Ok(true));
        assert_eq!(store.is_type_subtype_of(number, unknown), Ok(true));
        assert_eq!(store.is_type_strict_subtype_of(any, unknown), Ok(false));
        assert_eq!(store.is_type_subtype_of(any, unknown), Ok(true));
        assert_eq!(store.is_type_assignable_to(string, never), Ok(false));
        assert_eq!(
            store.is_type_assignable_to(string_literal, string),
            Ok(true)
        );
        assert_eq!(
            store.is_type_assignable_to(number_literal, number),
            Ok(true)
        );
        assert_eq!(
            store.is_type_assignable_to(bigint_literal, bigint),
            Ok(true)
        );
        assert_eq!(store.is_type_assignable_to(true_type, boolean), Ok(true));
        assert_eq!(
            store.is_type_assignable_to(unique_symbol_type, es_symbol),
            Ok(true)
        );
        assert_eq!(store.is_type_assignable_to(any, number), Ok(true));
        assert_eq!(store.is_type_comparable_to(any, number), Ok(true));
        assert_eq!(store.is_type_subtype_of(any, number), Ok(false));
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn authenticated_string_and_template_literals_compare_against_template_patterns() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let target = store
            .get_template_literal_type(&["do-".to_owned(), String::new()], &[string])
            .unwrap();
        let narrow = store
            .get_template_literal_type(&["do-prefix-".to_owned(), String::new()], &[number])
            .unwrap();
        let wrong_pattern = store
            .get_template_literal_type(&["undo-".to_owned(), String::new()], &[number])
            .unwrap();
        let matching = store.regular_string_literal_type("do-save".into()).unwrap();
        let wrong = store
            .regular_string_literal_type("undo-save".into())
            .unwrap();
        let fresh = store.fresh_type_of_literal_type(matching).unwrap();
        let before = store.relation_state_snapshot();

        for relation in [
            RelationKind::Assignable,
            RelationKind::Subtype,
            RelationKind::StrictSubtype,
            RelationKind::Comparable,
        ] {
            assert_eq!(
                store.is_type_related_to(matching, target, relation),
                Ok(true)
            );
            assert_eq!(store.is_type_related_to(fresh, target, relation), Ok(true));
            assert_eq!(store.is_type_related_to(wrong, target, relation), Ok(false));
            assert_eq!(store.is_type_related_to(narrow, target, relation), Ok(true));
            assert_eq!(
                store.is_type_related_to(wrong_pattern, target, relation),
                Ok(false)
            );
        }
        assert_eq!(store.is_type_comparable_to(target, matching), Ok(true));
        assert_eq!(store.is_type_comparable_to(target, wrong), Ok(false));
        assert_eq!(store.is_type_identical_to(matching, target), Ok(false));
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn template_relations_reject_unowned_literal_and_duplicate_pattern_identities() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let texts = ["do-".to_owned(), String::new()];
        let pattern = store.get_template_literal_type(&texts, &[string]).unwrap();
        let forged_literal = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL,
            LiteralValue::String("do-save".into()),
        );
        let canonical_literal = store.regular_string_literal_type("do-save".into()).unwrap();
        let forged_pattern = store
            .alloc_template_literal_type(texts.to_vec(), vec![string])
            .unwrap();
        let before = store.relation_state_snapshot();

        assert_eq!(
            store.is_type_assignable_to(forged_literal, pattern),
            Err(RelationUnavailable::MalformedLiteral(forged_literal))
        );
        assert_eq!(
            store.is_type_assignable_to(canonical_literal, forged_pattern),
            Err(RelationUnavailable::MalformedStructuredType(forged_pattern))
        );
        assert_eq!(
            store.is_type_assignable_to(forged_pattern, pattern),
            Err(RelationUnavailable::MalformedStructuredType(forged_pattern))
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn enum_backed_literal_values_use_direct_equality_including_nan() {
        let mut store = initialized(true);
        let enum_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::String("x".into()),
        );
        let ordinary_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL,
            LiteralValue::String("x".into()),
        );
        let other_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL,
            LiteralValue::String("y".into()),
        );
        assert_eq!(
            store.is_type_assignable_to(enum_string, ordinary_string),
            Ok(true)
        );
        assert_eq!(
            store.is_type_assignable_to(enum_string, other_string),
            Ok(false)
        );

        let enum_number = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        let ordinary_number = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        assert_eq!(
            store.is_type_assignable_to(enum_number, ordinary_number),
            Ok(true)
        );

        let enum_nan = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::nan()),
        );
        let ordinary_nan = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL,
            LiteralValue::Number(Number::nan()),
        );
        assert_eq!(
            store.is_type_assignable_to(enum_nan, ordinary_nan),
            Ok(false),
            "Go's direct jsnum.Number equality keeps NaN unequal"
        );
    }

    #[test]
    fn strict_and_non_strict_nullability_preserve_union_exclusion() {
        let mut strict = initialized(true);
        let (undefined, null, void, string) = {
            let bootstrap = strict.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.void_type,
                bootstrap.string_type,
            )
        };
        assert_eq!(strict.is_type_assignable_to(undefined, void), Ok(true));
        assert_eq!(strict.is_type_assignable_to(undefined, string), Ok(false));
        assert_eq!(strict.is_type_assignable_to(null, string), Ok(false));

        let mut loose = initialized(false);
        let (undefined, null, string, number) = {
            let bootstrap = loose.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        assert_eq!(loose.is_type_assignable_to(undefined, string), Ok(true));
        assert_eq!(loose.is_type_assignable_to(null, number), Ok(true));
        let union = loose
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![string, number])
            .unwrap();
        assert_eq!(
            loose.is_type_assignable_to(undefined, union),
            Err(RelationUnavailable::MalformedUnion(union))
        );
    }

    #[test]
    fn object_to_nonprimitive_preserves_empty_strict_subtype_exception() {
        let mut store = initialized(true);
        let (empty, any_function, non_primitive) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.empty_object_type,
                bootstrap.any_function_type,
                bootstrap.non_primitive_type,
            )
        };
        assert_eq!(store.is_type_assignable_to(empty, non_primitive), Ok(true));
        assert_eq!(
            store.is_type_strict_subtype_of(empty, non_primitive),
            Err(RelationUnavailable::StructuralRelation {
                source: empty,
                target: non_primitive,
                relation: RelationKind::StrictSubtype,
            })
        );
        assert_eq!(
            store.is_type_strict_subtype_of(any_function, non_primitive),
            Ok(true)
        );

        let fresh_empty = alloc_resolved_object(
            &mut store,
            ObjectFlags::ANONYMOUS | ObjectFlags::FRESH_LITERAL,
            None,
        );
        assert_eq!(
            store.is_type_strict_subtype_of(fresh_empty, non_primitive),
            Ok(true)
        );
        let property = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "value");
        let nonempty =
            alloc_resolved_object(&mut store, ObjectFlags::ANONYMOUS, Some(vec![property]));
        assert_eq!(
            store.is_type_strict_subtype_of(nonempty, non_primitive),
            Ok(true)
        );
    }

    #[test]
    fn object_to_primitive_relations_fail_without_requesting_structural_support() {
        let mut store = initialized(true);
        let (number, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let object = alloc_resolved_object(&mut store, ObjectFlags::ANONYMOUS, None);

        assert_eq!(store.is_type_assignable_to(object, number), Ok(false));
        assert_eq!(store.is_type_strict_subtype_of(object, string), Ok(false));
        assert_eq!(store.is_type_comparable_to(object, number), Ok(false));
        assert_eq!(
            store.is_type_identical_to(object, number),
            Ok(false),
            "the object/primitive fast path also preserves identity disjointness"
        );
    }

    #[test]
    fn global_primitive_wrappers_supply_apparent_types_without_legacy_cache_leaks() {
        let mut store = initialized(true);
        let (number, empty_object, empty_generic) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.empty_object_type,
                bootstrap.empty_generic_type,
            )
        };
        let wrapper_value = alloc_typed_property(&mut store, "value", number, false);
        let number_wrapper = alloc_property_object(&mut store, vec![wrapper_value]);
        let matching_value = alloc_typed_property(&mut store, "value", number, false);
        let matching_target = alloc_property_object(&mut store, vec![matching_value]);
        let missing_id = alloc_typed_property(&mut store, "id", number, false);
        let mismatching_target = alloc_property_object(&mut store, vec![missing_id]);
        let global_types = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(empty_generic, empty_generic),
            string_wrapper: empty_object,
            number_wrapper,
            boolean_wrapper: empty_object,
        };

        assert_eq!(
            store.is_type_assignable_to(number, matching_target),
            Err(RelationUnavailable::StructuralRelation {
                source: number,
                target: matching_target,
                relation: RelationKind::Assignable,
            })
        );
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                number,
                matching_target,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Ok(true)
        );
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                number,
                mismatching_target,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Ok(false)
        );
        let after_global_warmup = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(number, matching_target),
            Err(RelationUnavailable::StructuralRelation {
                source: number,
                target: matching_target,
                relation: RelationKind::Assignable,
            })
        );
        assert_eq!(store.relation_state_snapshot(), after_global_warmup);
    }

    #[test]
    fn unresolved_primitive_wrappers_reject_proven_missing_required_properties() {
        for (declaration, name) in [
            ("interface Number { value: number }", "Number"),
            ("interface String { value: string }", "String"),
            ("interface Boolean { value: boolean }", "Boolean"),
        ] {
            let mut fixture = function_relation_fixture(declaration);
            let wrapper = query_declared_interface(&mut fixture, name);
            let (source, number, empty_generic) = {
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                (
                    match name {
                        "Number" => bootstrap.number_type,
                        "String" => bootstrap.string_type,
                        "Boolean" => bootstrap.boolean_type,
                        _ => unreachable!("only primitive wrapper interfaces are covered"),
                    },
                    bootstrap.number_type,
                    bootstrap.empty_generic_type,
                )
            };
            let required = alloc_typed_property(&mut fixture.store, "id", number, false);
            let target = alloc_property_object(&mut fixture.store, vec![required]);
            let global_types = RelationGlobalTypes {
                array_targets: CanonicalArrayTargets::for_test(empty_generic, empty_generic),
                string_wrapper: wrapper,
                number_wrapper: wrapper,
                boolean_wrapper: wrapper,
            };
            let before = fixture.store.relation_state_snapshot();

            assert_eq!(
                fixture.store.is_type_related_to_with_optional_global_types(
                    source,
                    target,
                    RelationKind::Assignable,
                    Some(global_types),
                ),
                Ok(false)
            );
            assert_eq!(fixture.store.relation_state_snapshot(), before);
        }
    }

    #[test]
    fn unresolved_primitive_wrapper_checks_preserve_global_interface_augmentations() {
        for source in [
            "interface Number { id: number }",
            "interface Number {} interface Object { id: number }",
        ] {
            let mut fixture = function_relation_fixture(source);
            let wrapper = query_declared_interface(&mut fixture, "Number");
            let object = source
                .contains("interface Object")
                .then(|| query_declared_interface(&mut fixture, "Object"));
            let (number, empty_generic) = {
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                (bootstrap.number_type, bootstrap.empty_generic_type)
            };
            let required = alloc_typed_property(&mut fixture.store, "id", number, false);
            let target = alloc_property_object(&mut fixture.store, vec![required]);
            let global_types = RelationGlobalTypes {
                array_targets: CanonicalArrayTargets::for_test(empty_generic, empty_generic),
                string_wrapper: wrapper,
                number_wrapper: wrapper,
                boolean_wrapper: wrapper,
            };
            let before = fixture.store.relation_state_snapshot();

            assert_eq!(
                fixture.store.is_type_related_to_with_optional_global_types(
                    number,
                    target,
                    RelationKind::Assignable,
                    Some(global_types),
                ),
                Err(RelationUnavailable::UnresolvedStructuredMembers(
                    object.unwrap_or(wrapper)
                ))
            );
            assert_eq!(fixture.store.relation_state_snapshot(), before);
        }
    }

    #[test]
    fn unresolved_primitive_wrappers_do_not_ignore_inherited_interface_members() {
        let mut fixture = function_relation_fixture(
            "interface Extra { id: number } interface Number extends Extra {}",
        );
        let wrapper = query_declared_interface(&mut fixture, "Number");
        let (number, empty_generic) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.empty_generic_type)
        };
        let required = alloc_typed_property(&mut fixture.store, "id", number, false);
        let target = alloc_property_object(&mut fixture.store, vec![required]);
        let global_types = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(empty_generic, empty_generic),
            string_wrapper: wrapper,
            number_wrapper: wrapper,
            boolean_wrapper: wrapper,
        };
        let before = fixture.store.relation_state_snapshot();

        assert!(matches!(
            fixture.store.is_type_related_to_with_optional_global_types(
                number,
                target,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Err(
                RelationUnavailable::UnresolvedStructuredMembers(type_)
                    | RelationUnavailable::UnsupportedStructuredType(type_)
            ) if type_ == wrapper
        ));
        assert_eq!(fixture.store.relation_state_snapshot(), before);
    }

    #[test]
    fn late_bound_type_literal_members_require_and_honor_the_resolved_members_cache() {
        let mut store = initialized(true);
        let non_primitive = store.intrinsic_bootstrap().unwrap().non_primitive_type;
        let symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_LITERAL, "__type");
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
            .unwrap();
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_strict_subtype_of(object, non_primitive),
            Err(RelationUnavailable::LateBoundMembers(symbol))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let members = store.alloc_symbol_table();
        cache_resolved_members(&mut store, symbol, members);
        assert_eq!(
            store.is_type_strict_subtype_of(object, non_primitive),
            Err(RelationUnavailable::StructuralRelation {
                source: object,
                target: non_primitive,
                relation: RelationKind::StrictSubtype,
            })
        );

        let property = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "value");
        assert_eq!(
            store.insert_symbol(members, EscapedName::source("value"), property),
            Some(None)
        );
        assert_eq!(
            store.is_type_strict_subtype_of(object, non_primitive),
            Ok(true)
        );
    }

    #[test]
    fn resolved_nonempty_type_literal_falls_through_to_cached_symbol_members() {
        let mut store = initialized(true);
        let non_primitive = store.intrinsic_bootstrap().unwrap().non_primitive_type;
        let symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_LITERAL, "__inconsistent");
        let structured_property =
            alloc_symbol(&mut store, SymbolFlags::PROPERTY, "structuredProperty");
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            None,
            Some(vec![structured_property]),
            None,
            None,
            None,
        ));
        let cached_members = store.alloc_symbol_table();
        cache_resolved_members(&mut store, symbol, cached_members);

        assert_eq!(
            store.is_type_strict_subtype_of(object, non_primitive),
            Err(RelationUnavailable::StructuralRelation {
                source: object,
                target: non_primitive,
                relation: RelationKind::StrictSubtype,
            })
        );
    }

    #[test]
    fn comparability_checks_reverse_first_and_guards_reverse_never() {
        let mut store = initialized(true);
        let (any, never) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.any_type, bootstrap.never_type)
        };
        let enum_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::String("x".into()),
        );
        let ordinary_string = alloc_literal(
            &mut store,
            TypeFlags::STRING_LITERAL,
            LiteralValue::String("x".into()),
        );
        assert_eq!(
            store.is_type_comparable_to(ordinary_string, enum_string),
            Ok(true)
        );
        assert_eq!(
            store.is_type_comparable_to(enum_string, ordinary_string),
            Ok(true)
        );
        assert_eq!(store.is_type_comparable_to(any, never), Ok(false));
        assert_eq!(store.are_types_comparable(any, never), Ok(true));
    }

    #[test]
    fn numeric_enum_carveouts_and_enum_capability_boundary_are_exact() {
        let mut store = initialized(true);
        let (number, number_literal) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.zero_type)
        };
        let enum_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let computed_enum = alloc_enum_type(&mut store, enum_symbol);
        assert_eq!(store.is_type_assignable_to(number, computed_enum), Ok(true));
        assert_eq!(store.is_type_subtype_of(number, computed_enum), Ok(false));
        assert_eq!(
            store.is_type_assignable_to(number_literal, computed_enum),
            Ok(true)
        );

        let enum_zero = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::new(0.0)),
        );
        assert!(store.set_type_symbol(enum_zero, Some(enum_symbol)));
        assert_eq!(
            store.is_type_assignable_to(number_literal, enum_zero),
            Ok(true)
        );

        let same_enum_other_type = alloc_enum_type(&mut store, enum_symbol);
        assert_eq!(
            store.is_type_assignable_to(computed_enum, same_enum_other_type),
            Ok(true)
        );
        let same_name_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let same_name_enum = alloc_enum_type(&mut store, same_name_symbol);
        assert_eq!(
            store.is_type_assignable_to(computed_enum, same_name_enum),
            Err(RelationUnavailable::EnumRelation {
                source: enum_symbol,
                target: same_name_symbol,
            })
        );
        let other_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "Other");
        let other_enum = alloc_enum_type(&mut store, other_symbol);
        assert_eq!(
            store.is_type_assignable_to(computed_enum, other_enum),
            Ok(false)
        );
    }

    #[test]
    fn enum_relation_cache_answers_success_failure_and_miss_directionally() {
        let mut store = initialized(true);
        let source_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let target_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let miss_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let source = alloc_enum_type(&mut store, source_symbol);
        let target = alloc_enum_type(&mut store, target_symbol);
        let miss = alloc_enum_type(&mut store, miss_symbol);

        assert!(store.enum_relation_cache_set(
            source_symbol,
            target_symbol,
            RelationComparisonResult::SUCCEEDED,
        ));
        assert!(store.enum_relation_cache_set(
            target_symbol,
            source_symbol,
            RelationComparisonResult::FAILED,
        ));
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        assert_eq!(store.is_type_assignable_to(target, source), Ok(false));
        assert_eq!(
            store.is_type_assignable_to(source, miss),
            Err(RelationUnavailable::EnumRelation {
                source: source_symbol,
                target: miss_symbol,
            })
        );
        assert_eq!(store.enum_relation_cache_size(), 2);
    }

    #[test]
    fn warmed_parent_relation_revalidates_the_exact_enum_pair() {
        let mut store = initialized(true);
        let source_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let target_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let source_enum = alloc_enum_type(&mut store, source_symbol);
        let target_enum = alloc_enum_type(&mut store, target_symbol);
        let source_property = alloc_typed_property(&mut store, "value", source_enum, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let target_property = alloc_typed_property(&mut store, "value", target_enum, false);
        let target = alloc_property_object(&mut store, vec![target_property]);

        assert!(store.enum_relation_cache_set(
            source_symbol,
            target_symbol,
            RelationComparisonResult::SUCCEEDED,
        ));
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        let root_key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, root_key)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );

        let warmed = store.relation_state_snapshot();
        assert!(store.enum_relation_cache_set(
            source_symbol,
            target_symbol,
            RelationComparisonResult::SUCCEEDED,
        ));
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, root_key)
                .intersects(RelationComparisonResult::SUCCEEDED),
            "an equal enum-pair publication must preserve the parent cache"
        );
        assert_eq!(store.relation_state_snapshot(), warmed);

        assert!(store.enum_relation_cache_set(
            source_symbol,
            target_symbol,
            RelationComparisonResult::FAILED,
        ));
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE,
        );
        assert_eq!(store.is_type_assignable_to(source, target), Ok(false));
    }

    #[test]
    fn enum_member_symbols_canonicalize_to_their_shared_parent() {
        let mut store = initialized(true);
        let enum_symbol = alloc_symbol(&mut store, SymbolFlags::REGULAR_ENUM, "E");
        let left_member = alloc_symbol(&mut store, SymbolFlags::ENUM_MEMBER, "Left");
        let right_member = alloc_symbol(&mut store, SymbolFlags::ENUM_MEMBER, "Right");
        assert!(store.set_symbol_relationships(left_member, None, None, Some(enum_symbol), None,));
        assert!(store.set_symbol_relationships(right_member, None, None, Some(enum_symbol), None,));
        let left = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        let right = alloc_literal(
            &mut store,
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(Number::new(1.0)),
        );
        assert!(store.set_type_symbol(left, Some(left_member)));
        assert!(store.set_type_symbol(right, Some(right_member)));
        assert_eq!(store.is_type_assignable_to(left, right), Ok(true));
    }

    #[test]
    fn unknown_like_union_is_memoized_without_populating_relation_caches() {
        let mut store = initialized(true);
        let (string, unknown_union, undefined, null, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.unknown_union_type,
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.number_type,
            )
        };
        let before_relations = store.relation_state_snapshot();
        assert!(
            !store
                .type_payload(unknown_union)
                .unwrap()
                .object_flags()
                .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED)
        );
        assert_eq!(store.is_type_assignable_to(string, unknown_union), Ok(true));
        let flags = store.type_payload(unknown_union).unwrap().object_flags();
        assert!(flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED));
        assert!(flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION));
        assert_eq!(store.is_type_assignable_to(number, unknown_union), Ok(true));
        assert_eq!(store.relation_state_snapshot(), before_relations);

        let ordinary_union = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, null, string, number])
            .unwrap();
        assert_eq!(
            store.is_type_assignable_to(string, ordinary_union),
            Err(RelationUnavailable::MalformedUnion(ordinary_union))
        );
        let flags = store.type_payload(ordinary_union).unwrap().object_flags();
        assert!(flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED));
        assert!(!flags.intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION));
        assert_eq!(store.relation_state_snapshot(), before_relations);
    }

    #[test]
    fn unavailable_unknown_like_scan_does_not_publish_a_false_cache() {
        let mut store = initialized(true);
        let (string, undefined, null) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.undefined_type,
                bootstrap.null_type,
            )
        };
        let symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_LITERAL, "__late");
        let unresolved = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
            .unwrap();
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, null, unresolved])
            .unwrap();
        assert_eq!(
            store.is_type_assignable_to(string, union),
            Err(RelationUnavailable::LateBoundMembers(symbol))
        );
        assert!(
            !store
                .type_payload(union)
                .unwrap()
                .object_flags()
                .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED)
        );
    }

    #[test]
    fn object_cache_reads_are_directional_isolated_and_never_filled_on_miss() {
        let mut store = initialized(true);
        let source = alloc_resolved_object(&mut store, ObjectFlags::ANONYMOUS, None);
        let target = alloc_resolved_object(&mut store, ObjectFlags::ANONYMOUS, None);
        let key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        store.relation_cache_set(
            RelationKind::Assignable,
            key,
            RelationComparisonResult::SUCCEEDED,
        );
        store.relation_cache_set(RelationKind::Subtype, key, RelationComparisonResult::FAILED);
        store.relation_cache_set(
            RelationKind::StrictSubtype,
            key,
            RelationComparisonResult::SUCCEEDED,
        );
        store.relation_cache_set(
            RelationKind::Comparable,
            key,
            RelationComparisonResult::FAILED,
        );
        let identity_key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, true, false)
            .unwrap()
            .key();
        store.relation_cache_set(
            RelationKind::Identity,
            identity_key,
            RelationComparisonResult::FAILED,
        );
        let before = store.relation_state_snapshot();
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        assert_eq!(store.is_type_subtype_of(source, target), Ok(false));
        assert_eq!(store.is_type_strict_subtype_of(source, target), Ok(true));
        assert_eq!(store.is_type_identical_to(source, target), Ok(false));
        assert_eq!(store.is_type_comparable_to(source, target), Ok(false));
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn property_objects_use_pinned_comparable_structure_rules() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };

        let id = alloc_typed_property(&mut store, "id", string, false);
        let declared = alloc_property_object(&mut store, vec![id]);
        let empty = alloc_property_object(&mut store, Vec::new());
        assert_eq!(store.is_type_comparable_to(declared, empty), Ok(true));

        let wrong_id = alloc_typed_property(&mut store, "id", number, false);
        let wrong = alloc_property_object(&mut store, vec![wrong_id]);
        assert_eq!(store.is_type_comparable_to(declared, wrong), Ok(false));

        let optional_id = alloc_typed_property(&mut store, "id", string, true);
        let optional = alloc_property_object(&mut store, vec![optional_id]);
        let required_id = alloc_typed_property(&mut store, "id", string, false);
        let required = alloc_property_object(&mut store, vec![required_id]);
        assert_eq!(store.is_type_assignable_to(optional, required), Ok(false));
        assert_eq!(store.is_type_comparable_to(optional, required), Ok(true));

        let only_x = alloc_typed_property(&mut store, "x", string, false);
        let ordinary_source = alloc_property_object(&mut store, vec![only_x]);
        let optional_y = alloc_typed_property(&mut store, "y", string, true);
        let weak_target = alloc_property_object(&mut store, vec![optional_y]);
        assert_eq!(
            store.is_type_assignable_to(ordinary_source, weak_target),
            Ok(false)
        );
        assert_eq!(
            store.is_type_comparable_to(ordinary_source, weak_target),
            Ok(true),
            "Comparable skips weak common-property rejection for object sources"
        );

        let fresh_y = alloc_typed_property(&mut store, "y", string, false);
        let fresh = alloc_fresh_property_object(&mut store, vec![fresh_y]);
        assert_eq!(
            store.is_type_comparable_to(fresh, required),
            Ok(false),
            "Comparable still performs fresh excess-property checks"
        );
        assert!(store.relation_cache_size(RelationKind::Comparable) >= 4);
    }

    #[test]
    fn readonly_property_ordering_is_strict_subtype_only_and_cache_observed() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let readonly_property = alloc_typed_property(&mut store, "value", string, false);
        assert!(store.set_source_property_readonly(readonly_property, true));
        let readonly = alloc_property_object(&mut store, vec![readonly_property]);
        let mutable_property = alloc_typed_property(&mut store, "value", string, false);
        let mutable = alloc_property_object(&mut store, vec![mutable_property]);

        assert_eq!(store.is_type_assignable_to(readonly, mutable), Ok(true));
        assert_eq!(store.is_type_assignable_to(mutable, readonly), Ok(true));
        assert_eq!(
            store.is_type_strict_subtype_of(readonly, mutable),
            Ok(false)
        );
        assert_eq!(store.is_type_strict_subtype_of(mutable, readonly), Ok(true));

        let readonly_to_mutable = store
            .relation_key_if_available(
                readonly,
                mutable,
                super::IntersectionState::NONE,
                false,
                false,
            )
            .unwrap()
            .key();
        let mutable_to_readonly = store
            .relation_key_if_available(
                mutable,
                readonly,
                super::IntersectionState::NONE,
                false,
                false,
            )
            .unwrap()
            .key();
        assert_eq!(
            store.relation_cache_get(RelationKind::StrictSubtype, readonly_to_mutable),
            RelationComparisonResult::FAILED
        );
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, readonly_to_mutable)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );
        assert!(
            store
                .relation_cache_get(RelationKind::StrictSubtype, mutable_to_readonly)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );

        let warmed = store.relation_state_snapshot();
        assert!(store.set_source_property_readonly(readonly_property, true));
        assert_eq!(store.relation_state_snapshot(), warmed);
        assert_eq!(
            store.relation_cache_get(RelationKind::StrictSubtype, readonly_to_mutable),
            RelationComparisonResult::FAILED,
            "an equal readonly write preserves the warmed relation"
        );
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, readonly_to_mutable)
                .intersects(RelationComparisonResult::SUCCEEDED),
            "an equal readonly write preserves unrelated warmed relation kinds"
        );

        assert!(store.set_source_property_readonly(readonly_property, false));
        assert_eq!(
            store.relation_cache_get(RelationKind::StrictSubtype, readonly_to_mutable),
            RelationComparisonResult::NONE,
            "a changed observed readonly bit invalidates the warmed relation"
        );
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, readonly_to_mutable),
            RelationComparisonResult::NONE,
            "the observed-symbol mutation invalidates every relation cache kind"
        );
        assert_eq!(store.is_type_strict_subtype_of(readonly, mutable), Ok(true));
        assert_eq!(store.is_type_assignable_to(readonly, mutable), Ok(true));
    }

    #[test]
    fn subtype_property_objects_preserve_fresh_excess_and_shape_rules() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };

        let wide_id = alloc_typed_property(&mut store, "id", string, false);
        let wide_name = alloc_typed_property(&mut store, "name", number, false);
        let fresh_wide = alloc_fresh_property_object(&mut store, vec![wide_id, wide_name]);
        let narrow_id = alloc_typed_property(&mut store, "id", string, false);
        let fresh_narrow = alloc_fresh_property_object(&mut store, vec![narrow_id]);

        let before_excess = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_subtype_of(fresh_wide, fresh_narrow),
            Ok(false)
        );
        assert_eq!(store.relation_state_snapshot(), before_excess);
        assert_eq!(
            store.is_type_strict_subtype_of(fresh_wide, fresh_narrow),
            Ok(false)
        );
        assert_eq!(
            store.relation_state_snapshot(),
            before_excess,
            "fresh excess rejection precedes recursive cache publication"
        );

        let matching_source_id = alloc_typed_property(&mut store, "id", string, false);
        let matching_source = alloc_fresh_property_object(&mut store, vec![matching_source_id]);
        let matching_target_id = alloc_typed_property(&mut store, "id", string, false);
        let matching_target = alloc_fresh_property_object(&mut store, vec![matching_target_id]);
        assert_eq!(
            store.is_type_subtype_of(matching_source, matching_target),
            Ok(true)
        );
        assert_eq!(
            store.is_type_strict_subtype_of(matching_source, matching_target),
            Ok(true)
        );
        assert_eq!(store.relation_cache_size(RelationKind::Subtype), 1);
        assert_eq!(store.relation_cache_size(RelationKind::StrictSubtype), 1);
    }

    #[test]
    fn subtype_property_objects_preserve_optional_weak_and_empty_rules() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;

        let optional_value = alloc_typed_property(&mut store, "value", string, true);
        let optional_source = alloc_property_object(&mut store, vec![optional_value]);
        let required_value = alloc_typed_property(&mut store, "value", string, false);
        let required_target = alloc_property_object(&mut store, vec![required_value]);
        assert_eq!(
            store.is_type_subtype_of(optional_source, required_target),
            Ok(false)
        );
        assert_eq!(
            store.is_type_strict_subtype_of(optional_source, required_target),
            Ok(false)
        );

        let required_value = alloc_typed_property(&mut store, "value", string, false);
        let required_source = alloc_property_object(&mut store, vec![required_value]);
        let optional_value = alloc_typed_property(&mut store, "value", string, true);
        let optional_target = alloc_property_object(&mut store, vec![optional_value]);
        assert_eq!(
            store.is_type_subtype_of(required_source, optional_target),
            Ok(true)
        );
        assert_eq!(
            store.is_type_strict_subtype_of(required_source, optional_target),
            Ok(true)
        );

        let unrelated = alloc_typed_property(&mut store, "unrelated", string, false);
        let unrelated_source = alloc_property_object(&mut store, vec![unrelated]);
        let weak = alloc_typed_property(&mut store, "weak", string, true);
        let weak_target = alloc_property_object(&mut store, vec![weak]);
        let before_weak = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_subtype_of(unrelated_source, weak_target),
            Ok(false)
        );
        assert_eq!(store.relation_state_snapshot(), before_weak);
        assert_eq!(
            store.is_type_strict_subtype_of(unrelated_source, weak_target),
            Ok(false)
        );
        assert_eq!(store.relation_state_snapshot(), before_weak);

        let fresh_value = alloc_typed_property(&mut store, "value", string, false);
        let fresh_source = alloc_fresh_property_object(&mut store, vec![fresh_value]);
        let empty = alloc_property_object(&mut store, Vec::new());
        assert_eq!(store.is_type_assignable_to(fresh_source, empty), Ok(true));
        assert_eq!(store.is_type_comparable_to(fresh_source, empty), Ok(true));
        let before_subtype_excess = store.relation_state_snapshot();
        assert_eq!(store.is_type_subtype_of(fresh_source, empty), Ok(false));
        assert_eq!(store.relation_state_snapshot(), before_subtype_excess);
        assert_eq!(
            store.is_type_strict_subtype_of(fresh_source, empty),
            Ok(false)
        );
        assert_eq!(store.relation_state_snapshot(), before_subtype_excess);

        let ordinary_value = alloc_typed_property(&mut store, "value", string, false);
        let ordinary_source = alloc_property_object(&mut store, vec![ordinary_value]);
        assert_eq!(store.is_type_subtype_of(ordinary_source, empty), Ok(true));
        assert_eq!(
            store.is_type_strict_subtype_of(ordinary_source, empty),
            Ok(true)
        );

        let fresh_empty = alloc_fresh_property_object(&mut store, Vec::new());
        assert_eq!(
            store.is_type_subtype_of(ordinary_source, fresh_empty),
            Ok(false)
        );
        assert_eq!(
            store.is_type_strict_subtype_of(ordinary_source, fresh_empty),
            Ok(false)
        );
    }

    #[test]
    fn unavailable_subtype_property_relations_are_cache_atomic() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source_property = alloc_typed_property(&mut store, "value", string, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let unresolved_property = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "value");
        let target = alloc_property_object(&mut store, vec![unresolved_property]);

        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_subtype_of(source, target),
            Err(RelationUnavailable::UnresolvedPropertyType(
                unresolved_property
            ))
        );
        assert_eq!(store.relation_state_snapshot(), before);
        assert_eq!(
            store.is_type_strict_subtype_of(source, target),
            Err(RelationUnavailable::UnresolvedPropertyType(
                unresolved_property
            ))
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn explicit_global_array_relations_are_covariant_and_target_local() {
        let mut store = initialized(true);
        let (number, string, empty_object) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.empty_object_type,
            )
        };
        let number_or_string = canonical_union(&mut store, &[number, string]);
        let array = alloc_canonical_array_target(&mut store, "Array");
        let readonly_array = alloc_canonical_array_target(&mut store, "ReadonlyArray");
        let global_types = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(array.target, readonly_array.target),
            string_wrapper: empty_object,
            number_wrapper: empty_object,
            boolean_wrapper: empty_object,
        };
        let array_number = canonical_array_reference(&mut store, array.target, number);
        let array_union = canonical_array_reference(&mut store, array.target, number_or_string);
        let readonly_number = canonical_array_reference(&mut store, readonly_array.target, number);
        let readonly_union =
            canonical_array_reference(&mut store, readonly_array.target, number_or_string);

        let before_no_globals = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(array_number, array_union),
            Err(RelationUnavailable::UnsupportedStructuredType(array_union))
        );
        assert_eq!(store.relation_state_snapshot(), before_no_globals);

        for relation in [
            RelationKind::Assignable,
            RelationKind::Subtype,
            RelationKind::StrictSubtype,
        ] {
            assert_eq!(
                store.is_type_related_to_with_optional_global_types(
                    array_number,
                    array_union,
                    relation,
                    Some(global_types),
                ),
                Ok(true)
            );
            assert_eq!(
                store.is_type_related_to_with_optional_global_types(
                    array_union,
                    array_number,
                    relation,
                    Some(global_types),
                ),
                Ok(false)
            );
            assert_eq!(
                store.is_type_related_to_with_optional_global_types(
                    readonly_number,
                    readonly_union,
                    relation,
                    Some(global_types),
                ),
                Ok(true)
            );
        }
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                array_number,
                array_union,
                RelationKind::Identity,
                Some(global_types),
            ),
            Ok(false)
        );
        let after_global_warmup = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(array_number, array_union),
            Err(RelationUnavailable::UnsupportedStructuredType(array_union)),
            "global-aware Array answers do not leak through the shared legacy cache"
        );
        assert_eq!(store.relation_state_snapshot(), after_global_warmup);
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                array_number,
                readonly_union,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Ok(true),
            "mutable Array is covariant to the canonical ReadonlyArray target"
        );
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                readonly_number,
                array_union,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Ok(false),
            "ReadonlyArray is not assignable to mutable Array"
        );
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                array_number,
                readonly_number,
                RelationKind::Identity,
                Some(global_types),
            ),
            Ok(false),
            "different canonical array targets are never identical"
        );
    }

    #[test]
    fn primitives_do_not_acquire_canonical_array_shape_from_boxed_global_types() {
        let mut store = initialized(true);
        let (number, string, zero, empty_object) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.zero_type,
                bootstrap.empty_object_type,
            )
        };
        let array = alloc_canonical_array_target(&mut store, "Array");
        let global_types = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(array.target, array.target),
            string_wrapper: empty_object,
            number_wrapper: empty_object,
            boolean_wrapper: empty_object,
        };
        let array_number = canonical_array_reference(&mut store, array.target, number);

        for source in [number, string, zero] {
            for relation in [
                RelationKind::Assignable,
                RelationKind::Subtype,
                RelationKind::StrictSubtype,
                RelationKind::Comparable,
            ] {
                assert_eq!(
                    store.is_type_related_to_with_optional_global_types(
                        source,
                        array_number,
                        relation,
                        Some(global_types),
                    ),
                    Ok(false),
                );
            }
        }
    }

    #[test]
    fn canonical_arrays_only_reduce_against_empty_objects_with_required_surface_proof() {
        let mut store = initialized(true);
        let (number, empty_object) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.empty_object_type)
        };
        let array = alloc_canonical_array_target(&mut store, "Array");
        let global_types = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(array.target, array.target),
            string_wrapper: empty_object,
            number_wrapper: empty_object,
            boolean_wrapper: empty_object,
        };
        let array_number = canonical_array_reference(&mut store, array.target, number);
        let empty = alloc_property_object(&mut store, Vec::new());
        let id = alloc_typed_property(&mut store, "id", number, false);
        let nonempty = alloc_property_object(&mut store, vec![id]);

        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                array_number,
                empty,
                RelationKind::StrictSubtype,
                Some(global_types),
            ),
            Ok(true)
        );
        assert_eq!(store.relation_state_snapshot(), before);
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                empty,
                array_number,
                RelationKind::StrictSubtype,
                Some(global_types),
            ),
            Err(RelationUnavailable::UnsupportedStructuredType(array.target))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        {
            let bootstrap = store.relation_bootstrap_facts().unwrap();
            let mut session = super::RelaterSession::new_with_global_types(
                &mut store,
                RelationKind::StrictSubtype,
                bootstrap,
                Some(global_types),
            );
            assert_eq!(
                session.preflight_expression_union_array_object_pairs(&[array_number, empty]),
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(
                    array_number
                )),
                "an empty Array shell cannot prove the reverse subtype result"
            );
        }
        assert_eq!(store.relation_state_snapshot(), before);

        let length = add_required_array_property(&mut store, array, "length");
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                empty,
                array_number,
                RelationKind::StrictSubtype,
                Some(global_types),
            ),
            Ok(false)
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let (length_declarations, length_value_declaration) = {
            let record = store.symbol(length).unwrap();
            (
                record.declarations().unwrap().to_vec(),
                record.value_declaration(),
            )
        };
        for (declarations, value_declaration) in
            [(None, None), (Some(length_declarations.clone()), None)]
        {
            assert!(store.set_symbol_declarations(length, declarations, value_declaration));
            let poisoned = store.relation_state_snapshot();
            assert_eq!(
                store.is_type_related_to_with_optional_global_types(
                    empty,
                    array_number,
                    RelationKind::StrictSubtype,
                    Some(global_types),
                ),
                Err(RelationUnavailable::InvalidStructuredMembers(array.target))
            );
            assert_eq!(store.relation_state_snapshot(), poisoned);
            {
                let bootstrap = store.relation_bootstrap_facts().unwrap();
                let mut session = super::RelaterSession::new_with_global_types(
                    &mut store,
                    RelationKind::StrictSubtype,
                    bootstrap,
                    Some(global_types),
                );
                assert_eq!(
                    session.preflight_expression_union_array_object_pairs(&[array_number, empty,]),
                    Err(LiteralTypeCacheError::ArrayType {
                        type_: array_number,
                        error: ArrayTypeError::InvalidReference(array_number),
                    })
                );
            }
            assert_eq!(store.relation_state_snapshot(), poisoned);
            assert!(store.set_symbol_declarations(
                length,
                Some(length_declarations.clone()),
                length_value_declaration,
            ));
        }
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                empty,
                array_number,
                RelationKind::StrictSubtype,
                Some(global_types),
            ),
            Ok(false)
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let invalid_member = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "invalid");
        let invalid_members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(
                invalid_members,
                EscapedName::source("invalid"),
                invalid_member,
            ),
            Some(None)
        );
        assert!(store.set_structured_type_members(
            empty,
            Some(invalid_members),
            None,
            None,
            None,
            None,
        ));
        let poisoned = store.relation_state_snapshot();
        {
            let bootstrap = store.relation_bootstrap_facts().unwrap();
            let mut session = super::RelaterSession::new_with_global_types(
                &mut store,
                RelationKind::StrictSubtype,
                bootstrap,
                Some(global_types),
            );
            assert_eq!(
                session.preflight_expression_union_array_object_pairs(&[array_number, empty]),
                Err(LiteralTypeCacheError::InvalidCachedUnion(empty))
            );
        }
        assert_eq!(store.relation_state_snapshot(), poisoned);
        assert!(store.set_structured_type_members(empty, None, None, None, None, None));
        {
            let bootstrap = store.relation_bootstrap_facts().unwrap();
            let mut repaired = super::RelaterSession::new_with_global_types(
                &mut store,
                RelationKind::StrictSubtype,
                bootstrap,
                Some(global_types),
            );
            assert_eq!(
                repaired.preflight_expression_union_array_object_pairs(&[empty, array_number]),
                Ok(())
            );
        }
        assert_eq!(store.relation_state_snapshot(), before);

        for (source, target) in [(array_number, nonempty), (nonempty, array_number)] {
            assert!(matches!(
                store.is_type_related_to_with_optional_global_types(
                    source,
                    target,
                    RelationKind::StrictSubtype,
                    Some(global_types),
                ),
                Err(RelationUnavailable::StructuralRelation {
                    source: actual_source,
                    target: actual_target,
                    relation: RelationKind::StrictSubtype,
                }) if actual_source == source && actual_target == target
            ));
            assert_eq!(store.relation_state_snapshot(), before);
        }

        {
            let bootstrap = store.relation_bootstrap_facts().unwrap();
            let mut session = super::RelaterSession::new_with_global_types(
                &mut store,
                RelationKind::StrictSubtype,
                bootstrap,
                Some(global_types),
            );
            assert_eq!(
                session.preflight_expression_union_array_object_pairs(&[array_number, empty]),
                Ok(())
            );
            assert_eq!(
                session.preflight_expression_union_array_object_pairs(&[empty, array_number]),
                Ok(())
            );
            assert_eq!(
                session.preflight_expression_union_array_object_pairs(&[
                    empty,
                    array_number,
                    nonempty,
                ]),
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(nonempty)),
                "all mixed pairs are rejected before directional comparisons begin"
            );
        }
        assert_eq!(store.relation_state_snapshot(), before);

        assert!(store.set_type_reference_resolution(array_number, None, Some(vec![empty])));
        {
            let bootstrap = store.relation_bootstrap_facts().unwrap();
            let mut poisoned = super::RelaterSession::new_with_global_types(
                &mut store,
                RelationKind::StrictSubtype,
                bootstrap,
                Some(global_types),
            );
            assert_eq!(
                poisoned.preflight_expression_union_array_object_pairs(&[array_number, empty]),
                Err(LiteralTypeCacheError::ArrayType {
                    type_: array_number,
                    error: ArrayTypeError::GlobalType(
                        CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(
                            array.target
                        )
                    ),
                })
            );
        }
        assert_eq!(store.relation_state_snapshot(), before);

        assert!(store.set_type_reference_resolution(array_number, None, Some(vec![number])));
        {
            let bootstrap = store.relation_bootstrap_facts().unwrap();
            let mut repaired = super::RelaterSession::new_with_global_types(
                &mut store,
                RelationKind::StrictSubtype,
                bootstrap,
                Some(global_types),
            );
            assert_eq!(
                repaired.preflight_expression_union_array_object_pairs(&[array_number, empty]),
                Ok(())
            );
        }
        assert_eq!(store.relation_state_snapshot(), before);

        assert!(store.set_symbol_relationships(length, None, None, None, None));
        {
            let bootstrap = store.relation_bootstrap_facts().unwrap();
            let mut poisoned = super::RelaterSession::new_with_global_types(
                &mut store,
                RelationKind::StrictSubtype,
                bootstrap,
                Some(global_types),
            );
            assert_eq!(
                poisoned.preflight_expression_union_array_object_pairs(&[array_number, empty]),
                Err(LiteralTypeCacheError::ArrayType {
                    type_: array_number,
                    error: ArrayTypeError::InvalidReference(array_number),
                })
            );
        }
        assert_eq!(store.relation_state_snapshot(), before);

        assert!(store.set_symbol_relationships(length, None, None, Some(array.symbol), None,));
        {
            let bootstrap = store.relation_bootstrap_facts().unwrap();
            let mut repaired = super::RelaterSession::new_with_global_types(
                &mut store,
                RelationKind::StrictSubtype,
                bootstrap,
                Some(global_types),
            );
            assert_eq!(
                repaired.preflight_expression_union_array_object_pairs(&[empty, array_number]),
                Ok(())
            );
        }
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn canonical_array_literal_clones_and_malformed_references_are_distinguished() {
        let mut store = initialized(true);
        let (number, empty_object) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.empty_object_type)
        };
        let array = alloc_canonical_array_target(&mut store, "Array");
        let global_types = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(array.target, array.target),
            string_wrapper: empty_object,
            number_wrapper: empty_object,
            boolean_wrapper: empty_object,
        };
        let base = canonical_array_reference(&mut store, array.target, number);
        let literal = alloc_array_literal_clone(&mut store, array, number);
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                literal,
                base,
                RelationKind::Identity,
                Some(global_types),
            ),
            Ok(true)
        );

        let malformed_literal = store
            .alloc_type_reference(ObjectFlags::ARRAY_LITERAL, Some(array.symbol))
            .unwrap();
        assert!(store.set_object_target_and_mapper(malformed_literal, Some(array.target), None,));
        assert!(store.set_type_reference_resolution(malformed_literal, None, Some(vec![number]),));
        let before_malformed = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                base,
                malformed_literal,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Err(RelationUnavailable::MalformedCanonicalArrayReference(
                malformed_literal
            ))
        );
        assert_eq!(store.relation_state_snapshot(), before_malformed);

        let literal_flags = store.type_payload(literal).unwrap().object_flags();
        let uncached_literal = store
            .alloc_type_reference(literal_flags, Some(array.symbol))
            .unwrap();
        assert!(store.set_object_target_and_mapper(uncached_literal, Some(array.target), None,));
        assert!(store.set_type_reference_resolution(uncached_literal, None, Some(vec![number]),));
        let before_uncached_literal = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                base,
                uncached_literal,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Err(RelationUnavailable::MalformedCanonicalArrayReference(
                uncached_literal
            )),
            "an exact-shape clone without derived-cache ownership is rejected"
        );
        assert_eq!(store.relation_state_snapshot(), before_uncached_literal);

        let forged = store
            .alloc_type_reference(ObjectFlags::NONE, Some(array.symbol))
            .unwrap();
        assert!(store.set_object_target_and_mapper(forged, Some(array.target), None));
        assert!(store.set_type_reference_resolution(forged, None, Some(vec![number]),));
        let before_forged = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                base,
                forged,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Err(RelationUnavailable::MalformedCanonicalArrayReference(
                forged
            ))
        );
        assert_eq!(store.relation_state_snapshot(), before_forged);
    }

    #[test]
    fn unrelated_array_instantiation_preserves_an_exact_key_relation() {
        let mut store = initialized(true);
        let (number, string, any, empty_object) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.any_type,
                bootstrap.empty_object_type,
            )
        };
        let array = alloc_canonical_array_target(&mut store, "Array");
        let global_types = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(array.target, array.target),
            string_wrapper: empty_object,
            number_wrapper: empty_object,
            boolean_wrapper: empty_object,
        };
        let array_number = canonical_array_reference(&mut store, array.target, number);
        let array_any = canonical_array_reference(&mut store, array.target, any);
        let source_property = alloc_typed_property(&mut store, "items", array_number, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let target_property = alloc_typed_property(&mut store, "items", array_any, false);
        let target = alloc_property_object(&mut store, vec![target_property]);

        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                source,
                target,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Ok(true)
        );
        let root_key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, root_key)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );

        let _array_string = canonical_array_reference(&mut store, array.target, string);
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, root_key)
                .intersects(RelationComparisonResult::SUCCEEDED),
            "an unobserved target-local key must not stale the warmed relation"
        );
    }

    #[test]
    fn poisoned_or_fallback_array_targets_fail_without_relation_cache_writes() {
        let mut store = initialized(true);
        let (number, string, empty_object, empty_generic) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.empty_object_type,
                bootstrap.empty_generic_type,
            )
        };
        let number_or_string = canonical_union(&mut store, &[number, string]);
        let array = alloc_canonical_array_target(&mut store, "Array");
        let global_types = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(array.target, array.target),
            string_wrapper: empty_object,
            number_wrapper: empty_object,
            boolean_wrapper: empty_object,
        };
        let array_number = canonical_array_reference(&mut store, array.target, number);
        let array_union = canonical_array_reference(&mut store, array.target, number_or_string);
        assert!(store.set_type_reference_resolution(array_union, None, Some(vec![number]),));
        let before_poisoned = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                array_number,
                array_union,
                RelationKind::Assignable,
                Some(global_types),
            ),
            Err(RelationUnavailable::MalformedCanonicalArrayReference(
                array_union
            ))
        );
        assert_eq!(store.relation_state_snapshot(), before_poisoned);

        let fallback_source = alloc_reference(&mut store, empty_generic, vec![number]);
        let fallback_target = alloc_reference(&mut store, empty_generic, vec![string]);
        let fallback_globals = RelationGlobalTypes {
            array_targets: CanonicalArrayTargets::for_test(empty_generic, empty_generic),
            string_wrapper: empty_object,
            number_wrapper: empty_object,
            boolean_wrapper: empty_object,
        };
        let before_fallback = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_related_to_with_optional_global_types(
                fallback_source,
                fallback_target,
                RelationKind::Assignable,
                Some(fallback_globals),
            ),
            Err(RelationUnavailable::UnavailableCanonicalArrayTarget(
                empty_generic
            ))
        );
        assert_eq!(store.relation_state_snapshot(), before_fallback);
    }

    #[test]
    fn generic_object_key_gap_is_propagated_instead_of_becoming_a_cache_miss() {
        let mut store = initialized(true);
        let base = alloc_resolved_object(&mut store, ObjectFlags::ANONYMOUS, None);
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = alloc_reference(&mut store, base, vec![parameter]);
        let target = alloc_reference(&mut store, base, vec![parameter]);
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::RelationKeyTypeParameterConstraint(
                parameter
            ))
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn wrappers_return_only_true_or_false_ternary_values() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        assert_eq!(
            store.compare_types_assignable_simple(string, string),
            Ok(Ternary::True)
        );
        assert_eq!(
            store.compare_types_assignable_worker(string, number, true),
            Ok(Ternary::False)
        );
        assert_eq!(
            store.compare_types_subtype_of(string, number),
            Ok(Ternary::False)
        );
    }

    #[test]
    fn resolved_property_objects_support_width_mismatch_and_missing_checks() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let source_x = alloc_typed_property(&mut store, "x", string, false);
        let source_y = alloc_typed_property(&mut store, "y", number, false);
        let source = alloc_property_object(&mut store, vec![source_x, source_y]);

        let target_x = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_x]);
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));

        let wrong_x = alloc_typed_property(&mut store, "x", number, false);
        let wrong = alloc_property_object(&mut store, vec![wrong_x]);
        assert_eq!(store.is_type_assignable_to(source, wrong), Ok(false));

        let missing_z = alloc_typed_property(&mut store, "z", string, false);
        let missing = alloc_property_object(&mut store, vec![missing_z]);
        assert_eq!(store.is_type_assignable_to(source, missing), Ok(false));
        assert_eq!(store.relation_cache_size(RelationKind::Assignable), 3);
    }

    #[test]
    fn source_declared_index_signatures_compare_inferred_properties_and_value_types() {
        fn declared_alias(fixture: &mut FunctionRelationFixture, name: &str) -> TypeId {
            let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
            let symbol = fixture
                .store
                .symbol_table(globals)
                .and_then(|globals| globals.get_source(name))
                .unwrap_or_else(|| panic!("missing declared alias {name}"));
            let host = relation_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let result = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(symbol)
            .unwrap();
            assert!(diagnostics.is_empty());
            result
        }

        let mut fixture = function_relation_fixture(concat!(
            "type Numbers = { [key: string]: number }; ",
            "type Strings = { [key: string]: string }; ",
            "type ReadonlyNumbers = { readonly [key: string]: number }; ",
            "type NumericKeys = { [key: number]: number }; ",
            "type NumberProperty = { value: number };",
        ));
        let numbers = declared_alias(&mut fixture, "Numbers");
        let strings = declared_alias(&mut fixture, "Strings");
        let readonly_numbers = declared_alias(&mut fixture, "ReadonlyNumbers");
        let numeric_keys = declared_alias(&mut fixture, "NumericKeys");
        let declared = declared_alias(&mut fixture, "NumberProperty");
        let (number, string, any) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.any_type,
            )
        };
        let value = alloc_typed_property(&mut fixture.store, "value", number, false);
        let fresh_number = alloc_fresh_property_object(&mut fixture.store, vec![value]);
        let wrong = alloc_typed_property(&mut fixture.store, "value", string, false);
        let fresh_string = alloc_fresh_property_object(&mut fixture.store, vec![wrong]);
        let dynamic = alloc_typed_property(&mut fixture.store, "value", any, false);
        let fresh_any = alloc_fresh_property_object(&mut fixture.store, vec![dynamic]);

        assert_eq!(
            fixture.store.is_type_assignable_to(fresh_number, numbers),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(fresh_string, numbers),
            Ok(false)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(fresh_any, numbers),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(declared, numbers),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(numbers, strings),
            Ok(false)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(numbers, numeric_keys),
            Ok(true)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(numeric_keys, numbers),
            Ok(false)
        );
        assert_eq!(
            fixture
                .store
                .is_type_identical_to(numbers, readonly_numbers),
            Ok(false)
        );
    }

    #[test]
    fn broad_string_indexes_cover_matching_template_pattern_index_values() {
        fn declared_alias(fixture: &mut FunctionRelationFixture, name: &str) -> TypeId {
            let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
            let symbol = fixture
                .store
                .symbol_table(globals)
                .and_then(|globals| globals.get_source(name))
                .unwrap_or_else(|| panic!("missing declared alias {name}"));
            let host = relation_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let type_ = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(symbol)
            .unwrap();
            assert!(diagnostics.is_empty());
            type_
        }

        let mut fixture = function_relation_fixture(concat!(
            "type All = { [name: string]: number }; ",
            "type Actions = { [name: `do-${string}`]: number }; ",
            "type WrongActions = { [name: `do-${string}`]: string };",
        ));
        let all = declared_alias(&mut fixture, "All");
        let actions = declared_alias(&mut fixture, "Actions");
        let wrong_actions = declared_alias(&mut fixture, "WrongActions");

        assert_eq!(fixture.store.is_type_assignable_to(all, actions), Ok(true));
        assert_eq!(fixture.store.is_type_subtype_of(all, actions), Ok(true));
        assert_eq!(fixture.store.is_type_assignable_to(actions, all), Ok(false));
        assert_eq!(
            fixture.store.is_type_assignable_to(all, wrong_actions),
            Ok(false)
        );
        assert_eq!(fixture.store.is_type_identical_to(all, actions), Ok(false));
    }

    #[test]
    fn template_pattern_indexes_can_share_a_surface_with_declared_properties() {
        fn declared_alias(fixture: &mut FunctionRelationFixture, name: &str) -> TypeId {
            let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
            let symbol = fixture
                .store
                .symbol_table(globals)
                .and_then(|globals| globals.get_source(name))
                .unwrap_or_else(|| panic!("missing declared alias {name}"));
            let host = relation_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let result = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(symbol)
            .unwrap();
            assert!(diagnostics.is_empty());
            result
        }

        let mut fixture = function_relation_fixture(concat!(
            "type Attributes = { required: string; [name: `do-${string}`]: number }; ",
            "type Same = { required: string; [name: `do-${string}`]: number };",
        ));
        let target = declared_alias(&mut fixture, "Attributes");
        let same = declared_alias(&mut fixture, "Same");
        let (string, number) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };

        let required = alloc_typed_property(&mut fixture.store, "required", string, false);
        let matching = alloc_typed_property(&mut fixture.store, "do-save", number, false);
        let valid = alloc_fresh_property_object(&mut fixture.store, vec![required, matching]);
        let required = alloc_typed_property(&mut fixture.store, "required", string, false);
        let wrong_value = alloc_typed_property(&mut fixture.store, "do-save", string, false);
        let wrong = alloc_fresh_property_object(&mut fixture.store, vec![required, wrong_value]);
        let required = alloc_typed_property(&mut fixture.store, "required", string, false);
        let unrelated = alloc_typed_property(&mut fixture.store, "other", number, false);
        let excess = alloc_fresh_property_object(&mut fixture.store, vec![required, unrelated]);

        assert_eq!(fixture.store.is_type_assignable_to(valid, target), Ok(true));
        assert_eq!(
            fixture.store.is_type_assignable_to(wrong, target),
            Ok(false)
        );
        assert_eq!(
            fixture.store.is_type_assignable_to(excess, target),
            Ok(false)
        );
        assert_eq!(fixture.store.is_type_assignable_to(target, same), Ok(true));
    }

    #[test]
    fn merged_interface_indexes_accept_properties_from_every_declaration() {
        let mut fixture = function_relation_fixture(concat!(
            "interface Attributes { label: string; } ",
            "interface Attributes { [name: `do-${string}`]: number; }",
        ));
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let symbol = fixture
            .store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("Attributes"))
            .unwrap();
        let host = relation_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let target = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(symbol)
        .unwrap();
        assert!(diagnostics.is_empty());
        let (string, number) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let required = alloc_typed_property(&mut fixture.store, "label", string, false);
        let matching = alloc_typed_property(&mut fixture.store, "do-save", number, false);
        let source = alloc_fresh_property_object(&mut fixture.store, vec![required, matching]);

        assert_eq!(
            fixture.store.is_type_assignable_to(source, target),
            Ok(true)
        );
    }

    #[test]
    fn warmed_structured_relation_observes_the_target_members_table() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source_property = alloc_typed_property(&mut store, "value", string, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let target_property = alloc_typed_property(&mut store, "value", string, false);
        let target = alloc_property_object(&mut store, vec![target_property]);
        let target_members = store
            .type_payload(target)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .unwrap();

        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        let root_key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        let extra = alloc_typed_property(&mut store, "extra", string, false);
        assert_eq!(
            store.insert_symbol(target_members, EscapedName::source("extra"), extra),
            Some(None)
        );
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE
        );
        let stale = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::InvalidStructuredMembers(target))
        );
        assert_eq!(
            store.relation_state_snapshot(),
            stale,
            "failed table revalidation must not publish a replacement relation"
        );
    }

    #[test]
    fn fresh_object_literals_check_excess_properties_before_structural_width() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let stale_x = alloc_typed_property(&mut store, "x", string, false);
        let stale_y = alloc_typed_property(&mut store, "y", number, false);
        let stale = alloc_property_object(&mut store, vec![stale_x, stale_y]);
        let target_x = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_x]);
        assert_eq!(store.is_type_assignable_to(stale, target), Ok(true));

        let fresh_x = alloc_typed_property(&mut store, "x", string, false);
        let fresh_y = alloc_typed_property(&mut store, "y", number, false);
        let fresh = alloc_fresh_property_object(&mut store, vec![fresh_x, fresh_y]);
        let before_excess = store.relation_state_snapshot();
        assert_eq!(store.is_type_assignable_to(fresh, target), Ok(false));
        assert_eq!(
            store.relation_state_snapshot(),
            before_excess,
            "an excess-property failure precedes recursive cache publication"
        );

        let matching_x = alloc_typed_property(&mut store, "x", string, false);
        let matching = alloc_fresh_property_object(&mut store, vec![matching_x]);
        assert_eq!(store.is_type_assignable_to(matching, target), Ok(true));

        let empty = alloc_property_object(&mut store, Vec::new());
        assert_eq!(
            store.is_type_assignable_to(fresh, empty),
            Ok(true),
            "the pinned empty-object target remains open to fresh literals"
        );

        let mut global_target = initialized(true);
        let string = global_target.intrinsic_bootstrap().unwrap().string_type;
        let global_property = alloc_typed_property(&mut global_target, "toString", string, false);
        let global_object = alloc_property_object(&mut global_target, vec![global_property]);
        install_global_object(&mut global_target, global_object);
        let fresh_property = alloc_typed_property(&mut global_target, "x", string, false);
        let fresh = alloc_fresh_property_object(&mut global_target, vec![fresh_property]);
        assert_eq!(
            global_target.is_type_assignable_to(fresh, global_object),
            Ok(true),
            "the exact global Object target is exempt from excess-property checks"
        );
    }

    #[test]
    fn fresh_union_sources_accept_properties_known_in_different_matching_constituents() {
        let mut fixture = function_relation_fixture(
            "type Thing = { str: \"a\"; num: 0 } | { str: \"b\" } | { num: 1 };",
        );
        let target = query_type_alias(&mut fixture, "Thing");
        let str_b = fixture
            .store
            .regular_string_literal_type("b".into())
            .unwrap();
        let num_one = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let str_property = alloc_typed_property(&mut fixture.store, "str", str_b, false);
        let num_property = alloc_typed_property(&mut fixture.store, "num", num_one, false);
        let source =
            alloc_fresh_property_object(&mut fixture.store, vec![str_property, num_property]);

        assert_eq!(
            fixture.store.is_type_assignable_to(source, target),
            Ok(true)
        );
        let warm = fixture.store.relation_state_snapshot();
        assert_eq!(
            fixture.store.is_type_assignable_to(source, target),
            Ok(true)
        );
        assert_eq!(fixture.store.relation_state_snapshot(), warm);
    }

    #[test]
    fn fresh_union_excess_checks_use_the_matching_discriminated_constituent() {
        let mut fixture = function_relation_fixture(
            "type Item = { kind: \"a\"; subkind: 0; value: string } \
             | { kind: \"a\"; subkind: 1; value: number } | { kind: \"b\" };",
        );
        let target = query_type_alias(&mut fixture, "Item");
        let kind_b = fixture
            .store
            .regular_string_literal_type("b".into())
            .unwrap();
        let subkind_one = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let subkind = alloc_typed_property(&mut fixture.store, "subkind", subkind_one, false);
        let kind = alloc_typed_property(&mut fixture.store, "kind", kind_b, false);
        let source = alloc_fresh_property_object(&mut fixture.store, vec![subkind, kind]);
        let before = fixture.store.relation_state_snapshot();

        assert_eq!(
            fixture.store.is_type_assignable_to(source, target),
            Ok(false)
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
    }

    #[test]
    fn fresh_excess_uses_the_combined_target_intersection_surface() {
        let mut fixture = function_relation_fixture(
            "type Left = { a: string }; \
             type Right = { b: string }; \
             type Target = Left & Right;",
        );
        let target = query_type_alias(&mut fixture, "Target");
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let a = alloc_typed_property(&mut fixture.store, "a", string, false);
        let b = alloc_typed_property(&mut fixture.store, "b", string, false);
        let extra = alloc_typed_property(&mut fixture.store, "extra", string, false);
        let source = alloc_fresh_property_object(&mut fixture.store, vec![a, b, extra]);
        let before = fixture.store.relation_state_snapshot();

        assert_eq!(
            fixture.store.is_type_assignable_to(source, target),
            Ok(false),
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
        assert_eq!(
            fixture.store.is_type_comparable_to(source, target),
            Ok(false),
        );
        assert_eq!(fixture.store.relation_state_snapshot(), before);
    }

    #[test]
    fn object_literal_properties_require_checker_owned_source_clones() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let raw_seed = alloc_typed_property(&mut store, "x", string, false);
        let fixture = alloc_fresh_property_object_fixture(&mut store, vec![raw_seed]);
        let source = fixture.type_;
        let owner = fixture.owner;
        let raw = fixture.raw_properties[0];
        let property = fixture.properties[0];
        let source_members = store
            .type_payload(source)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .unwrap();

        let record = store.symbol(property).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
        );
        assert_eq!(record.check_flags(), CheckFlags::NONE);
        assert_eq!(record.parent(), Some(owner));
        assert_eq!(
            record.declarations(),
            store.symbol(raw).unwrap().declarations()
        );
        assert_eq!(
            record.value_declaration(),
            store.symbol(raw).unwrap().value_declaration()
        );
        assert_eq!(
            store.value_symbol_links(property),
            Some(&ValueSymbolLinks {
                resolved_type: Some(string),
                target: Some(raw),
                ..ValueSymbolLinks::default()
            })
        );
        assert!(
            store
                .value_symbol_links(raw)
                .is_some_and(|links| links == &ValueSymbolLinks::default())
        );

        let target_property = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_property]);
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));

        let raw_members = store.symbol(owner).unwrap().members().unwrap();
        let raw_source = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS
                    | ObjectFlags::OBJECT_LITERAL
                    | ObjectFlags::FRESH_LITERAL
                    | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL,
                Some(owner),
            )
            .unwrap();
        assert!(store.set_structured_type_members(
            raw_source,
            Some(raw_members),
            Some(vec![raw]),
            None,
            None,
            None,
        ));
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(raw_source, target),
            Err(RelationUnavailable::UnsupportedProperty(raw))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let ordinary_source_property = alloc_typed_property(&mut store, "x", string, false);
        let ordinary_source = alloc_property_object(&mut store, vec![ordinary_source_property]);
        let object_literal_shaped_target = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(owner))
            .unwrap();
        assert!(store.set_structured_type_members(
            object_literal_shaped_target,
            Some(source_members),
            Some(vec![property]),
            None,
            None,
            None,
        ));
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(ordinary_source, object_literal_shaped_target),
            Err(RelationUnavailable::UnsupportedProperty(property))
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn cached_regular_and_widened_object_literals_relate_cold_and_warm() {
        let mut store = initialized(false);
        let (undefined_widening, any) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.undefined_widening_type, bootstrap.any_type)
        };
        let raw_seed = alloc_typed_property(&mut store, "value", undefined_widening, false);
        let fixture = alloc_fresh_property_object_fixture(&mut store, vec![raw_seed]);
        let regular = store
            .get_regular_type_of_object_literal(fixture.type_)
            .unwrap();
        let widened = store.get_widened_type(regular).unwrap();
        assert_ne!(regular, fixture.type_);
        assert_ne!(widened, regular);

        let regular_property = store
            .type_payload(regular)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_deref())
            .and_then(|properties| properties.first())
            .copied()
            .unwrap();
        let widened_property = store
            .type_payload(widened)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_deref())
            .and_then(|properties| properties.first())
            .copied()
            .unwrap();
        assert_eq!(regular_property, fixture.properties[0]);
        assert_eq!(
            store
                .value_symbol_links(regular_property)
                .and_then(|links| links.target),
            Some(fixture.raw_properties[0])
        );
        assert_eq!(
            store
                .value_symbol_links(widened_property)
                .and_then(|links| links.target),
            Some(regular_property)
        );

        let target_property = alloc_typed_property(&mut store, "value", any, false);
        let target = alloc_property_object(&mut store, vec![target_property]);
        assert_eq!(store.is_type_assignable_to(regular, target), Ok(true));
        let regular_warm = store.relation_state_snapshot();
        assert_eq!(store.is_type_assignable_to(regular, target), Ok(true));
        assert_eq!(store.relation_state_snapshot(), regular_warm);

        assert_eq!(store.is_type_assignable_to(widened, target), Ok(true));
        let widened_warm = store.relation_state_snapshot();
        assert_eq!(store.is_type_assignable_to(widened, target), Ok(true));
        assert_eq!(store.relation_state_snapshot(), widened_warm);
        assert_eq!(store.is_type_comparable_to(target, widened), Ok(true));
        assert_eq!(store.is_type_comparable_to(widened, target), Ok(true));
    }

    #[test]
    fn resolved_own_property_returns_declared_optionality_and_no_fallback() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let property = alloc_typed_property(&mut store, "value", string, true);
        let object = alloc_property_object(&mut store, vec![property]);

        assert_eq!(
            store.resolved_own_property(object, "value"),
            Ok(Some(ResolvedOwnProperty {
                symbol: property,
                type_: string,
                optional: true,
                readonly: false,
            }))
        );
        assert_eq!(store.resolved_own_property(object, "missing"), Ok(None));
    }

    #[test]
    fn resolved_own_property_accepts_validated_fresh_regular_and_widened_literals() {
        let mut store = initialized(false);
        let (undefined_widening, any) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.undefined_widening_type, bootstrap.any_type)
        };
        let raw_seed = alloc_typed_property(&mut store, "value", undefined_widening, false);
        let fixture = alloc_fresh_property_object_fixture(&mut store, vec![raw_seed]);
        let regular = store
            .get_regular_type_of_object_literal(fixture.type_)
            .unwrap();
        let widened = store.get_widened_type(regular).unwrap();

        let fresh = store
            .resolved_own_property(fixture.type_, "value")
            .unwrap()
            .unwrap();
        let regular_property = store
            .resolved_own_property(regular, "value")
            .unwrap()
            .unwrap();
        let widened_property = store
            .resolved_own_property(widened, "value")
            .unwrap()
            .unwrap();
        assert_eq!(fresh.symbol, fixture.properties[0]);
        assert_eq!(fresh.type_, undefined_widening);
        assert_eq!(regular_property.symbol, fixture.properties[0]);
        assert_eq!(regular_property.type_, undefined_widening);
        assert_ne!(widened_property.symbol, fixture.properties[0]);
        assert_eq!(widened_property.type_, any);
        assert!(!fresh.optional && !regular_property.optional && !widened_property.optional);
    }

    #[test]
    fn resolved_own_property_rejects_union_and_primitive_receivers() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let union = canonical_union(&mut store, &[string, number]);

        assert_eq!(
            store.resolved_own_property(union, "value"),
            Err(RelationUnavailable::UnsupportedStructuredType(union))
        );
        assert_eq!(
            store.resolved_own_property(string, "length"),
            Err(RelationUnavailable::UnsupportedStructuredType(string))
        );
    }

    #[test]
    fn poisoned_derived_property_clone_chain_is_retryable() {
        let mut store = initialized(false);
        let (undefined_widening, any) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.undefined_widening_type, bootstrap.any_type)
        };
        let raw_seed = alloc_typed_property(&mut store, "value", undefined_widening, false);
        let fixture = alloc_fresh_property_object_fixture(&mut store, vec![raw_seed]);
        let regular = store
            .get_regular_type_of_object_literal(fixture.type_)
            .unwrap();
        let widened = store.get_widened_type(regular).unwrap();
        let widened_property = store
            .type_payload(widened)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_deref())
            .and_then(|properties| properties.first())
            .copied()
            .unwrap();
        let correct_links = store.value_symbol_links(widened_property).unwrap().clone();
        let target_property = alloc_typed_property(&mut store, "value", any, false);
        let target = alloc_property_object(&mut store, vec![target_property]);

        assert_eq!(store.is_type_assignable_to(widened, target), Ok(true));
        let root_key = store
            .relation_key_if_available(
                widened,
                target,
                super::IntersectionState::NONE,
                false,
                false,
            )
            .unwrap()
            .key();
        assert!(store.set_value_symbol_links(
            widened_property,
            ValueSymbolLinks {
                resolved_type: Some(any),
                target: Some(fixture.raw_properties[0]),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, root_key),
            RelationComparisonResult::NONE,
            "the warmed relation observed the nested derived clone chain"
        );
        let poisoned = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(widened, target),
            Err(RelationUnavailable::InvalidStructuredMembers(widened))
        );
        assert_eq!(store.relation_state_snapshot(), poisoned);

        assert!(store.set_value_symbol_links(widened_property, correct_links));
        assert_eq!(store.is_type_assignable_to(widened, target), Ok(true));
    }

    #[test]
    fn object_literal_clone_target_poison_is_retryable() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let raw_seed = alloc_typed_property(&mut store, "x", string, false);
        let fixture = alloc_fresh_property_object_fixture(&mut store, vec![raw_seed]);
        let property = fixture.properties[0];
        let raw = fixture.raw_properties[0];
        let target_property = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_property]);

        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, target),
            Err(RelationUnavailable::UnsupportedProperty(property))
        );
        assert_eq!(store.relation_state_snapshot(), poisoned);

        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(string),
                target: Some(raw),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(store.is_type_assignable_to(fixture.type_, target), Ok(true));
    }

    #[test]
    fn object_literal_clone_metadata_poison_is_retryable() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let raw_seed = alloc_typed_property(&mut store, "x", string, false);
        let fixture = alloc_fresh_property_object_fixture(&mut store, vec![raw_seed]);
        let property = fixture.properties[0];
        let target_property = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_property]);

        assert!(store.set_symbol_flags(
            property,
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        let poisoned = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, target),
            Err(RelationUnavailable::UnsupportedProperty(property))
        );
        assert_eq!(store.relation_state_snapshot(), poisoned);

        assert!(store.set_symbol_flags(
            property,
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        assert_eq!(store.is_type_assignable_to(fixture.type_, target), Ok(true));
    }

    #[test]
    fn object_literal_propagating_flag_poison_is_retryable() {
        let mut store = initialized(false);
        let undefined_widening = store.intrinsic_bootstrap().unwrap().undefined_widening_type;
        let raw_seed = alloc_typed_property(&mut store, "value", undefined_widening, false);
        let fixture = alloc_fresh_property_object_fixture(&mut store, vec![raw_seed]);
        let expected_flags = store.type_payload(fixture.type_).unwrap().object_flags();
        assert!(expected_flags.contains(ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL));
        assert!(expected_flags.contains(ObjectFlags::CONTAINS_WIDENING_TYPE));

        let first_target_property =
            alloc_typed_property(&mut store, "value", undefined_widening, false);
        let first_target = alloc_property_object(&mut store, vec![first_target_property]);
        assert!(store.set_type_object_flags(
            fixture.type_,
            expected_flags & !ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL,
        ));
        let missing_base_flag = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, first_target),
            Err(RelationUnavailable::UnsupportedStructuredType(
                fixture.type_
            ))
        );
        assert_eq!(store.relation_state_snapshot(), missing_base_flag);
        assert!(store.set_type_object_flags(fixture.type_, expected_flags));
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, first_target),
            Ok(true)
        );

        let second_target_property =
            alloc_typed_property(&mut store, "value", undefined_widening, false);
        let second_target = alloc_property_object(&mut store, vec![second_target_property]);
        assert!(store.set_type_object_flags(
            fixture.type_,
            expected_flags & !ObjectFlags::CONTAINS_WIDENING_TYPE,
        ));
        let missing_propagated_flag = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, second_target),
            Err(RelationUnavailable::UnsupportedStructuredType(
                fixture.type_
            ))
        );
        assert_eq!(store.relation_state_snapshot(), missing_propagated_flag);
        assert!(store.set_type_object_flags(fixture.type_, expected_flags));
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, second_target),
            Ok(true)
        );
    }

    #[test]
    fn object_literal_plain_object_tail_poison_is_retryable() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let raw_seed = alloc_typed_property(&mut store, "x", string, false);
        let fixture = alloc_fresh_property_object_fixture(&mut store, vec![raw_seed]);
        let target_property = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_property]);

        assert!(store.set_object_target_and_mapper(fixture.type_, Some(target), None));
        let poisoned = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, target),
            Err(RelationUnavailable::UnsupportedStructuredType(
                fixture.type_
            ))
        );
        assert_eq!(store.relation_state_snapshot(), poisoned);

        assert!(store.set_object_target_and_mapper(fixture.type_, None, None));
        assert_eq!(store.is_type_assignable_to(fixture.type_, target), Ok(true));
    }

    #[test]
    fn object_literal_raw_member_omission_is_retryable() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let raw_x = alloc_typed_property(&mut store, "x", string, false);
        let raw_y = alloc_typed_property(&mut store, "y", string, false);
        let fixture = alloc_fresh_property_object_fixture(&mut store, vec![raw_x, raw_y]);
        let complete_members = store
            .type_payload(fixture.type_)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .unwrap();
        let incomplete_members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(
                incomplete_members,
                EscapedName::source("x"),
                fixture.properties[0],
            ),
            Some(None)
        );
        assert!(store.set_structured_type_members(
            fixture.type_,
            Some(incomplete_members),
            Some(vec![fixture.properties[0]]),
            None,
            None,
            None,
        ));
        let target_x = alloc_typed_property(&mut store, "x", string, false);
        let target_y = alloc_typed_property(&mut store, "y", string, false);
        let target = alloc_property_object(&mut store, vec![target_x, target_y]);

        let poisoned = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, target),
            Err(RelationUnavailable::InvalidStructuredMembers(fixture.type_))
        );
        assert_eq!(store.relation_state_snapshot(), poisoned);

        assert!(store.set_structured_type_members(
            fixture.type_,
            Some(complete_members),
            Some(fixture.properties.clone()),
            None,
            None,
            None,
        ));
        assert_eq!(store.is_type_assignable_to(fixture.type_, target), Ok(true));
    }

    #[test]
    fn empty_object_literal_owner_and_tables_are_retryable() {
        let mut store = initialized(true);
        let fixture = alloc_fresh_property_object_fixture(&mut store, Vec::new());
        assert!(store.symbol(fixture.owner).unwrap().members().is_none());
        let structured_members = store
            .type_payload(fixture.type_)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .unwrap();
        let first_target = alloc_property_object(&mut store, Vec::new());

        assert!(store.set_type_symbol(fixture.type_, None));
        let missing_owner = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, first_target),
            Err(RelationUnavailable::UnsupportedStructuredType(
                fixture.type_
            ))
        );
        assert_eq!(store.relation_state_snapshot(), missing_owner);
        assert!(store.set_type_symbol(fixture.type_, Some(fixture.owner)));

        let invalid_parent = alloc_symbol(&mut store, SymbolFlags::OBJECT_LITERAL, "parent");
        assert!(store.set_symbol_relationships(
            fixture.owner,
            None,
            None,
            Some(invalid_parent),
            None,
        ));
        let parent_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, first_target),
            Err(RelationUnavailable::InvalidStructuredMembers(fixture.type_))
        );
        assert_eq!(store.relation_state_snapshot(), parent_poison);
        assert!(store.set_symbol_relationships(fixture.owner, None, None, None, None));

        let unexpected_raw_table = store.alloc_symbol_table();
        assert!(store.set_symbol_relationships(
            fixture.owner,
            Some(unexpected_raw_table),
            None,
            None,
            None,
        ));
        let raw_table_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, first_target),
            Err(RelationUnavailable::InvalidStructuredMembers(fixture.type_))
        );
        assert_eq!(store.relation_state_snapshot(), raw_table_poison);
        assert!(store.set_symbol_relationships(fixture.owner, None, None, None, None));
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, first_target),
            Ok(true)
        );

        let second_target = alloc_property_object(&mut store, Vec::new());
        assert!(store.set_structured_type_members(fixture.type_, None, None, None, None, None,));
        let missing_structured_table = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, second_target),
            Err(RelationUnavailable::InvalidStructuredMembers(fixture.type_))
        );
        assert_eq!(store.relation_state_snapshot(), missing_structured_table);
        assert!(store.set_structured_type_members(
            fixture.type_,
            Some(structured_members),
            None,
            None,
            None,
            None,
        ));
        assert_eq!(
            store.is_type_assignable_to(fixture.type_, second_target),
            Ok(true)
        );
    }

    #[test]
    fn canonical_direct_type_literal_aliases_are_transparent_and_poison_forms_fail_closed() {
        let parsed = parse_source_file("type Shape = { x: string };");
        let scope = AstScope::new(FileId::new(0), &parsed.arena);
        let node_of_kind = |kind| {
            let (node, _) = parsed
                .arena
                .iter()
                .find(|(_, node)| node.kind == kind)
                .unwrap_or_else(|| panic!("fixture is missing {kind:?}"));
            scope.node_ref(node).unwrap()
        };
        let alias_declaration = node_of_kind(SyntaxKind::TypeAliasDeclaration);
        let type_literal = node_of_kind(SyntaxKind::TypeLiteral);
        let property_declaration = node_of_kind(SyntaxKind::PropertyDeclaration);

        let mut store = initialized(true);
        assert!(store.register_ast_scope(scope));
        let string = store.intrinsic_bootstrap().unwrap().string_type;

        let mut owner_data = SymbolData::new(
            SymbolFlags::TYPE_LITERAL,
            EscapedName::internal(InternalSymbolName::Type),
        );
        owner_data.declarations = Some(vec![type_literal]);
        let owner = store.alloc_symbol(owner_data).unwrap();
        let mut property_data = SymbolData::new(SymbolFlags::PROPERTY, EscapedName::source("x"));
        property_data.declarations = Some(vec![property_declaration]);
        property_data.value_declaration = Some(property_declaration);
        property_data.parent = Some(owner);
        let property = store.alloc_symbol(property_data).unwrap();
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source("x"), property),
            Some(None)
        );
        assert!(store.set_symbol_relationships(owner, Some(members), None, None, None,));
        let shape = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(owner))
            .unwrap();
        assert!(store.set_structured_type_members(
            shape,
            Some(members),
            Some(vec![property]),
            None,
            None,
            None,
        ));

        let mut alias_data = SymbolData::new(SymbolFlags::TYPE_ALIAS, EscapedName::source("Shape"));
        alias_data.declarations = Some(vec![alias_declaration]);
        let alias_symbol = store.alloc_symbol(alias_data).unwrap();
        attach_direct_type_alias(&mut store, shape, Some(alias_symbol), None, Some(shape));

        let fresh_property = alloc_typed_property(&mut store, "x", string, false);
        let fresh = alloc_fresh_property_object(&mut store, vec![fresh_property]);
        assert_eq!(
            store.is_type_assignable_to(fresh, shape),
            Ok(true),
            "direct alias metadata is display provenance, not a structural boundary"
        );
        let plain_property = alloc_typed_property(&mut store, "x", string, false);
        let plain = alloc_property_object(&mut store, vec![plain_property]);
        assert_eq!(store.is_type_assignable_to(shape, plain), Ok(true));
        let alias_key = store
            .relation_key_if_available(shape, plain, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, alias_key)
                .intersects(RelationComparisonResult::SUCCEEDED)
        );
        let exact_alias_links = store.type_alias_links(alias_symbol).unwrap().clone();
        assert!(
            store.set_type_alias_links(alias_symbol, exact_alias_links.clone()),
            "an equal link publication remains an accepted no-op"
        );
        let warmed_alias_relations = store.relation_state_snapshot();
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, alias_key)
                .intersects(RelationComparisonResult::SUCCEEDED),
            "an equal link publication must not stale a warmed relation"
        );
        let foreign = initialized(true);
        let foreign_type = foreign.intrinsic_bootstrap().unwrap().string_type;
        let mut rejected_alias_links = exact_alias_links.clone();
        rejected_alias_links.declared_type = Some(foreign_type);
        assert!(!store.set_type_alias_links(alias_symbol, rejected_alias_links));
        assert_eq!(store.relation_state_snapshot(), warmed_alias_relations);
        assert!(
            store
                .relation_cache_get(RelationKind::Assignable, alias_key)
                .intersects(RelationComparisonResult::SUCCEEDED),
            "a rejected link publication must not stale a warmed relation"
        );
        let mut wrong_alias_links = exact_alias_links;
        wrong_alias_links.declared_type = Some(plain);
        assert!(store.set_type_alias_links(alias_symbol, wrong_alias_links));
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, alias_key),
            RelationComparisonResult::NONE,
        );
        assert_eq!(
            store.is_type_assignable_to(shape, plain),
            Err(RelationUnavailable::UnsupportedStructuredType(shape))
        );
        assert_eq!(
            store.relation_state_snapshot(),
            warmed_alias_relations,
            "a rejected warmed alias query must not publish relation writes"
        );

        let transient_shape = alloc_synthetic_type_literal_object(&mut store, string);
        let transient_alias_symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("TransientShape"),
            CheckFlags::NONE,
        );
        assert_eq!(
            store.symbol(transient_alias_symbol).unwrap().flags(),
            SymbolFlags::TYPE_ALIAS | SymbolFlags::TRANSIENT
        );
        attach_direct_type_alias(
            &mut store,
            transient_shape,
            Some(transient_alias_symbol),
            None,
            Some(transient_shape),
        );
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(fresh, transient_shape),
            Err(RelationUnavailable::UnsupportedStructuredType(
                transient_shape
            ))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let allocated_empty_arguments = alloc_synthetic_type_literal_object(&mut store, string);
        let generic_symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_ALIAS, "Generic");
        attach_direct_type_alias(
            &mut store,
            allocated_empty_arguments,
            Some(generic_symbol),
            Some(Vec::new()),
            Some(allocated_empty_arguments),
        );

        let missing_symbol = alloc_synthetic_type_literal_object(&mut store, string);
        attach_direct_type_alias(&mut store, missing_symbol, None, None, None);

        let wrong_alias_flags = alloc_synthetic_type_literal_object(&mut store, string);
        let interface_symbol = alloc_symbol(&mut store, SymbolFlags::INTERFACE, "NotAlias");
        attach_direct_type_alias(
            &mut store,
            wrong_alias_flags,
            Some(interface_symbol),
            None,
            Some(wrong_alias_flags),
        );

        let merged_value_alias = alloc_synthetic_type_literal_object(&mut store, string);
        let merged_value_alias_symbol = alloc_symbol(
            &mut store,
            SymbolFlags::TYPE_ALIAS | SymbolFlags::VALUE_MODULE,
            "MergedValueAlias",
        );
        attach_direct_type_alias(
            &mut store,
            merged_value_alias,
            Some(merged_value_alias_symbol),
            None,
            Some(merged_value_alias),
        );

        let malformed_alias_merge = alloc_synthetic_type_literal_object(&mut store, string);
        let mixed_alias_symbol = alloc_symbol(
            &mut store,
            SymbolFlags::TYPE_ALIAS | SymbolFlags::ALIAS,
            "MixedAlias",
        );
        attach_direct_type_alias(
            &mut store,
            malformed_alias_merge,
            Some(mixed_alias_symbol),
            None,
            Some(malformed_alias_merge),
        );

        let mismatched_declared_type = alloc_synthetic_type_literal_object(&mut store, string);
        let mismatch_symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_ALIAS, "Mismatch");
        attach_direct_type_alias(
            &mut store,
            mismatched_declared_type,
            Some(mismatch_symbol),
            None,
            Some(plain),
        );

        let wrong_owner_property = alloc_typed_property(&mut store, "x", string, false);
        let wrong_owner = alloc_property_object(&mut store, vec![wrong_owner_property]);
        let wrong_owner_symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_ALIAS, "WrongOwner");
        attach_direct_type_alias(
            &mut store,
            wrong_owner,
            Some(wrong_owner_symbol),
            None,
            Some(wrong_owner),
        );

        let aliased_interface_symbol =
            alloc_symbol(&mut store, SymbolFlags::INTERFACE, "AliasedInterface");
        let aliased_interface = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(aliased_interface_symbol))
            .unwrap();
        let interface_property = alloc_typed_property(&mut store, "x", string, false);
        set_object_properties(&mut store, aliased_interface, vec![interface_property]);
        let interface_alias_symbol =
            alloc_symbol(&mut store, SymbolFlags::TYPE_ALIAS, "InterfaceAlias");
        attach_direct_type_alias(
            &mut store,
            aliased_interface,
            Some(interface_alias_symbol),
            None,
            Some(aliased_interface),
        );

        for poisoned in [
            allocated_empty_arguments,
            missing_symbol,
            wrong_alias_flags,
            merged_value_alias,
            malformed_alias_merge,
            mismatched_declared_type,
            wrong_owner,
            aliased_interface,
        ] {
            let before = store.relation_state_snapshot();
            assert_eq!(
                store.is_type_assignable_to(plain, poisoned),
                Err(RelationUnavailable::UnsupportedStructuredType(poisoned))
            );
            assert_eq!(store.relation_state_snapshot(), before);
        }
    }

    #[test]
    fn direct_type_literal_alias_owner_provenance_poison_is_retryable() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let shape = alloc_synthetic_type_literal_object(&mut store, string);
        let owner = store.type_payload(shape).unwrap().symbol().unwrap();
        let owner_record = store.symbol(owner).unwrap();
        let owner_members = owner_record.members();
        let owner_declaration = owner_record.declarations().unwrap()[0];
        let alias_symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_ALIAS, "Shape");
        attach_direct_type_alias(&mut store, shape, Some(alias_symbol), None, Some(shape));

        let source_property = alloc_typed_property(&mut store, "x", string, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let invalid_parent = alloc_symbol(&mut store, SymbolFlags::TYPE_LITERAL, "parent");
        assert!(store.set_symbol_relationships(
            owner,
            owner_members,
            None,
            Some(invalid_parent),
            None,
        ));
        let parent_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, shape),
            Err(RelationUnavailable::UnsupportedStructuredType(shape))
        );
        assert_eq!(store.relation_state_snapshot(), parent_poison);
        assert!(store.set_symbol_relationships(owner, owner_members, None, None, None));
        assert_eq!(store.is_type_assignable_to(source, shape), Ok(true));

        let source_property = alloc_typed_property(&mut store, "x", string, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let exports = store.alloc_symbol_table();
        assert!(store.set_symbol_relationships(owner, owner_members, Some(exports), None, None,));
        let exports_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, shape),
            Err(RelationUnavailable::UnsupportedStructuredType(shape))
        );
        assert_eq!(store.relation_state_snapshot(), exports_poison);
        assert!(store.set_symbol_relationships(owner, owner_members, None, None, None));
        assert_eq!(store.is_type_assignable_to(source, shape), Ok(true));

        let source_property = alloc_typed_property(&mut store, "x", string, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let export_symbol = alloc_symbol(&mut store, SymbolFlags::TYPE_ALIAS, "export");
        assert!(store.set_symbol_relationships(
            owner,
            owner_members,
            None,
            None,
            Some(export_symbol),
        ));
        let export_symbol_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, shape),
            Err(RelationUnavailable::UnsupportedStructuredType(shape))
        );
        assert_eq!(store.relation_state_snapshot(), export_symbol_poison);
        assert!(store.set_symbol_relationships(owner, owner_members, None, None, None));
        assert_eq!(store.is_type_assignable_to(source, shape), Ok(true));

        let source_property = alloc_typed_property(&mut store, "x", string, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        assert!(store.set_symbol_declarations(owner, None, None));
        let declarations_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, shape),
            Err(RelationUnavailable::UnsupportedStructuredType(shape))
        );
        assert_eq!(store.relation_state_snapshot(), declarations_poison);
        assert!(store.set_symbol_declarations(owner, Some(vec![owner_declaration]), None,));
        assert_eq!(store.is_type_assignable_to(source, shape), Ok(true));

        let source_property = alloc_typed_property(&mut store, "x", string, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        assert!(store.set_symbol_declarations(
            owner,
            Some(vec![owner_declaration]),
            Some(owner_declaration),
        ));
        let value_declaration_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, shape),
            Err(RelationUnavailable::UnsupportedStructuredType(shape))
        );
        assert_eq!(store.relation_state_snapshot(), value_declaration_poison);
        assert!(store.set_symbol_declarations(owner, Some(vec![owner_declaration]), None,));
        assert_eq!(store.is_type_assignable_to(source, shape), Ok(true));
    }

    #[test]
    fn fresh_excess_precedes_weak_checks_and_target_freshness_stays_typed() {
        let mut ordered = initialized(true);
        let string = ordered.intrinsic_bootstrap().unwrap().string_type;
        let globals = ordered.intrinsic_bootstrap().unwrap().globals;
        let object_symbol = alloc_symbol(&mut ordered, SymbolFlags::INTERFACE, "Object");
        assert_eq!(
            ordered.insert_symbol(globals, EscapedName::source("Object"), object_symbol),
            Some(None)
        );
        let extra = alloc_typed_property(&mut ordered, "extra", string, false);
        let source = alloc_fresh_property_object(&mut ordered, vec![extra]);
        let weak = alloc_typed_property(&mut ordered, "expected", string, true);
        let target = alloc_property_object(&mut ordered, vec![weak]);
        let before = ordered.relation_state_snapshot();
        assert_eq!(ordered.is_type_assignable_to(source, target), Ok(false));
        assert_eq!(ordered.relation_state_snapshot(), before);

        let mut unsupported_target = initialized(true);
        let string = unsupported_target
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        let source_property = alloc_typed_property(&mut unsupported_target, "value", string, false);
        let source = alloc_property_object(&mut unsupported_target, vec![source_property]);
        let target_property = alloc_typed_property(&mut unsupported_target, "value", string, false);
        let target = alloc_fresh_property_object(&mut unsupported_target, vec![target_property]);
        let before = unsupported_target.relation_state_snapshot();
        assert_eq!(
            unsupported_target.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnsupportedStructuredType(target))
        );
        assert_eq!(unsupported_target.relation_state_snapshot(), before);
    }

    #[test]
    fn nested_target_freshness_rolls_back_the_outer_pending_relation() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source_inner_property = alloc_typed_property(&mut store, "value", string, false);
        let source_inner = alloc_property_object(&mut store, vec![source_inner_property]);
        let target_inner_property = alloc_typed_property(&mut store, "value", string, false);
        let target_inner = alloc_fresh_property_object(&mut store, vec![target_inner_property]);
        let source_property = alloc_typed_property(&mut store, "nested", source_inner, false);
        let source = alloc_property_object(&mut store, vec![source_property]);
        let target_property = alloc_typed_property(&mut store, "nested", target_inner, false);
        let target = alloc_property_object(&mut store, vec![target_property]);
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnsupportedStructuredType(target_inner))
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }

    #[test]
    fn ordinary_property_owners_match_the_type_owner_or_none() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;

        let interface_owner = alloc_symbol(&mut store, SymbolFlags::INTERFACE, "Interface");
        let wrong_interface_owner =
            alloc_symbol(&mut store, SymbolFlags::INTERFACE, "WrongInterface");
        let interface = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(interface_owner))
            .unwrap();
        let interface_property = alloc_typed_property(&mut store, "x", string, false);
        assert!(store.set_symbol_relationships(
            interface_property,
            None,
            None,
            Some(wrong_interface_owner),
            None,
        ));
        set_object_properties(&mut store, interface, vec![interface_property]);
        let target_property = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_property]);
        let interface_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(interface, target),
            Err(RelationUnavailable::InvalidStructuredMembers(interface))
        );
        assert_eq!(store.relation_state_snapshot(), interface_poison);
        assert!(store.set_symbol_relationships(
            interface_property,
            None,
            None,
            Some(interface_owner),
            None,
        ));
        assert_eq!(store.is_type_assignable_to(interface, target), Ok(true));

        let type_literal_owner = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_LITERAL,
                EscapedName::internal(InternalSymbolName::Type),
            ))
            .unwrap();
        let wrong_type_literal_owner = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_LITERAL,
                EscapedName::internal(InternalSymbolName::Type),
            ))
            .unwrap();
        let type_literal = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(type_literal_owner))
            .unwrap();
        let type_literal_property = alloc_typed_property(&mut store, "x", string, false);
        assert!(store.set_symbol_relationships(
            type_literal_property,
            None,
            None,
            Some(wrong_type_literal_owner),
            None,
        ));
        set_object_properties(&mut store, type_literal, vec![type_literal_property]);
        let target_property = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_property]);
        let type_literal_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(type_literal, target),
            Err(RelationUnavailable::InvalidStructuredMembers(type_literal))
        );
        assert_eq!(store.relation_state_snapshot(), type_literal_poison);
        assert!(store.set_symbol_relationships(
            type_literal_property,
            None,
            None,
            Some(type_literal_owner),
            None,
        ));
        assert_eq!(store.is_type_assignable_to(type_literal, target), Ok(true));

        let unowned_property = alloc_typed_property(&mut store, "x", string, false);
        assert!(store.set_symbol_relationships(
            unowned_property,
            None,
            None,
            Some(interface_owner),
            None,
        ));
        let unowned = alloc_property_object(&mut store, vec![unowned_property]);
        let target_property = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_property]);
        let unowned_poison = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(unowned, target),
            Err(RelationUnavailable::InvalidStructuredMembers(unowned))
        );
        assert_eq!(store.relation_state_snapshot(), unowned_poison);
        assert!(store.set_symbol_relationships(unowned_property, None, None, None, None));
        assert_eq!(store.is_type_assignable_to(unowned, target), Ok(true));
    }

    #[test]
    fn resolved_interface_properties_use_the_same_structural_path() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source_symbol = alloc_symbol(&mut store, SymbolFlags::INTERFACE, "Source");
        let target_symbol = alloc_symbol(&mut store, SymbolFlags::INTERFACE, "Target");
        let source = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(source_symbol))
            .unwrap();
        let target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(target_symbol))
            .unwrap();
        let source_property = alloc_typed_property(&mut store, "value", string, false);
        let target_property = alloc_typed_property(&mut store, "value", string, false);
        assert!(store.set_symbol_relationships(
            source_property,
            None,
            None,
            Some(source_symbol),
            None,
        ));
        assert!(store.set_symbol_relationships(
            target_property,
            None,
            None,
            Some(target_symbol),
            None,
        ));
        set_object_properties(&mut store, source, vec![source_property]);
        set_object_properties(&mut store, target, vec![target_property]);
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
    }

    #[test]
    fn optional_properties_follow_loose_strict_and_exact_optional_matrices() {
        let mut loose = initialized(false);
        let string = loose.intrinsic_bootstrap().unwrap().string_type;
        let empty = alloc_property_object(&mut loose, Vec::new());
        let optional_target_property = alloc_typed_property(&mut loose, "value", string, true);
        let optional_target = alloc_property_object(&mut loose, vec![optional_target_property]);
        assert_eq!(
            loose.is_type_assignable_to(empty, optional_target),
            Ok(true)
        );

        let optional_source_property = alloc_typed_property(&mut loose, "value", string, true);
        let optional_source = alloc_property_object(&mut loose, vec![optional_source_property]);
        let required_target_property = alloc_typed_property(&mut loose, "value", string, false);
        let required_target = alloc_property_object(&mut loose, vec![required_target_property]);
        assert_eq!(
            loose.is_type_assignable_to(optional_source, required_target),
            Ok(false)
        );

        let required_source_property = alloc_typed_property(&mut loose, "value", string, false);
        let required_source = alloc_property_object(&mut loose, vec![required_source_property]);
        assert_eq!(
            loose.is_type_assignable_to(required_source, optional_target),
            Ok(true)
        );

        let mut strict = initialized(true);
        let (string, undefined) = {
            let bootstrap = strict.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_type)
        };
        let empty = alloc_property_object(&mut strict, Vec::new());
        let optional_target_property = alloc_typed_property(&mut strict, "value", string, true);
        let optional_target = alloc_property_object(&mut strict, vec![optional_target_property]);
        assert_eq!(
            strict.is_type_assignable_to(empty, optional_target),
            Ok(true),
            "an absent optional remains exact after global Object lookup"
        );

        let required_source_property = alloc_typed_property(&mut strict, "value", string, false);
        let required_source = alloc_property_object(&mut strict, vec![required_source_property]);
        assert_eq!(
            strict.is_type_assignable_to(required_source, optional_target),
            Ok(true)
        );

        let undefined_source_property =
            alloc_typed_property(&mut strict, "value", undefined, false);
        let undefined_source = alloc_property_object(&mut strict, vec![undefined_source_property]);
        assert_eq!(
            strict.is_type_assignable_to(undefined_source, optional_target),
            Ok(true),
            "non-exact optional properties virtually include undefined"
        );

        let optional_source_property = alloc_typed_property(&mut strict, "value", string, true);
        let optional_source = alloc_property_object(&mut strict, vec![optional_source_property]);
        let required_target_property = alloc_typed_property(&mut strict, "value", string, false);
        let required_target = alloc_property_object(&mut strict, vec![required_target_property]);
        assert_eq!(
            strict.is_type_assignable_to(optional_source, required_target),
            Ok(false)
        );

        let mut exact = initialized_with_options(true, true);
        let (string, undefined, missing, never) = {
            let bootstrap = exact.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.undefined_type,
                bootstrap.missing_type,
                bootstrap.never_type,
            )
        };
        let optional_string_property = alloc_typed_property(&mut exact, "value", string, true);
        let optional_string = alloc_property_object(&mut exact, vec![optional_string_property]);
        let required_string_property = alloc_typed_property(&mut exact, "value", string, false);
        let required_string = alloc_property_object(&mut exact, vec![required_string_property]);
        assert_eq!(
            exact.is_type_assignable_to(required_string, optional_string),
            Ok(true)
        );

        let required_undefined_property =
            alloc_typed_property(&mut exact, "value", undefined, false);
        let required_undefined =
            alloc_property_object(&mut exact, vec![required_undefined_property]);
        assert_eq!(
            exact.is_type_assignable_to(required_undefined, optional_string),
            Ok(false),
            "exact optional properties do not add implicit undefined"
        );

        let explicit_undefined = canonical_union(&mut exact, &[undefined, string]);
        let explicit_optional_property =
            alloc_typed_property(&mut exact, "value", explicit_undefined, true);
        let explicit_optional = alloc_property_object(&mut exact, vec![explicit_optional_property]);
        assert_eq!(
            exact.is_type_assignable_to(required_undefined, explicit_optional),
            Ok(true),
            "an explicitly declared undefined remains in the base annotation"
        );

        let stored_optional_property = alloc_typed_property(&mut exact, "value", missing, true);
        let stored_optional = alloc_property_object(&mut exact, vec![stored_optional_property]);
        assert_eq!(
            exact.is_type_assignable_to(required_undefined, stored_optional),
            Ok(false),
            "a directly stored missing sentinel is removed from exact optional comparisons"
        );
        let required_never_property = alloc_typed_property(&mut exact, "value", never, false);
        let required_never = alloc_property_object(&mut exact, vec![required_never_property]);
        assert_eq!(
            exact.is_type_assignable_to(required_never, stored_optional),
            Ok(true),
            "removing a stored missing sentinel leaves the exact never type"
        );

        let optional_source_property = alloc_typed_property(&mut exact, "value", string, true);
        let optional_source = alloc_property_object(&mut exact, vec![optional_source_property]);
        assert_eq!(
            exact.is_type_assignable_to(optional_source, required_string),
            Ok(false)
        );
        assert_eq!(
            exact.is_type_assignable_to(optional_source, optional_string),
            Ok(true)
        );
    }

    #[test]
    fn weak_targets_require_a_common_own_property_before_recursion() {
        for strict_null_checks in [false, true] {
            let mut store = initialized(strict_null_checks);
            let (string, number) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.number_type)
            };
            let source_property = alloc_typed_property(&mut store, "b", number, false);
            let source = alloc_property_object(&mut store, vec![source_property]);
            let target_property = alloc_typed_property(&mut store, "a", string, true);
            let target = alloc_property_object(&mut store, vec![target_property]);

            assert_eq!(store.is_type_assignable_to(source, target), Ok(false));
            assert_eq!(
                store.relation_cache_size(RelationKind::Assignable),
                0,
                "the weak-type check runs before recursive relation caching"
            );
        }

        let mut loose = initialized(false);
        let string = loose.intrinsic_bootstrap().unwrap().string_type;
        let source_property = alloc_typed_property(&mut loose, "a", string, false);
        let source = alloc_property_object(&mut loose, vec![source_property]);
        let target_property = alloc_typed_property(&mut loose, "a", string, true);
        let target = alloc_property_object(&mut loose, vec![target_property]);
        assert_eq!(loose.is_type_assignable_to(source, target), Ok(true));

        let mut unresolved_global = initialized(true);
        let string = unresolved_global.intrinsic_bootstrap().unwrap().string_type;
        let globals = unresolved_global.intrinsic_bootstrap().unwrap().globals;
        let object_symbol = alloc_symbol(&mut unresolved_global, SymbolFlags::INTERFACE, "Object");
        assert_eq!(
            unresolved_global.insert_symbol(globals, EscapedName::source("Object"), object_symbol,),
            Some(None)
        );
        let source_property = alloc_typed_property(&mut unresolved_global, "a", string, false);
        let source = alloc_property_object(&mut unresolved_global, vec![source_property]);
        let target_property = alloc_typed_property(&mut unresolved_global, "a", string, true);
        let target = alloc_property_object(&mut unresolved_global, vec![target_property]);
        assert_eq!(
            unresolved_global.is_type_assignable_to(source, target),
            Ok(true),
            "an unresolved global Object does not poison a common own property"
        );

        for strict_null_checks in [false, true] {
            let mut store = initialized(strict_null_checks);
            let string = store.intrinsic_bootstrap().unwrap().string_type;
            let global_property = alloc_typed_property(&mut store, "a", string, false);
            let global_object = alloc_property_object(&mut store, vec![global_property]);
            install_global_object(&mut store, global_object);

            let source_property = alloc_typed_property(&mut store, "b", string, false);
            let source = alloc_property_object(&mut store, vec![source_property]);
            let target_property = alloc_typed_property(&mut store, "a", string, true);
            let target = alloc_property_object(&mut store, vec![target_property]);
            assert_eq!(
                store.is_type_assignable_to(source, target),
                Ok(false),
                "global Object augmentation is not an own common property"
            );
        }

        let mut loose_global_source = initialized(false);
        let string = loose_global_source
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        let global_property =
            alloc_typed_property(&mut loose_global_source, "global", string, false);
        let global_object = alloc_property_object(&mut loose_global_source, vec![global_property]);
        install_global_object(&mut loose_global_source, global_object);
        let target_property = alloc_typed_property(&mut loose_global_source, "a", string, true);
        let target = alloc_property_object(&mut loose_global_source, vec![target_property]);
        assert_eq!(
            loose_global_source.is_type_assignable_to(global_object, target),
            Ok(true),
            "the canonical global Object source is exempt from the weak-type check"
        );
    }

    #[test]
    fn nested_self_and_mutually_recursive_properties_terminate_and_cache_success() {
        let mut nested = initialized(true);
        let string = nested.intrinsic_bootstrap().unwrap().string_type;
        let source_leaf_property = alloc_typed_property(&mut nested, "value", string, false);
        let source_leaf = alloc_property_object(&mut nested, vec![source_leaf_property]);
        let target_leaf_property = alloc_typed_property(&mut nested, "value", string, false);
        let target_leaf = alloc_property_object(&mut nested, vec![target_leaf_property]);
        let source_nested_property =
            alloc_typed_property(&mut nested, "nested", source_leaf, false);
        let source = alloc_property_object(&mut nested, vec![source_nested_property]);
        let target_nested_property =
            alloc_typed_property(&mut nested, "nested", target_leaf, false);
        let target = alloc_property_object(&mut nested, vec![target_nested_property]);
        assert_eq!(nested.is_type_assignable_to(source, target), Ok(true));
        assert_eq!(
            nested.relation_cache_size(RelationKind::Assignable),
            2,
            "the nested pair and root pair are both published"
        );

        let mut recursive = initialized(true);
        let source = alloc_object_shell(&mut recursive);
        let target = alloc_object_shell(&mut recursive);
        let source_next = alloc_typed_property(&mut recursive, "next", source, false);
        let target_next = alloc_typed_property(&mut recursive, "next", target, false);
        set_object_properties(&mut recursive, source, vec![source_next]);
        set_object_properties(&mut recursive, target, vec![target_next]);
        assert_eq!(recursive.is_type_assignable_to(source, target), Ok(true));
        assert_eq!(
            recursive.relation_cache_size(RelationKind::Assignable),
            1,
            "depth-zero Maybe publishes the active root key"
        );

        let mut mutual = initialized(true);
        let source_left = alloc_object_shell(&mut mutual);
        let source_right = alloc_object_shell(&mut mutual);
        let target_left = alloc_object_shell(&mut mutual);
        let target_right = alloc_object_shell(&mut mutual);
        let source_left_next = alloc_typed_property(&mut mutual, "next", source_right, false);
        let source_right_next = alloc_typed_property(&mut mutual, "next", source_left, false);
        let target_left_next = alloc_typed_property(&mut mutual, "next", target_right, false);
        let target_right_next = alloc_typed_property(&mut mutual, "next", target_left, false);
        set_object_properties(&mut mutual, source_left, vec![source_left_next]);
        set_object_properties(&mut mutual, source_right, vec![source_right_next]);
        set_object_properties(&mut mutual, target_left, vec![target_left_next]);
        set_object_properties(&mut mutual, target_right, vec![target_right_next]);
        assert_eq!(
            mutual.is_type_assignable_to(source_left, target_left),
            Ok(true)
        );
        assert_eq!(mutual.relation_cache_size(RelationKind::Assignable), 2);
    }

    #[test]
    fn recursive_mismatch_turns_assumptions_into_a_directional_failure() {
        let mut store = initialized(true);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let source = alloc_object_shell(&mut store);
        let target = alloc_object_shell(&mut store);
        let source_next = alloc_typed_property(&mut store, "next", source, false);
        let source_value = alloc_typed_property(&mut store, "value", string, false);
        let target_next = alloc_typed_property(&mut store, "next", target, false);
        let target_value = alloc_typed_property(&mut store, "value", number, false);
        set_object_properties(&mut store, source, vec![source_next, source_value]);
        set_object_properties(&mut store, target, vec![target_next, target_value]);

        assert_eq!(store.is_type_assignable_to(source, target), Ok(false));
        let key = store
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert_eq!(
            store.relation_cache_get(RelationKind::Assignable, key),
            RelationComparisonResult::FAILED
        );
    }

    #[test]
    fn structural_cache_is_directional_isolated_and_reused() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source_x = alloc_typed_property(&mut store, "x", string, false);
        let source_y = alloc_typed_property(&mut store, "y", string, false);
        let source = alloc_property_object(&mut store, vec![source_x, source_y]);
        let target_x = alloc_typed_property(&mut store, "x", string, false);
        let target = alloc_property_object(&mut store, vec![target_x]);

        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        let after_first = store.relation_state_snapshot();
        assert_eq!(store.is_type_assignable_to(source, target), Ok(true));
        assert_eq!(store.relation_state_snapshot(), after_first);
        assert_eq!(store.is_type_assignable_to(target, source), Ok(false));
        assert_eq!(store.relation_cache_size(RelationKind::Assignable), 2);
        assert_eq!(store.relation_cache_size(RelationKind::Subtype), 0);
        assert_eq!(store.is_type_subtype_of(source, target), Ok(true));
        assert_eq!(store.relation_cache_size(RelationKind::Subtype), 1);
        let after_subtype = store.relation_state_snapshot();
        assert_eq!(store.is_type_subtype_of(source, target), Ok(true));
        assert_eq!(store.relation_state_snapshot(), after_subtype);
        assert_eq!(store.is_type_strict_subtype_of(source, target), Ok(true));
        assert_eq!(store.relation_cache_size(RelationKind::StrictSubtype), 1);
    }

    #[test]
    fn unavailable_or_malformed_structural_inputs_never_commit_pending_cache_entries() {
        let mut store = initialized(true);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let unresolved = alloc_object_shell(&mut store);
        let target = alloc_property_object(&mut store, Vec::new());
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(unresolved, target),
            Err(RelationUnavailable::UnresolvedStructuredMembers(unresolved))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let source_property = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "value");
        let source = alloc_property_object(&mut store, vec![source_property]);
        let target_property = alloc_typed_property(&mut store, "value", string, false);
        let typed_target = alloc_property_object(&mut store, vec![target_property]);
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, typed_target),
            Err(RelationUnavailable::UnresolvedPropertyType(source_property))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let malformed_property = alloc_typed_property(&mut store, "value", string, false);
        let malformed = alloc_object_shell(&mut store);
        assert!(store.set_structured_type_members(
            malformed,
            None,
            Some(vec![malformed_property]),
            None,
            None,
            None,
        ));
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(malformed, target),
            Err(RelationUnavailable::InvalidStructuredMembers(malformed))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let signature = store
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
            .unwrap();
        let with_signature = alloc_object_shell(&mut store);
        assert!(store.set_structured_type_members(
            with_signature,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(with_signature, target),
            Err(RelationUnavailable::StructuredSignatures(with_signature))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let index = store
            .alloc_index_info(string, string, false, None, Vec::new())
            .unwrap();
        let with_index = alloc_object_shell(&mut store);
        assert!(store.set_structured_type_members(
            with_index,
            None,
            None,
            None,
            None,
            Some(vec![index]),
        ));
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(with_index, target),
            Err(RelationUnavailable::StructuredIndexInfos(with_index))
        );
        assert_eq!(store.relation_state_snapshot(), before);

        let source_leaf = alloc_property_object(&mut store, Vec::new());
        let target_leaf = alloc_property_object(&mut store, Vec::new());
        let source_first = alloc_typed_property(&mut store, "first", source_leaf, false);
        let source_late = alloc_symbol(&mut store, SymbolFlags::PROPERTY, "late");
        let source = alloc_property_object(&mut store, vec![source_first, source_late]);
        let target_first = alloc_typed_property(&mut store, "first", target_leaf, false);
        let target_late = alloc_typed_property(&mut store, "late", string, false);
        let target = alloc_property_object(&mut store, vec![target_first, target_late]);
        let before = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnresolvedPropertyType(source_late))
        );
        assert_eq!(
            store.relation_state_snapshot(),
            before,
            "a later typed boundary discards an earlier nested success"
        );
    }

    #[test]
    fn transformed_object_shapes_are_unsupported_and_atomic_in_both_roles() {
        let mut store = initialized(true);
        let ordinary = alloc_property_object(&mut store, Vec::new());
        for flag in [
            ObjectFlags::CONTAINS_SPREAD,
            ObjectFlags::OBJECT_REST_TYPE,
            ObjectFlags::IS_CLASS_INSTANCE_CLONE,
        ] {
            let transformed = store
                .alloc_plain_object_type(ObjectFlags::ANONYMOUS | flag, None)
                .unwrap();
            assert!(store.set_structured_type_members(transformed, None, None, None, None, None,));

            let before = store.relation_state_snapshot();
            assert_eq!(
                store.is_type_assignable_to(transformed, ordinary),
                Err(RelationUnavailable::UnsupportedStructuredType(transformed))
            );
            assert_eq!(store.relation_state_snapshot(), before);

            let before = store.relation_state_snapshot();
            assert_eq!(
                store.is_type_assignable_to(ordinary, transformed),
                Err(RelationUnavailable::UnsupportedStructuredType(transformed))
            );
            assert_eq!(store.relation_state_snapshot(), before);
        }
    }

    #[test]
    fn global_object_fallback_distinguishes_absent_resolved_and_unresolved_states() {
        let mut absent = initialized(true);
        let string = absent.intrinsic_bootstrap().unwrap().string_type;
        let source = alloc_property_object(&mut absent, Vec::new());
        let target_property = alloc_typed_property(&mut absent, "custom", string, false);
        let target = alloc_property_object(&mut absent, vec![target_property]);
        assert_eq!(absent.is_type_assignable_to(source, target), Ok(false));

        let mut shell_absent = initialized(true);
        let string = shell_absent.intrinsic_bootstrap().unwrap().string_type;
        let globals = shell_absent.intrinsic_bootstrap().unwrap().globals;
        let object_symbol = alloc_symbol(&mut shell_absent, SymbolFlags::INTERFACE, "Object");
        let unrelated = alloc_typed_property(&mut shell_absent, "unrelated", string, false);
        let raw_members = shell_absent.alloc_symbol_table();
        assert_eq!(
            shell_absent.insert_symbol(raw_members, EscapedName::source("unrelated"), unrelated,),
            Some(None)
        );
        assert!(shell_absent.set_symbol_relationships(
            object_symbol,
            Some(raw_members),
            None,
            None,
            None,
        ));
        assert_eq!(
            shell_absent.insert_symbol(globals, EscapedName::source("Object"), object_symbol,),
            Some(None)
        );
        let object_type = shell_absent
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(object_symbol))
            .unwrap();
        assert!(shell_absent.set_declared_type_links(
            object_symbol,
            DeclaredTypeLinks {
                declared_type: Some(object_type),
                ..DeclaredTypeLinks::default()
            },
        ));
        let source = alloc_property_object(&mut shell_absent, Vec::new());
        let target_property = alloc_typed_property(&mut shell_absent, "custom", string, false);
        let target = alloc_property_object(&mut shell_absent, vec![target_property]);
        let before = shell_absent.relation_state_snapshot();
        assert_eq!(
            shell_absent.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnresolvedStructuredMembers(
                object_type
            )),
            "an interface with unresolved bases cannot prove inherited properties absent"
        );
        assert_eq!(shell_absent.relation_state_snapshot(), before);
        assert!(shell_absent.set_interface_base_resolution(
            object_type,
            true,
            None,
            Some(Vec::new()),
        ));
        let before = shell_absent.relation_state_snapshot();
        assert_eq!(
            shell_absent.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnresolvedStructuredMembers(
                object_type
            )),
            "an allocated-empty base list is noncanonical and cannot prove absence"
        );
        assert_eq!(shell_absent.relation_state_snapshot(), before);
        assert!(shell_absent.set_interface_base_resolution(object_type, true, None, None,));
        assert_eq!(
            shell_absent.is_type_assignable_to(source, target),
            Ok(false),
            "a canonical resolved base-less interface may prove the raw name absent"
        );

        let mut inherited = initialized(true);
        let (string, globals) = {
            let bootstrap = inherited.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.globals)
        };
        let object_symbol = alloc_symbol(&mut inherited, SymbolFlags::INTERFACE, "Object");
        let unrelated = alloc_typed_property(&mut inherited, "unrelated", string, false);
        let raw_members = inherited.alloc_symbol_table();
        assert_eq!(
            inherited.insert_symbol(raw_members, EscapedName::source("unrelated"), unrelated,),
            Some(None)
        );
        assert!(inherited.set_symbol_relationships(
            object_symbol,
            Some(raw_members),
            None,
            None,
            None,
        ));
        assert_eq!(
            inherited.insert_symbol(globals, EscapedName::source("Object"), object_symbol,),
            Some(None)
        );
        let object_type = inherited
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(object_symbol))
            .unwrap();
        let constructor_property =
            alloc_typed_property(&mut inherited, "fromConstructor", string, false);
        let base_property = alloc_typed_property(&mut inherited, "fromBase", string, false);
        assert!(inherited.set_symbol_relationships(
            constructor_property,
            None,
            None,
            Some(object_symbol),
            None,
        ));
        assert!(inherited.set_symbol_relationships(
            base_property,
            None,
            None,
            Some(object_symbol),
            None,
        ));
        set_object_properties(
            &mut inherited,
            object_type,
            vec![constructor_property, base_property],
        );
        assert!(inherited.set_declared_type_links(
            object_symbol,
            DeclaredTypeLinks {
                declared_type: Some(object_type),
                ..DeclaredTypeLinks::default()
            },
        ));
        let base = alloc_property_object(&mut inherited, Vec::new());
        assert!(inherited.set_interface_base_resolution(
            object_type,
            true,
            Some(base),
            Some(Vec::new()),
        ));
        let source = alloc_property_object(&mut inherited, Vec::new());
        let target_property =
            alloc_typed_property(&mut inherited, "fromConstructor", string, false);
        let target = alloc_property_object(&mut inherited, vec![target_property]);
        assert_eq!(
            inherited.is_type_assignable_to(source, target),
            Ok(true),
            "a resolved base constructor forces lookup through typed Object members"
        );

        assert!(
            inherited.set_interface_base_resolution(object_type, true, None, Some(vec![base]),)
        );
        let target_property = alloc_typed_property(&mut inherited, "fromBase", string, false);
        let target = alloc_property_object(&mut inherited, vec![target_property]);
        assert_eq!(
            inherited.is_type_assignable_to(source, target),
            Ok(true),
            "resolved base types force lookup through inherited typed Object members"
        );

        let mut unresolved = initialized(true);
        let string = unresolved.intrinsic_bootstrap().unwrap().string_type;
        let globals = unresolved.intrinsic_bootstrap().unwrap().globals;
        let object_symbol = alloc_symbol(&mut unresolved, SymbolFlags::INTERFACE, "Object");
        assert_eq!(
            unresolved.insert_symbol(globals, EscapedName::source("Object"), object_symbol),
            Some(None)
        );
        let source = alloc_property_object(&mut unresolved, Vec::new());
        let target_property = alloc_typed_property(&mut unresolved, "custom", string, false);
        let target = alloc_property_object(&mut unresolved, vec![target_property]);
        let before = unresolved.relation_state_snapshot();
        assert_eq!(
            unresolved.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnresolvedGlobalObject(object_symbol)),
            "raw absence requires a declared global Object type"
        );
        assert_eq!(unresolved.relation_state_snapshot(), before);

        let raw_members = unresolved.alloc_symbol_table();
        let unrelated_raw_property =
            alloc_typed_property(&mut unresolved, "unrelated", string, false);
        assert_eq!(
            unresolved.insert_symbol(
                raw_members,
                EscapedName::source("unrelated"),
                unrelated_raw_property,
            ),
            Some(None)
        );
        assert!(unresolved.set_symbol_relationships(
            object_symbol,
            Some(raw_members),
            None,
            None,
            None,
        ));
        let unrelated_source = alloc_property_object(&mut unresolved, Vec::new());
        let unrelated_target_property =
            alloc_typed_property(&mut unresolved, "custom", string, false);
        let unrelated_target =
            alloc_property_object(&mut unresolved, vec![unrelated_target_property]);
        let before = unresolved.relation_state_snapshot();
        assert_eq!(
            unresolved.is_type_assignable_to(unrelated_source, unrelated_target),
            Err(RelationUnavailable::UnresolvedGlobalObject(object_symbol)),
            "a raw table cannot prove absence without declared-type base facts"
        );
        assert_eq!(unresolved.relation_state_snapshot(), before);

        let raw_property = alloc_typed_property(&mut unresolved, "custom", string, false);
        assert_eq!(
            unresolved.insert_symbol(raw_members, EscapedName::source("custom"), raw_property,),
            Some(None)
        );
        let source = alloc_property_object(&mut unresolved, Vec::new());
        let target_property = alloc_typed_property(&mut unresolved, "custom", string, false);
        let target = alloc_property_object(&mut unresolved, vec![target_property]);
        let before = unresolved.relation_state_snapshot();
        assert_eq!(
            unresolved.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnresolvedGlobalObject(object_symbol)),
            "a raw present name cannot fabricate a resolved property type"
        );
        assert_eq!(unresolved.relation_state_snapshot(), before);

        let object_type = unresolved
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(object_symbol))
            .unwrap();
        assert!(unresolved.set_declared_type_links(
            object_symbol,
            DeclaredTypeLinks {
                declared_type: Some(object_type),
                ..DeclaredTypeLinks::default()
            },
        ));
        let before = unresolved.relation_state_snapshot();
        assert_eq!(
            unresolved.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnresolvedStructuredMembers(
                object_type
            ))
        );
        assert_eq!(unresolved.relation_state_snapshot(), before);

        let mut resolved = initialized(true);
        let (string, number, globals) = {
            let bootstrap = resolved.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.globals,
            )
        };
        let object_symbol = alloc_symbol(&mut resolved, SymbolFlags::INTERFACE, "Object");
        assert_eq!(
            resolved.insert_symbol(globals, EscapedName::source("Object"), object_symbol),
            Some(None)
        );
        let object_type = resolved
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(object_symbol))
            .unwrap();
        let global_property = alloc_typed_property(&mut resolved, "custom", string, false);
        assert!(resolved.set_symbol_relationships(
            global_property,
            None,
            None,
            Some(object_symbol),
            None,
        ));
        set_object_properties(&mut resolved, object_type, vec![global_property]);
        let raw_members = resolved.alloc_symbol_table();
        assert_eq!(
            resolved.insert_symbol(raw_members, EscapedName::source("custom"), global_property,),
            Some(None)
        );
        assert!(resolved.set_symbol_relationships(
            object_symbol,
            Some(raw_members),
            None,
            None,
            None,
        ));
        assert!(resolved.set_declared_type_links(
            object_symbol,
            DeclaredTypeLinks {
                declared_type: Some(object_type),
                ..DeclaredTypeLinks::default()
            },
        ));

        let source = alloc_property_object(&mut resolved, Vec::new());
        let compatible_property = alloc_typed_property(&mut resolved, "custom", string, false);
        let compatible = alloc_property_object(&mut resolved, vec![compatible_property]);
        assert_eq!(resolved.is_type_assignable_to(source, compatible), Ok(true));

        let incompatible_property = alloc_typed_property(&mut resolved, "custom", number, false);
        let incompatible = alloc_property_object(&mut resolved, vec![incompatible_property]);
        assert_eq!(
            resolved.is_type_assignable_to(source, incompatible),
            Ok(false)
        );

        let absent_property = alloc_typed_property(&mut resolved, "other", string, false);
        let absent_target = alloc_property_object(&mut resolved, vec![absent_property]);
        assert_eq!(
            resolved.is_type_assignable_to(source, absent_target),
            Ok(false)
        );
    }

    #[test]
    fn global_object_fallback_validates_the_complete_resolved_shape() {
        let mut invalid_raw = initialized(true);
        let string = invalid_raw.intrinsic_bootstrap().unwrap().string_type;
        let globals = invalid_raw.intrinsic_bootstrap().unwrap().globals;
        let object_symbol = alloc_symbol(&mut invalid_raw, SymbolFlags::INTERFACE, "Object");
        let actual = alloc_typed_property(&mut invalid_raw, "actual", string, false);
        let raw_members = invalid_raw.alloc_symbol_table();
        assert_eq!(
            invalid_raw.insert_symbol(raw_members, EscapedName::source("wrong"), actual),
            Some(None)
        );
        assert!(invalid_raw.set_symbol_relationships(
            object_symbol,
            Some(raw_members),
            None,
            None,
            None,
        ));
        assert_eq!(
            invalid_raw.insert_symbol(globals, EscapedName::source("Object"), object_symbol),
            Some(None)
        );
        let object_type = alloc_property_object(&mut invalid_raw, Vec::new());
        assert!(invalid_raw.set_declared_type_links(
            object_symbol,
            DeclaredTypeLinks {
                declared_type: Some(object_type),
                ..DeclaredTypeLinks::default()
            },
        ));
        let (source, target) = alloc_global_property_query(&mut invalid_raw);
        let before = invalid_raw.relation_state_snapshot();
        assert_eq!(
            invalid_raw.is_type_assignable_to(source, target),
            Err(RelationUnavailable::InvalidSymbolMembers(object_symbol))
        );
        assert_eq!(invalid_raw.relation_state_snapshot(), before);

        let mut computed_raw = initialized(true);
        let globals = computed_raw.intrinsic_bootstrap().unwrap().globals;
        let object_symbol = alloc_symbol(&mut computed_raw, SymbolFlags::INTERFACE, "Object");
        let computed = computed_raw
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::internal(InternalSymbolName::Computed),
            ))
            .unwrap();
        let raw_members = computed_raw.alloc_symbol_table();
        assert_eq!(
            computed_raw.insert_symbol(
                raw_members,
                EscapedName::internal(InternalSymbolName::Computed),
                computed,
            ),
            Some(None)
        );
        assert!(computed_raw.set_symbol_relationships(
            object_symbol,
            Some(raw_members),
            None,
            None,
            None,
        ));
        assert_eq!(
            computed_raw.insert_symbol(globals, EscapedName::source("Object"), object_symbol,),
            Some(None)
        );
        let object_type = alloc_object_shell(&mut computed_raw);
        assert!(computed_raw.set_declared_type_links(
            object_symbol,
            DeclaredTypeLinks {
                declared_type: Some(object_type),
                ..DeclaredTypeLinks::default()
            },
        ));
        let (source, target) = alloc_global_property_query(&mut computed_raw);
        let before = computed_raw.relation_state_snapshot();
        assert_eq!(
            computed_raw.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnresolvedStructuredMembers(
                object_type
            )),
            "a computed placeholder prevents a raw absence proof"
        );
        assert_eq!(computed_raw.relation_state_snapshot(), before);

        let mut unsupported = initialized(true);
        let global_object = unsupported
            .alloc_type_reference(ObjectFlags::NONE, None)
            .unwrap();
        assert!(unsupported.set_structured_type_members(
            global_object,
            None,
            None,
            None,
            None,
            None,
        ));
        let object_symbol = install_global_object(&mut unsupported, global_object);
        let string = unsupported.intrinsic_bootstrap().unwrap().string_type;
        let raw_property = alloc_typed_property(&mut unsupported, "custom", string, false);
        let raw_members = unsupported.alloc_symbol_table();
        assert_eq!(
            unsupported.insert_symbol(raw_members, EscapedName::source("custom"), raw_property,),
            Some(None)
        );
        assert!(unsupported.set_symbol_relationships(
            object_symbol,
            Some(raw_members),
            None,
            None,
            None,
        ));
        let (source, target) = alloc_global_property_query(&mut unsupported);
        let before = unsupported.relation_state_snapshot();
        assert_eq!(
            unsupported.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnsupportedStructuredType(
                global_object
            ))
        );
        assert_eq!(unsupported.relation_state_snapshot(), before);

        let mut malformed = initialized(true);
        let string = malformed.intrinsic_bootstrap().unwrap().string_type;
        let global_object = alloc_object_shell(&mut malformed);
        let global_property = alloc_typed_property(&mut malformed, "custom", string, false);
        assert!(malformed.set_structured_type_members(
            global_object,
            None,
            Some(vec![global_property]),
            None,
            None,
            None,
        ));
        install_global_object(&mut malformed, global_object);
        let (source, target) = alloc_global_property_query(&mut malformed);
        let before = malformed.relation_state_snapshot();
        assert_eq!(
            malformed.is_type_assignable_to(source, target),
            Err(RelationUnavailable::InvalidStructuredMembers(global_object))
        );
        assert_eq!(malformed.relation_state_snapshot(), before);

        let mut unrelated = initialized(true);
        let string = unrelated.intrinsic_bootstrap().unwrap().string_type;
        let method = alloc_symbol(&mut unrelated, SymbolFlags::METHOD, "unrelated");
        let members = unrelated.alloc_symbol_table();
        assert_eq!(
            unrelated.insert_symbol(members, EscapedName::source("unrelated"), method),
            Some(None)
        );
        let signature = unrelated
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
            .unwrap();
        let index = unrelated
            .alloc_index_info(string, string, false, None, Vec::new())
            .unwrap();
        let global_object = alloc_object_shell(&mut unrelated);
        assert!(unrelated.set_structured_type_members(
            global_object,
            Some(members),
            Some(vec![method]),
            Some(vec![signature]),
            None,
            Some(vec![index]),
        ));
        install_global_object(&mut unrelated, global_object);
        let source = alloc_property_object(&mut unrelated, Vec::new());
        let target_property = alloc_typed_property(&mut unrelated, "a", string, true);
        let target = alloc_property_object(&mut unrelated, vec![target_property]);
        assert_eq!(
            unrelated.is_type_assignable_to(source, target),
            Ok(true),
            "unrelated global methods, signatures, and indexes do not affect an absent lookup"
        );

        let mut requested = initialized(true);
        let method = alloc_symbol(&mut requested, SymbolFlags::METHOD, "custom");
        let global_object = alloc_property_object(&mut requested, vec![method]);
        install_global_object(&mut requested, global_object);
        let (source, target) = alloc_global_property_query(&mut requested);
        let before = requested.relation_state_snapshot();
        assert_eq!(
            requested.is_type_assignable_to(source, target),
            Err(RelationUnavailable::UnsupportedProperty(method))
        );
        assert_eq!(requested.relation_state_snapshot(), before);
    }

    #[test]
    fn test_limits_publish_exact_complexity_and_stack_overflow_results() {
        let mut complexity = initialized(true);
        let source = alloc_property_object(&mut complexity, Vec::new());
        let target = alloc_property_object(&mut complexity, Vec::new());
        assert_eq!(
            complexity.is_type_assignable_to_with_test_limits(source, target, 0, 100),
            Ok(false)
        );
        let key = complexity
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert_eq!(
            complexity.relation_cache_get(RelationKind::Assignable, key),
            RelationComparisonResult::FAILED | RelationComparisonResult::COMPLEXITY_OVERFLOW
        );

        let mut depth = initialized(true);
        let source_inner = alloc_property_object(&mut depth, Vec::new());
        let target_inner = alloc_property_object(&mut depth, Vec::new());
        let source_property = alloc_typed_property(&mut depth, "nested", source_inner, false);
        let target_property = alloc_typed_property(&mut depth, "nested", target_inner, false);
        let source = alloc_property_object(&mut depth, vec![source_property]);
        let target = alloc_property_object(&mut depth, vec![target_property]);
        assert_eq!(
            depth.is_type_assignable_to_with_test_limits(source, target, 100, 1),
            Ok(false)
        );
        let key = depth
            .relation_key_if_available(source, target, super::IntersectionState::NONE, false, false)
            .unwrap()
            .key();
        assert_eq!(
            depth.relation_cache_get(RelationKind::Assignable, key),
            RelationComparisonResult::FAILED | RelationComparisonResult::STACK_DEPTH_OVERFLOW
        );
    }

    #[test]
    fn unknown_like_cache_bits_remain_union_payload_state() {
        let mut store = initialized(true);
        let unknown_union = store.intrinsic_bootstrap().unwrap().unknown_union_type;
        let TypeData::Union(_) = store.type_payload(unknown_union).unwrap().data() else {
            panic!("strict bootstrap unknown union must retain its union payload");
        };
        assert!(store.add_type_object_flags(
            unknown_union,
            ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED | ObjectFlags::IS_UNKNOWN_LIKE_UNION,
        ));
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(store.is_type_assignable_to(string, unknown_union), Ok(true));
    }
}
