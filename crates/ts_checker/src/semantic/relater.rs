//! Exact dependency-closed fast, primitive-union, and property-only relations.
//!
//! This module ports `isTypeRelatedTo`, `isSimpleTypeRelatedTo`, and their
//! no-diagnostic entry points plus primitive/literal/nullable unions and the
//! property-only object slice of `recursiveTypeRelatedTo` for assignable,
//! comparable, subtype, and strict-subtype relations, including fresh
//! excess-property checks and strict/exact optional-property relations, from pinned
//! `internal/checker/relater.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Unsupported structural paths
//! return [`RelationUnavailable`] instead of being misreported as unrelated.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};

use super::{
    CanonicalGlobalTypeInitializationError, CanonicalGlobalTypes, DeclaredTypeHost,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
    bootstrap::LiteralTypeCacheError,
    declared::type_list_key,
    derived_types::DerivedObjectLiteralValidation,
    global_types::preflight_generic_global_type_target,
    ids::TypeId,
    links::{MembersOrExportsResolutionKind, ValueSymbolLinks},
    mapper::TypeMapper,
    relation::{
        ExpandingFlags, IntersectionState, RecursionFlags, RecursionIdentityUnavailable,
        RelationComparisonResult, RelationKeyUnavailable, RelationKind,
    },
    signatures::Ternary,
    store::SemanticStore,
    type_records::{CacheHashKey, ConstrainedTypeData, TypeCacheState, TypeData, TypeRecord},
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

#[derive(Clone, Copy)]
struct RelationBootstrapFacts {
    strict_null_checks: bool,
    exact_optional_property_types: bool,
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
    property_origin: ObjectPropertyOrigin,
}

#[derive(Clone, Copy)]
enum ObjectPropertyOrigin {
    Declared,
    FreshObjectLiteral(SemanticSymbolId),
    DerivedObjectLiteral(SemanticSymbolId),
}

impl ObjectPropertyOrigin {
    fn is_declared(self) -> bool {
        matches!(self, Self::Declared)
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
    validated_array_targets: HashSet<TypeId>,
    validated_unions: HashMap<TypeId, Vec<TypeId>>,
    pending: PendingRelationCache,
    maybe_keys: Vec<CacheHashKey>,
    maybe_keys_set: HashSet<CacheHashKey>,
    source_stack: Vec<TypeId>,
    target_stack: Vec<TypeId>,
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
        Self::new_with_global_types(store, relation, bootstrap, None)
    }

    fn new_with_global_types(
        store: &'store mut SemanticStore<TypeRecord, TypeMapper>,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
        global_types: Option<RelationGlobalTypes>,
    ) -> Self {
        let relation_count = store.relation_comparison_budget(relation);
        Self::new_with_limits_and_global_types(
            store,
            relation,
            bootstrap,
            global_types,
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
            relation_count,
            stack_depth_limit,
        )
    }

    fn new_with_limits_and_global_types(
        store: &'store mut SemanticStore<TypeRecord, TypeMapper>,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
        global_types: Option<RelationGlobalTypes>,
        relation_count: isize,
        stack_depth_limit: usize,
    ) -> Self {
        Self {
            store,
            relation,
            bootstrap,
            global_types,
            validated_array_targets: HashSet::new(),
            validated_unions: HashMap::new(),
            pending: PendingRelationCache::default(),
            maybe_keys: Vec::new(),
            maybe_keys_set: HashSet::new(),
            source_stack: Vec::new(),
            target_stack: Vec::new(),
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
        for (key, value) in self.pending.writes {
            self.store.relation_cache_set(self.relation, key, value);
        }
        Ok(result != Ternary::False)
    }

    fn finish_without_specialized_root_cache(self, result: Ternary) -> bool {
        for (key, value) in self.pending.writes {
            self.store.relation_cache_set(self.relation, key, value);
        }
        result != Ternary::False
    }

    fn cache_get(&self, key: CacheHashKey) -> RelationComparisonResult {
        self.pending.get(self.store, self.relation, key)
    }

    fn cache_set(&mut self, key: CacheHashKey, result: RelationComparisonResult) {
        self.pending.set(key, result);
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

    fn matching_array_reference_target(
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Option<TypeId>, RelationUnavailable> {
        matching_configured_array_reference_target(self.store, self.global_types, source, target)
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

    fn validate_canonical_array_target(
        &mut self,
        target: TypeId,
    ) -> Result<(), RelationUnavailable> {
        if self.validated_array_targets.contains(&target) {
            return Ok(());
        }
        let fallback = preflight_generic_global_type_target(self.store, target)
            .map_err(RelationUnavailable::CanonicalGlobalType)?;
        if fallback.is_some() {
            return Err(RelationUnavailable::UnavailableCanonicalArrayTarget(target));
        }
        self.validated_array_targets.insert(target);
        Ok(())
    }

    #[allow(clippy::too_many_lines)] // One read-only Array-reference invariant matrix.
    fn canonical_array_reference_argument(
        &mut self,
        type_id: TypeId,
        target: TypeId,
    ) -> Result<TypeId, RelationUnavailable> {
        self.validate_canonical_array_target(target)?;

        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        let TypeData::TypeReference(reference) = record.data() else {
            return Err(RelationUnavailable::MalformedCanonicalArrayReference(
                type_id,
            ));
        };
        let Some([argument]) = reference.resolved_type_arguments.as_deref() else {
            return Err(RelationUnavailable::MalformedCanonicalArrayReference(
                type_id,
            ));
        };
        let argument = *argument;
        if record.flags() != TypeFlags::OBJECT
            || reference.object.target != Some(target)
            || reference.object.mapper.is_some()
            || reference.object.instantiations != TypeCacheState::Unallocated
            || reference.node.is_some()
            || record.alias().is_some()
            || self.store.type_payload(argument).is_none()
        {
            return Err(RelationUnavailable::MalformedCanonicalArrayReference(
                type_id,
            ));
        }

        let target_record = self
            .store
            .type_payload(target)
            .expect("the canonical Array target was preflighted");
        let TypeData::Interface(interface) = target_record.data() else {
            unreachable!("the canonical Array target changed after preflight")
        };
        let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
        else {
            unreachable!("the canonical Array cache changed after preflight")
        };
        let Some(canonical) = instantiations.get(&type_list_key(&[argument])).copied() else {
            return Err(RelationUnavailable::MalformedCanonicalArrayReference(
                type_id,
            ));
        };
        if record.symbol() != target_record.symbol() {
            return Err(RelationUnavailable::MalformedCanonicalArrayReference(
                type_id,
            ));
        }

        if canonical == type_id {
            return if record.object_flags().intersects(ObjectFlags::ARRAY_LITERAL) {
                Err(RelationUnavailable::MalformedCanonicalArrayReference(
                    type_id,
                ))
            } else {
                Ok(argument)
            };
        }

        if !record.object_flags().intersects(ObjectFlags::ARRAY_LITERAL) {
            return Err(RelationUnavailable::MalformedCanonicalArrayReference(
                type_id,
            ));
        }
        self.store
            .validate_array_literal_clone(canonical, type_id)
            .map_err(|_| RelationUnavailable::MalformedCanonicalArrayReference(type_id))?;
        Ok(argument)
    }

    fn canonical_array_reference_arguments(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Option<(TypeId, TypeId)>, RelationUnavailable> {
        let Some(array_target) = self.matching_array_reference_target(source, target)? else {
            return Ok(None);
        };
        let source_argument = self.canonical_array_reference_argument(source, array_target)?;
        let target_argument = self.canonical_array_reference_argument(target, array_target)?;
        Ok(Some((source_argument, target_argument)))
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
        &self,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
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
                    || record.check_flags() != CheckFlags::NONE
                    || record.members().is_some()
                    || record.exports().is_some()
                    || record.export_symbol().is_some()
                {
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
                .name();
            if self.global_object_property(name)?.is_none() {
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
                    .map_err(|error| array_relation_preflight_error(*type_id, error))?;
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
                        let flags = self.store.type_flags(object).map_err(|_| {
                            LiteralTypeCacheError::UnsupportedUnionConstituent(object)
                        })?;
                        if !flags.intersects(TypeFlags::OBJECT) {
                            continue;
                        }
                        let members = self.resolved_object_members(object, true).map_err(|_| {
                            LiteralTypeCacheError::UnsupportedUnionConstituent(object)
                        })?;
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
        let validation = match self.global_types {
            Some(global_types) => self
                .store
                .validate_union_constituent_with_array_targets(global_types.array_targets, type_id),
            None => self.store.validate_union_constituent(type_id),
        };
        validation.map_err(|error| union_validation_unavailable(type_id, error))?;
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
        if original_source == original_target {
            return Ok(Ternary::True);
        }
        if intersection_state != IntersectionState::NONE {
            return Err(RelationUnavailable::StructuralRelation {
                source: original_source,
                target: original_target,
                relation: self.relation,
            });
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
            if source_flags.intersects(TypeFlags::UNION) {
                return self.recursive_type_related_to(
                    source,
                    target,
                    IntersectionState::NONE,
                    recursion_flags,
                );
            }
            if let Some((source_argument, target_argument)) =
                self.canonical_array_reference_arguments(source, target)?
            {
                return self.is_related_to_ex(
                    source_argument,
                    target_argument,
                    RecursionFlags::BOTH,
                    intersection_state,
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

        if source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
            || target_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
        {
            if self.relation != RelationKind::Identity
                && target_flags.intersects(TypeFlags::OBJECT)
                && let Some(apparent_source) = self
                    .global_types
                    .and_then(|global_types| global_types.apparent_primitive_type(source_flags))
            {
                return self.is_related_to_ex(
                    apparent_source,
                    target,
                    recursion_flags,
                    intersection_state,
                );
            }
            if let Some((source_argument, target_argument)) =
                self.canonical_array_reference_arguments(source, target)?
            {
                return self.is_related_to_ex(
                    source_argument,
                    target_argument,
                    RecursionFlags::BOTH,
                    intersection_state,
                );
            }
            if source_flags.intersects(TypeFlags::OBJECT)
                && target_flags.intersects(TypeFlags::OBJECT)
                && let Some(related) = self.canonical_array_empty_object_relation(source, target)?
            {
                return Ok(related);
            }
            if supports_property_object_relation(self.relation)
                && source_flags.intersects(TypeFlags::OBJECT)
                && target_flags.intersects(TypeFlags::OBJECT)
            {
                if self.is_fresh_object_literal(source)?
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
        if intersection_state != IntersectionState::NONE {
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }
        let source_flags = self.store.type_flags(source)?;
        let target_flags = self.store.type_flags(target)?;
        if self.relation.is_identity() {
            if source_flags.intersects(TypeFlags::UNION) {
                let mut result = self.each_type_related_to_some_type(source, target)?;
                if result != Ternary::False {
                    result &= self.each_type_related_to_some_type(target, source)?;
                }
                return Ok(result);
            }
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }
        if source_flags.intersects(TypeFlags::UNION) || target_flags.intersects(TypeFlags::UNION) {
            return self.union_or_intersection_related_to(source, target, intersection_state);
        }
        if !supports_property_object_relation(self.relation)
            || !source_flags.intersects(TypeFlags::OBJECT)
            || !target_flags.intersects(TypeFlags::OBJECT)
        {
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }
        let source_members = self.resolved_object_members(source, true)?;
        let target_members =
            self.resolved_object_members(target, self.allows_fresh_object_target())?;
        if matches!(
            self.relation,
            RelationKind::Subtype | RelationKind::StrictSubtype
        ) && self.is_fresh_object_literal(target)?
            && target_members.properties.is_empty()
            && !source_members.properties.is_empty()
        {
            return Ok(Ternary::False);
        }
        self.properties_related_to(source, &source_members, &target_members)
    }

    fn union_or_intersection_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        intersection_state: IntersectionState,
    ) -> Result<Ternary, RelationUnavailable> {
        let source_flags = self.store.type_flags(source)?;
        let target_flags = self.store.type_flags(target)?;
        if source_flags.intersects(TypeFlags::INTERSECTION)
            || target_flags.intersects(TypeFlags::INTERSECTION)
        {
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }
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
            return self.type_related_to_some_type(source, target, intersection_state);
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

    fn each_type_related_to_some_type(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Result<Ternary, RelationUnavailable> {
        let source_types = self.union_types(source)?;
        self.union_types(target)?;
        let mut result = Ternary::True;
        for source_type in source_types {
            let related =
                self.type_related_to_some_type(source_type, target, IntersectionState::NONE)?;
            if related == Ternary::False {
                return Ok(Ternary::False);
            }
            result &= related;
        }
        Ok(result)
    }

    fn weak_target_lacks_common_properties(
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let target_members =
            self.resolved_object_members(target, self.allows_fresh_object_target())?;
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
        let source_members = self.resolved_object_members(source, true)?;
        if source_members.properties.is_empty() || self.is_direct_global_object_type(source)? {
            return Ok(false);
        }
        let target_table = target_members
            .members
            .and_then(|members| self.store.symbol_table(members))
            .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?;
        for property in source_members.properties {
            if target_table
                .get(
                    self.property_symbol(property, source_members.property_origin)?
                        .name(),
                )
                .is_some()
            {
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
        &self,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, RelationUnavailable> {
        let target_members =
            self.resolved_object_members(target, self.allows_fresh_object_target())?;

        // Pinned `hasExcessProperties` treats the empty object as an open
        // target and exempts the global Object target only for assignable and
        // comparable relations. Subtype relations retain fresh-literal excess
        // checking against those targets. Index signatures and
        // union/intersection targets remain outside this property-only slice.
        if matches!(
            self.relation,
            RelationKind::Assignable | RelationKind::Comparable
        ) && (target_members.properties.is_empty()
            || self.is_direct_global_object_type(target)?)
        {
            return Ok(false);
        }
        let source_members = self.resolved_object_members(source, true)?;
        if target_members.properties.is_empty() {
            return Ok(!source_members.properties.is_empty());
        }
        let target_table = target_members
            .members
            .and_then(|members| self.store.symbol_table(members))
            .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?;
        for property in source_members.properties {
            let name = self
                .property_symbol(property, source_members.property_origin)?
                .name();
            if target_table.get(name).is_none() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn is_direct_global_object_type(&self, type_id: TypeId) -> Result<bool, RelationUnavailable> {
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
        Ok(self.store.get_merged_symbol(type_symbol) == Some(global_object))
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

    fn property_related_to(
        &mut self,
        source_property: SemanticSymbolId,
        source_origin: ObjectPropertyOrigin,
        target_property: SemanticSymbolId,
        target_origin: ObjectPropertyOrigin,
    ) -> Result<Ternary, RelationUnavailable> {
        let source_flags = self
            .property_symbol(source_property, source_origin)?
            .flags();
        let target_flags = self
            .property_symbol(target_property, target_origin)?
            .flags();
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
        &self,
        source: TypeId,
        source_members: &ResolvedObjectMembers,
        target_property: SemanticSymbolId,
        target_origin: ObjectPropertyOrigin,
    ) -> Result<Option<SemanticSymbolId>, RelationUnavailable> {
        let target_symbol = self.property_symbol(target_property, target_origin)?;
        let name = target_symbol.name();
        if let Some(members) = source_members.members {
            let table = self
                .store
                .symbol_table(members)
                .ok_or(RelationUnavailable::InvalidStructuredMembers(source))?;
            if let Some(property) = table.get(name) {
                self.property_symbol(property, source_members.property_origin)?;
                return Ok(Some(property));
            }
        }
        self.global_object_property(name)
    }

    fn global_object_property(
        &self,
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
        let record = self
            .store
            .type_payload(global_object_type)
            .ok_or(RelationUnavailable::Type(global_object_type))?;
        let no_inherited_members = match record.data() {
            TypeData::Object(_) => true,
            TypeData::Interface(interface) => {
                interface.base_types_resolved
                    && interface.resolved_base_constructor_type.is_none()
                    && interface.resolved_base_types.is_none()
            }
            _ => false,
        };
        if no_inherited_members && self.raw_symbol_members_prove_absent(global_object, name)? {
            return Ok(None);
        }
        if !record
            .object_flags()
            .intersects(ObjectFlags::MEMBERS_RESOLVED)
        {
            return Err(RelationUnavailable::UnresolvedStructuredMembers(
                global_object_type,
            ));
        }
        let structured =
            record
                .data()
                .structured()
                .ok_or(RelationUnavailable::MalformedStructuredType(
                    global_object_type,
                ))?;
        let properties = structured.properties.as_deref().unwrap_or_default();
        let mut property_set = HashSet::with_capacity(properties.len());
        for property in properties {
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
        for property in properties {
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

    fn raw_symbol_members_prove_absent(
        &self,
        symbol: SemanticSymbolId,
        name: ts_binder::EscapedNameRef<'_>,
    ) -> Result<bool, RelationUnavailable> {
        let record = self
            .store
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?;
        let Some(members) = record.members() else {
            return Ok(true);
        };
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

    fn global_object_symbol(&self) -> Result<Option<SemanticSymbolId>, RelationUnavailable> {
        let globals = self
            .store
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(RelationUnavailable::MissingBootstrap)?
            .globals;
        let globals = self
            .store
            .symbol_table(globals)
            .ok_or(RelationUnavailable::MissingBootstrap)?;
        let Some(global_object) = globals.get_source("Object") else {
            return Ok(None);
        };
        self.store
            .get_merged_symbol(global_object)
            .map(Some)
            .ok_or(RelationUnavailable::Symbol(global_object))
    }

    fn property_symbol(
        &self,
        symbol: SemanticSymbolId,
        origin: ObjectPropertyOrigin,
    ) -> Result<&ts_binder::semantic::Symbol, RelationUnavailable> {
        let record = self
            .store
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?;
        match origin {
            ObjectPropertyOrigin::FreshObjectLiteral(owner) => {
                return if self.is_canonical_object_literal_property(symbol, record, owner) {
                    Ok(record)
                } else {
                    Err(RelationUnavailable::UnsupportedProperty(symbol))
                };
            }
            ObjectPropertyOrigin::DerivedObjectLiteral(owner) => {
                // The object-wide warm-cache validator established the full
                // clone/reuse chain before this marker was constructed.
                return if record.parent() == Some(owner)
                    && self.store.get_merged_symbol(symbol) == Some(symbol)
                {
                    Ok(record)
                } else {
                    Err(RelationUnavailable::UnsupportedProperty(symbol))
                };
            }
            ObjectPropertyOrigin::Declared => {}
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
            let allowed_parent_flags = SymbolFlags::INTERFACE | SymbolFlags::TYPE_LITERAL;
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
            self.canonical_object_literal_raw_members(owner),
            Some(CanonicalObjectLiteralRawMembers::Allocated(members))
                if members.get(name) == Some(target)
        )
    }

    fn canonical_object_literal_raw_members(
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
        if source_is_union {
            self.union_types(source)?;
        }
        if target_is_union {
            self.union_types(target)?;
        }
        if source_is_union || target_is_union {
            return Ok(());
        }
        if supports_property_object_relation(self.relation)
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

    fn ensure_supported_object_kind(
        &self,
        type_id: TypeId,
        allow_fresh_literal: bool,
    ) -> Result<(), RelationUnavailable> {
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if record.flags() != TypeFlags::OBJECT || !self.supports_property_object_alias(type_id) {
            return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
        }
        match self
            .store
            .validate_derived_object_literal_for_relation(type_id)
        {
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

    fn resolved_object_members(
        &self,
        type_id: TypeId,
        allow_fresh_literal: bool,
    ) -> Result<ResolvedObjectMembers, RelationUnavailable> {
        self.ensure_supported_object_kind(type_id, allow_fresh_literal)?;
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        let property_origin = match self
            .store
            .validate_derived_object_literal_for_relation(type_id)
        {
            DerivedObjectLiteralValidation::Valid { owner } => {
                ObjectPropertyOrigin::DerivedObjectLiteral(owner)
            }
            DerivedObjectLiteralValidation::Invalid => {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            }
            DerivedObjectLiteralValidation::NotDerived
                if record
                    .object_flags()
                    .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL) =>
            {
                ObjectPropertyOrigin::FreshObjectLiteral(
                    record
                        .symbol()
                        .ok_or(RelationUnavailable::UnsupportedStructuredType(type_id))?,
                )
            }
            DerivedObjectLiteralValidation::NotDerived => ObjectPropertyOrigin::Declared,
        };
        if !record
            .object_flags()
            .intersects(ObjectFlags::MEMBERS_RESOLVED)
        {
            return Err(RelationUnavailable::UnresolvedStructuredMembers(type_id));
        }
        let structured = record
            .data()
            .structured()
            .ok_or(RelationUnavailable::MalformedStructuredType(type_id))?;
        if structured.call_signature_count != 0
            || structured
                .signatures
                .as_ref()
                .is_some_and(|values| !values.is_empty())
        {
            return Err(RelationUnavailable::StructuredSignatures(type_id));
        }
        if structured
            .index_infos
            .as_ref()
            .is_some_and(|values| !values.is_empty())
        {
            return Err(RelationUnavailable::StructuredIndexInfos(type_id));
        }
        let properties = structured.properties.clone().unwrap_or_default();
        let mut property_set = HashSet::with_capacity(properties.len());
        for property in &properties {
            if !property_set.insert(*property) {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            }
            let property_record = self.property_symbol(*property, property_origin)?;
            // This dependency-closed slice admits no interface heritage, so
            // every ordinary member is owned directly by this type's symbol.
            // Revisit this equality when inherited members become supported.
            if property_origin.is_declared() && property_record.parent() != record.symbol() {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
            }
        }
        if let ObjectPropertyOrigin::FreshObjectLiteral(owner) = property_origin {
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
            if record.object_flags() != expected_flags {
                return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
            }
            let TypeData::Object(object) = record.data() else {
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
                CanonicalObjectLiteralRawMembers::Nil => {
                    return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                }
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
                CanonicalObjectLiteralRawMembers::Allocated(_) => {
                    return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                }
            }
        }
        match structured.members {
            None if properties.is_empty() && property_origin.is_declared() => {}
            None => return Err(RelationUnavailable::InvalidStructuredMembers(type_id)),
            Some(members) => {
                let table = self
                    .store
                    .symbol_table(members)
                    .ok_or(RelationUnavailable::InvalidStructuredMembers(type_id))?;
                if table.len() != properties.len() {
                    return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                }
                for (name, property) in table.iter() {
                    let symbol = self.property_symbol(property, property_origin)?;
                    if symbol.name() != name || !property_set.contains(&property) {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                    }
                }
                for property in &properties {
                    let symbol = self.property_symbol(*property, property_origin)?;
                    if table.get(symbol.name()) != Some(*property) {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                    }
                }
            }
        }
        Ok(ResolvedObjectMembers {
            members: structured.members,
            properties,
            property_origin,
        })
    }
}

impl SemanticStore<TypeRecord, TypeMapper> {
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
                    let state = super::object_members::interface_state(self, &plan, type_id)
                        .map_err(|_| RelationUnavailable::InvalidStructuredMembers(type_id))?;
                    if !matches!(
                        state,
                        super::object_members::PropertyObjectState::Resolved(resolved)
                            if resolved == type_id
                    ) {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
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
                            if alias.type_arguments().is_some()
                                || self.get_merged_symbol(alias_symbol) != Some(alias_symbol)
                                || alias_record.flags() != SymbolFlags::TYPE_ALIAS
                                || alias_record.check_flags() != CheckFlags::NONE
                                || alias_record.parent().is_some()
                                || alias_record.value_declaration().is_some()
                                || alias_record.exports().is_some()
                                || alias_record.export_symbol().is_some()
                                || self.source_node_kind(alias_declaration)
                                    != Some(SyntaxKind::TypeAliasDeclaration)
                                || !host.symbol_matches(self, alias_declaration, alias_symbol)
                                || self.type_alias_links(alias_symbol).is_none_or(|links| {
                                    links.declared_type != Some(type_id)
                                        || links.type_parameters.is_some()
                                        || links.instantiations.is_some()
                                        || links.is_constructor_declared_property
                                })
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
        let session = RelaterSession::new(self, RelationKind::Assignable, bootstrap);
        let resolved = session.resolved_object_members(type_id, false)?;
        if let Some((plan, property_types)) = plan {
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
        let bootstrap = self.relation_bootstrap_facts()?;
        let source = self.regular_type_if_fresh(source)?;
        let target = self.regular_type_if_fresh(target)?;
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

        let supported_array_relation = source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::OBJECT)
            && matching_configured_array_reference_target(self, global_types, source, target)?
                .is_some();
        let supported_apparent_primitive_relation = relation != RelationKind::Identity
            && target_flags.intersects(TypeFlags::OBJECT)
            && global_types
                .and_then(|global_types| global_types.apparent_primitive_type(source_flags))
                .is_some();
        if source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::OBJECT)
            && !supported_array_relation
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
            let union_relation = source_flags.intersects(TypeFlags::UNION)
                || target_flags.intersects(TypeFlags::UNION);
            let supported_object_relation = supports_property_object_relation(relation)
                && source_flags.intersects(TypeFlags::OBJECT)
                && target_flags.intersects(TypeFlags::OBJECT);
            if union_relation
                || supported_object_relation
                || supported_array_relation
                || supported_apparent_primitive_relation
            {
                let mut session =
                    RelaterSession::new_with_global_types(self, relation, bootstrap, global_types);
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
        self.type_payload(literal.regular_type)
            .map(|_| literal.regular_type)
            .ok_or(RelationUnavailable::Type(literal.regular_type))
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
        if !bootstrap.strict_null_checks || !record.flags().intersects(TypeFlags::UNION) {
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

fn matching_configured_array_reference_target(
    store: &SemanticStore<TypeRecord, TypeMapper>,
    global_types: Option<RelationGlobalTypes>,
    source: TypeId,
    target: TypeId,
) -> Result<Option<TypeId>, RelationUnavailable> {
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
    let Some(reference_target) = source_reference.object.target else {
        return Ok(None);
    };
    Ok((target_reference.object.target == Some(reference_target)
        && global_types.contains_array_target(reference_target))
    .then_some(reference_target))
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
    use ts_ast::{FileId, SyntaxKind};
    use ts_binder::{
        AstScope, CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData,
        SymbolFlags,
    };
    use ts_jsnum::{Number, PseudoBigInt};
    use ts_parser::parse_source_file;

    use super::{ArrayTypeError, LiteralTypeCacheError, RelationGlobalTypes, RelationUnavailable};
    use crate::semantic::{
        CanonicalGlobalTypeInitializationError, CanonicalTypeMapperStore, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, MembersAndExportsLinks, MembersOrExportsResolutionKind,
        RelationComparisonResult, RelationKind, TypeAliasLinks, TypeId, ValueSymbolLinks,
        array_types::CanonicalArrayTargets,
        declared::type_list_key,
        global_types::create_type_from_generic_global_type,
        signatures::{SignatureFlags, Ternary},
        type_records::{LiteralValue, RegularLiteralLink, TypeData},
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
                .map(|(name, _)| format!("{name}: 0"))
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
        let property = alloc_symbol(store, SymbolFlags::PROPERTY, name);
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
            Err(RelationUnavailable::UnsupportedStructuredType(
                readonly_union
            )),
            "different generic targets do not acquire inferred variance"
        );
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
            Err(RelationUnavailable::CanonicalGlobalType(
                CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(array.target)
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

        assert!(store.set_value_symbol_links(
            widened_property,
            ValueSymbolLinks {
                resolved_type: Some(any),
                target: Some(fixture.raw_properties[0]),
                ..ValueSymbolLinks::default()
            },
        ));
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
