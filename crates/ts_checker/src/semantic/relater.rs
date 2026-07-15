//! Exact dependency-closed fast, primitive-union, and property-only relations.
//!
//! This module ports `isTypeRelatedTo`, `isSimpleTypeRelatedTo`, and their
//! no-diagnostic entry points plus primitive/literal/nullable unions and the
//! required-property object slice of `recursiveTypeRelatedTo` from pinned
//! `internal/checker/relater.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Unsupported structural paths
//! return [`RelationUnavailable`] instead of being misreported as unrelated.

use std::collections::{HashMap, HashSet};

use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags, SymbolTableId};

use super::{
    bootstrap::LiteralTypeCacheError,
    ids::TypeId,
    links::MembersOrExportsResolutionKind,
    mapper::TypeMapper,
    relation::{
        ExpandingFlags, IntersectionState, RecursionFlags, RecursionIdentityUnavailable,
        RelationComparisonResult, RelationKeyUnavailable, RelationKind,
    },
    signatures::Ternary,
    store::SemanticStore,
    type_records::{CacheHashKey, TypeData, TypeRecord},
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
    wildcard_type: TypeId,
    any_function_type: TypeId,
    string_type: TypeId,
    number_type: TypeId,
    bigint_type: TypeId,
}

const PINNED_RELATION_STACK_DEPTH: usize = 100;
const PINNED_EXPANDING_DEPTH: usize = 3;

struct ResolvedObjectMembers {
    members: Option<SymbolTableId>,
    properties: Vec<SemanticSymbolId>,
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
        let relation_count = store.relation_comparison_budget(relation);
        Self::new_with_limits(
            store,
            relation,
            bootstrap,
            relation_count,
            PINNED_RELATION_STACK_DEPTH,
        )
    }

    fn new_with_limits(
        store: &'store mut SemanticStore<TypeRecord, TypeMapper>,
        relation: RelationKind,
        bootstrap: RelationBootstrapFacts,
        relation_count: isize,
        stack_depth_limit: usize,
    ) -> Self {
        Self {
            store,
            relation,
            bootstrap,
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

    fn cache_get(&self, key: CacheHashKey) -> RelationComparisonResult {
        self.pending.get(self.store, self.relation, key)
    }

    fn cache_set(&mut self, key: CacheHashKey, result: RelationComparisonResult) {
        self.pending.set(key, result);
    }

    fn union_types(&mut self, type_id: TypeId) -> Result<Vec<TypeId>, RelationUnavailable> {
        if let Some(types) = self.validated_unions.get(&type_id) {
            return Ok(types.clone());
        }
        self.store
            .validate_union_constituent(type_id)
            .map_err(|error| union_validation_unavailable(type_id, error))?;
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
            if self.relation == RelationKind::Assignable
                && source_flags.intersects(TypeFlags::OBJECT)
                && target_flags.intersects(TypeFlags::OBJECT)
            {
                if self.weak_target_lacks_common_properties(source, target)? {
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
        if self.relation != RelationKind::Assignable
            || !source_flags.intersects(TypeFlags::OBJECT)
            || !target_flags.intersects(TypeFlags::OBJECT)
        {
            return Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: self.relation,
            });
        }
        let source_members = self.resolved_object_members(source)?;
        let target_members = self.resolved_object_members(target)?;
        self.properties_related_to(source, target, &source_members, &target_members)
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
        let target_members = self.resolved_object_members(target)?;
        if target_members.properties.is_empty() {
            return Ok(false);
        }
        for property in &target_members.properties {
            if !self
                .property_symbol(*property)?
                .flags()
                .intersects(SymbolFlags::OPTIONAL)
            {
                return Ok(false);
            }
        }
        let source_members = self.resolved_object_members(source)?;
        if source_members.properties.is_empty() || self.global_object_type()? == Some(source) {
            return Ok(false);
        }
        let target_table = target_members
            .members
            .and_then(|members| self.store.symbol_table(members))
            .ok_or(RelationUnavailable::InvalidStructuredMembers(target))?;
        for property in source_members.properties {
            if target_table
                .get(self.property_symbol(property)?.name())
                .is_some()
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn properties_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        source_members: &ResolvedObjectMembers,
        target_members: &ResolvedObjectMembers,
    ) -> Result<Ternary, RelationUnavailable> {
        // Preserve upstream's unmatched-property pass before comparing any
        // property types. This ordering is observable through relation caches.
        for target_property in &target_members.properties {
            let target_symbol = self.property_symbol(*target_property)?;
            if !target_symbol.flags().intersects(SymbolFlags::OPTIONAL)
                && self
                    .lookup_source_property(source, source_members, *target_property)?
                    .is_none()
            {
                return Ok(Ternary::False);
            }
        }

        let mut result = Ternary::True;
        for target_property in &target_members.properties {
            let Some(source_property) =
                self.lookup_source_property(source, source_members, *target_property)?
            else {
                continue;
            };
            if source_property == *target_property {
                continue;
            }
            let related =
                self.property_related_to(source, target, source_property, *target_property)?;
            if related == Ternary::False {
                return Ok(Ternary::False);
            }
            result &= related;
        }
        Ok(result)
    }

    fn property_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        source_property: SemanticSymbolId,
        target_property: SemanticSymbolId,
    ) -> Result<Ternary, RelationUnavailable> {
        let source_flags = self.property_symbol(source_property)?.flags();
        let target_flags = self.property_symbol(target_property)?.flags();
        let target_type = self.property_type(target_property)?;
        if self.bootstrap.strict_null_checks && target_flags.intersects(SymbolFlags::OPTIONAL) {
            return Err(RelationUnavailable::StrictOptionalProperty(target_property));
        }
        let target_type_flags = self.store.type_flags(target_type)?;
        if target_type_flags.intersects(TypeFlags::ANY_OR_UNKNOWN) {
            return self.optional_property_result(
                source,
                target,
                source_property,
                target_property,
                Ternary::True,
            );
        }
        if self.bootstrap.strict_null_checks && source_flags.intersects(SymbolFlags::OPTIONAL) {
            return Err(RelationUnavailable::StrictOptionalProperty(source_property));
        }
        let source_type = self.property_type(source_property)?;
        let related = self.is_related_to_ex(
            source_type,
            target_type,
            RecursionFlags::BOTH,
            IntersectionState::NONE,
        )?;
        self.optional_property_result(source, target, source_property, target_property, related)
    }

    fn optional_property_result(
        &self,
        _source: TypeId,
        _target: TypeId,
        source_property: SemanticSymbolId,
        target_property: SemanticSymbolId,
        related: Ternary,
    ) -> Result<Ternary, RelationUnavailable> {
        if related == Ternary::False {
            return Ok(Ternary::False);
        }
        let source_flags = self.property_symbol(source_property)?.flags();
        let target_flags = self.property_symbol(target_property)?.flags();
        if source_flags.intersects(SymbolFlags::OPTIONAL)
            && !target_flags.intersects(SymbolFlags::OPTIONAL)
        {
            return Ok(Ternary::False);
        }
        Ok(related)
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
    ) -> Result<Option<SemanticSymbolId>, RelationUnavailable> {
        let target_symbol = self.property_symbol(target_property)?;
        let name = target_symbol.name();
        if let Some(members) = source_members.members {
            let table = self
                .store
                .symbol_table(members)
                .ok_or(RelationUnavailable::InvalidStructuredMembers(source))?;
            if let Some(property) = table.get(name) {
                self.property_symbol(property)?;
                return Ok(Some(property));
            }
        }
        self.global_object_property(name)
    }

    fn global_object_property(
        &self,
        name: ts_binder::EscapedNameRef<'_>,
    ) -> Result<Option<SemanticSymbolId>, RelationUnavailable> {
        let Some(global_object_type) = self.global_object_type()? else {
            return Ok(None);
        };
        self.ensure_supported_object_kind(global_object_type)?;
        let record = self
            .store
            .type_payload(global_object_type)
            .ok_or(RelationUnavailable::Type(global_object_type))?;
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
        self.property_symbol(property)?;
        Ok(Some(property))
    }

    fn global_object_type(&self) -> Result<Option<TypeId>, RelationUnavailable> {
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
        let global_object = self
            .store
            .get_merged_symbol(global_object)
            .ok_or(RelationUnavailable::Symbol(global_object))?;
        let Some(global_object_type) = self
            .store
            .declared_type_links(global_object)
            .and_then(|links| links.declared_type)
        else {
            return Err(RelationUnavailable::UnresolvedGlobalObject(global_object));
        };
        Ok(Some(global_object_type))
    }

    fn property_symbol(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<&ts_binder::semantic::Symbol, RelationUnavailable> {
        let record = self
            .store
            .symbol(symbol)
            .ok_or(RelationUnavailable::Symbol(symbol))?;
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
            if !parent
                .flags()
                .intersects(SymbolFlags::INTERFACE | SymbolFlags::TYPE_LITERAL)
            {
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
        if self.relation == RelationKind::Assignable
            && source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::OBJECT)
        {
            self.ensure_supported_object_kind(source)?;
            self.ensure_supported_object_kind(target)?;
            return Ok(());
        }
        Err(RelationUnavailable::StructuralRelation {
            source,
            target,
            relation: self.relation,
        })
    }

    fn ensure_supported_object_kind(&self, type_id: TypeId) -> Result<(), RelationUnavailable> {
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
        if record.flags() != TypeFlags::OBJECT || record.alias().is_some() {
            return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
        }
        let kind = record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK;
        if kind != ObjectFlags::NONE
            && kind != ObjectFlags::INTERFACE
            && kind != ObjectFlags::ANONYMOUS
        {
            return Err(RelationUnavailable::UnsupportedStructuredType(type_id));
        }
        let unsupported_flags = ObjectFlags::CLASS
            | ObjectFlags::REFERENCE
            | ObjectFlags::TUPLE
            | ObjectFlags::MAPPED
            | ObjectFlags::REVERSE_MAPPED
            | ObjectFlags::EVOLVING_ARRAY
            | ObjectFlags::INSTANTIATED
            | ObjectFlags::OBJECT_LITERAL
            | ObjectFlags::FRESH_LITERAL
            | ObjectFlags::ARRAY_LITERAL
            | ObjectFlags::JSX_ATTRIBUTES
            | ObjectFlags::UNRESOLVED_MEMBERS;
        if record.object_flags().intersects(unsupported_flags) {
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

    fn resolved_object_members(
        &self,
        type_id: TypeId,
    ) -> Result<ResolvedObjectMembers, RelationUnavailable> {
        self.ensure_supported_object_kind(type_id)?;
        let record = self
            .store
            .type_payload(type_id)
            .ok_or(RelationUnavailable::Type(type_id))?;
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
            self.property_symbol(*property)?;
        }
        match structured.members {
            None if properties.is_empty() => {}
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
                    let symbol = self.property_symbol(property)?;
                    if symbol.name() != name || !property_set.contains(&property) {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                    }
                }
                for property in &properties {
                    let symbol = self.property_symbol(*property)?;
                    if table.get(symbol.name()) != Some(*property) {
                        return Err(RelationUnavailable::InvalidStructuredMembers(type_id));
                    }
                }
            }
        }
        Ok(ResolvedObjectMembers {
            members: structured.members,
            properties,
        })
    }
}

impl SemanticStore<TypeRecord, TypeMapper> {
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
        let bootstrap = self.relation_bootstrap_facts()?;
        let source = self.regular_type_if_fresh(source)?;
        let target = self.regular_type_if_fresh(target)?;
        if source == target {
            return Ok(true);
        }

        let source_flags = self.type_flags(source)?;
        let target_flags = self.type_flags(target)?;
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

        if source_flags.intersects(TypeFlags::OBJECT) && target_flags.intersects(TypeFlags::OBJECT)
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
            let supported_object_relation = relation == RelationKind::Assignable
                && source_flags.intersects(TypeFlags::OBJECT)
                && target_flags.intersects(TypeFlags::OBJECT);
            if union_relation || supported_object_relation {
                let mut session = RelaterSession::new(self, relation, bootstrap);
                let result = session.is_related_to_ex(
                    source,
                    target,
                    RecursionFlags::BOTH,
                    IntersectionState::NONE,
                )?;
                return session.finish(source, target, result);
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
            wildcard_type: bootstrap.wildcard_type,
            any_function_type: bootstrap.any_function_type,
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

const fn bool_to_ternary(value: bool) -> Ternary {
    if value { Ternary::True } else { Ternary::False }
}

const fn union_validation_unavailable(
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
    use ts_binder::{EscapedName, SemanticSymbolId, SymbolData, SymbolFlags};
    use ts_jsnum::{Number, PseudoBigInt};

    use super::RelationUnavailable;
    use crate::semantic::{
        CanonicalTypeMapperStore, DeclaredTypeLinks, IntrinsicBootstrapOptions,
        MembersAndExportsLinks, MembersOrExportsResolutionKind, RelationComparisonResult,
        RelationKind, TypeId, ValueSymbolLinks,
        signatures::{SignatureFlags, Ternary},
        type_records::{LiteralValue, RegularLiteralLink, TypeData},
        types::{ObjectFlags, TypeFlags},
    };

    type TestStore = CanonicalTypeMapperStore;

    fn initialized(strict_null_checks: bool) -> TestStore {
        let mut store = TestStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks,
                exact_optional_property_types: false,
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

    fn install_global_object(store: &mut TestStore, object_type: TypeId) -> SemanticSymbolId {
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let object_symbol = alloc_symbol(store, SymbolFlags::INTERFACE, "Object");
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
        assert_eq!(
            store.is_type_comparable_to(source, target),
            Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: RelationKind::Comparable,
            })
        );
        assert_eq!(store.relation_state_snapshot(), before);
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
    fn optional_properties_are_exact_only_inside_the_supported_nullability_boundary() {
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
        let string = strict.intrinsic_bootstrap().unwrap().string_type;
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
        let before = strict.relation_state_snapshot();
        assert_eq!(
            strict.is_type_assignable_to(required_source, optional_target),
            Err(RelationUnavailable::StrictOptionalProperty(
                optional_target_property
            ))
        );
        assert_eq!(strict.relation_state_snapshot(), before);

        let optional_source_property = alloc_typed_property(&mut strict, "value", string, true);
        let optional_source = alloc_property_object(&mut strict, vec![optional_source_property]);
        let required_target_property = alloc_typed_property(&mut strict, "value", string, false);
        let required_target = alloc_property_object(&mut strict, vec![required_target_property]);
        let before = strict.relation_state_snapshot();
        assert_eq!(
            strict.is_type_assignable_to(optional_source, required_target),
            Err(RelationUnavailable::StrictOptionalProperty(
                optional_source_property
            ))
        );
        assert_eq!(strict.relation_state_snapshot(), before);
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
        let before_subtype = store.relation_state_snapshot();
        assert_eq!(
            store.is_type_subtype_of(source, target),
            Err(RelationUnavailable::StructuralRelation {
                source,
                target,
                relation: RelationKind::Subtype,
            })
        );
        assert_eq!(store.relation_state_snapshot(), before_subtype);
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
    fn global_object_fallback_distinguishes_absent_resolved_and_unresolved_states() {
        let mut absent = initialized(true);
        let string = absent.intrinsic_bootstrap().unwrap().string_type;
        let source = alloc_property_object(&mut absent, Vec::new());
        let target_property = alloc_typed_property(&mut absent, "custom", string, false);
        let target = alloc_property_object(&mut absent, vec![target_property]);
        assert_eq!(absent.is_type_assignable_to(source, target), Ok(false));

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
            Err(RelationUnavailable::UnresolvedGlobalObject(object_symbol))
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
        set_object_properties(&mut resolved, object_type, vec![global_property]);
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
        install_global_object(&mut unsupported, global_object);
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
