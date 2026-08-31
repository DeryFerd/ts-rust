//! Dependency-closed type instantiation.
//!
//! This is the first exact slice of pinned `instantiateTypeWorker`. It covers
//! primitive and literal leaves, direct type-parameter mapping, canonical
//! Array/ReadonlyArray references under an explicit target capability, direct
//! full-arity generic class/interface references, indexed accesses, generic
//! `keyof` indexes, authenticated selection-shaped mapped aliases, deferred
//! intersections, template literals, intrinsic string mappings, ordinary
//! property-object aliases, inline intersection objects, authenticated deferred
//! conditionals, closed declaration-owned values, and unions with canonical
//! alias arguments and union origins. Other object and signature instantiation
//! needs its owning caches and is rejected.

use std::collections::{HashMap, HashSet};

use super::{
    CanonicalGlobalTypes, TypeAliasId, TypeId, TypeMapperId,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
    bootstrap::LiteralTypeCacheError,
    conditional_types::{
        ConditionalAliasIdentity, ConditionalBranchSource, ConditionalRemapLookup,
        ConditionalRemapProjection, ConditionalRemapResult, ConditionalTypeError,
        cached_conditional_remap_with_source, cached_deferred_conditional_remap,
        cached_signature_conditional_result, conditional_alias_projection_with_array_targets,
        conditional_remap_projection_with_array_targets, conditional_remap_projection_with_source,
        conditional_signature_projection_with_array_targets, is_signature_conditional_source,
        remap_conditional_with_source, remap_deferred_conditional_with_session,
    },
    declared::{DeclaredTypeError, cached_ordinary_type_parameter_owner, type_list_key},
    indexed_access_types::{
        SourceAliasIndexedBoundPlan, SourceAliasIndexedReadMode, SourceAliasIndexedSelection,
        cached_deferred_indexed_access_type, get_instantiated_indexed_access_type,
    },
    instantiated_members::{
        closed_declared_function_type, instantiated_function_member_type_matches,
    },
    intersection_types::{
        DeferredIntersectionTypeProjection, IntersectionTypeCacheKey, IntersectionTypeError,
    },
    keyof_types::{
        NongenericKeyofError, cached_nongeneric_keyof_type, plan_nongeneric_keyof_type,
        plan_nongeneric_keyof_type_with_array_targets, resolve_nongeneric_keyof_type_with_session,
        validate_generic_keyof_index_type, validate_source_object_literal_for_keyof,
    },
    mapped_types::{
        MappedTypeError, MappedTypeModifiers, SupportedMappedAliasProjection,
        cached_source_mapped_lookup_instance, cached_supported_mapped_alias_instance,
        escaped_property_name_from_type, instantiate_source_mapped_lookup_instance,
        instantiate_supported_mapped_alias_instance_with_session, source_mapped_lookup_projection,
        supported_mapped_alias_projection,
    },
    mapper::{CanonicalTypeMapperStore, TypeMapperApplication},
    object_aliases::{
        InlinePropertyObjectProjection, PropertyObjectAliasProjection, SourceAliasOperandGraph,
        SourcePropertyObjectProjection, closed_declared_property_object_is_mapping_invariant,
        inline_property_object_projection, inline_property_object_template_matches,
        property_object_alias_identity_source_header, property_object_alias_projection,
        source_property_object_instance_flags_match, source_property_object_projection,
        validate_property_object_alias_arguments,
    },
    object_members::{
        DeclaredPropertyObjectValidation, validate_resolved_declared_property_object,
    },
    reference_types::{
        DirectGenericReference, DirectGenericReferenceError, create_direct_generic_reference,
        validate_direct_generic_reference,
    },
    store::SourceNodeParent,
    template_types::TemplateTypeError,
    type_nodes::type_alias_instantiation_cache_key,
    type_records::{StructuredTypeData, TypeCacheState, TypeData, TypeRecord},
    types::{AccessFlags, ObjectFlags, TypeFlags},
};
use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags};

/// Pinned checker limits for one instantiation query.
///
/// `max_depth` and `max_count` correspond to upstream's depth 100 and
/// per-expression count 5,000,000 guards. Standalone callers fail with a typed
/// error; a checker-owned recovering session substitutes its validated error
/// type and records the event for the eventual TS2589 diagnostic owner.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(dead_code)] // Installed ahead of the generic call/signature consumer.
pub(super) struct InstantiationLimits {
    pub max_depth: usize,
    pub max_count: usize,
}

impl Default for InstantiationLimits {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_count: 5_000_000,
        }
    }
}

/// A semantic dependency or guard that prevents exact instantiation.
#[derive(Debug, PartialEq)]
#[allow(dead_code)] // Installed ahead of the generic call/signature consumer.
pub(super) enum InstantiationError {
    InvalidType(TypeId),
    InvalidRecoveryType(TypeId),
    InvalidMapper(TypeMapperId),
    InvalidAlias(TypeAliasId),
    DepthLimit { depth: usize, limit: usize },
    CountLimit { count: usize, limit: usize },
    UnsupportedType(TypeId),
    UnsupportedAliasedUnion(TypeId),
    UnsupportedUnionOrigin(TypeId),
    UnsupportedUnionConstituent(TypeId),
    Array(ArrayTypeError),
    Reference(DirectGenericReferenceError),
    Template(TemplateTypeError),
    Union(LiteralTypeCacheError),
    Declared(DeclaredTypeError),
}

impl std::fmt::Display for InstantiationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidType(type_) => {
                write!(formatter, "cannot instantiate invalid type {type_:?}")
            }
            Self::InvalidRecoveryType(type_) => {
                write!(
                    formatter,
                    "cannot recover instantiation with foreign type {type_:?}"
                )
            }
            Self::InvalidMapper(mapper) => {
                write!(
                    formatter,
                    "cannot instantiate with invalid mapper {mapper:?}"
                )
            }
            Self::InvalidAlias(alias) => {
                write!(formatter, "cannot instantiate with invalid alias {alias:?}")
            }
            Self::DepthLimit { depth, limit } => write!(
                formatter,
                "type instantiation depth {depth} reached configured limit {limit}"
            ),
            Self::CountLimit { count, limit } => write!(
                formatter,
                "type instantiation count {count} reached configured limit {limit}"
            ),
            Self::UnsupportedType(type_) => {
                write!(
                    formatter,
                    "type {type_:?} is outside the installed instantiation slice"
                )
            }
            Self::UnsupportedAliasedUnion(type_) => write!(
                formatter,
                "union {type_:?} requires type-alias instantiation"
            ),
            Self::UnsupportedUnionOrigin(type_) => write!(
                formatter,
                "union {type_:?} requires named-union origin instantiation"
            ),
            Self::UnsupportedUnionConstituent(type_) => write!(
                formatter,
                "union constituent {type_:?} is outside the primitive/literal mapper slice"
            ),
            Self::Array(error) => error.fmt(formatter),
            Self::Reference(error) => error.fmt(formatter),
            Self::Template(error) => error.fmt(formatter),
            Self::Union(error) => error.fmt(formatter),
            Self::Declared(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for InstantiationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Array(error) => Some(error),
            Self::Reference(error) => Some(error),
            Self::Template(error) => Some(error),
            Self::Union(error) => Some(error),
            Self::Declared(error) => Some(error),
            _ => None,
        }
    }
}

impl From<LiteralTypeCacheError> for InstantiationError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Union(error)
    }
}

impl From<ArrayTypeError> for InstantiationError {
    fn from(error: ArrayTypeError) -> Self {
        Self::Array(error)
    }
}

impl From<DirectGenericReferenceError> for InstantiationError {
    fn from(error: DirectGenericReferenceError) -> Self {
        Self::Reference(error)
    }
}

impl From<TemplateTypeError> for InstantiationError {
    fn from(error: TemplateTypeError) -> Self {
        Self::Template(error)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum InstantiationCacheKey {
    Type {
        type_: TypeId,
        alias: InstantiationAliasCacheKey,
    },
    MappedOptional {
        template: TypeId,
        sentinel: TypeId,
    },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum InstantiationAliasCacheKey {
    None,
    Some {
        symbol: SemanticSymbolId,
        type_arguments: Vec<TypeId>,
    },
}

#[derive(Clone, Copy)]
enum InstantiationAliasInput<'a> {
    Stored(TypeAliasId),
    Borrowed(SemanticSymbolId, &'a [TypeId]),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InstantiationMappingIdentity {
    Stored(TypeMapperId),
    Vector {
        sources: usize,
        source_count: usize,
        targets: usize,
        target_count: usize,
    },
}

#[derive(Debug)]
struct ActiveMapperFrame {
    mapping: InstantiationMappingIdentity,
    cache: HashMap<InstantiationCacheKey, TypeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InstantiationLimitPolicy {
    FailFast,
    Recover { error_type: TypeId },
}

/// A point in the session's monotonic limit-event sequence.
///
/// Source-call checking records a mark before resolution and compares it after
/// resolution to decide whether that call owns a TS2589 diagnostic. A mark is
/// meaningful only when passed back to the same session that created it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[allow(dead_code)] // Installed ahead of the source-call diagnostic owner.
pub(super) struct InstantiationLimitEventMark(u64);

/// Exact object fields produced by a real argument-level recovery.
/// Only the anonymous-object producer can construct this record.
#[derive(Debug)]
#[cfg_attr(test, derive(Clone))]
pub(super) struct PropertyObjectAliasRecovery {
    result: TypeId,
    target: TypeId,
    declaration: NodeRef,
    source_symbol: SemanticSymbolId,
    alias_symbol: SemanticSymbolId,
    parameters: Vec<TypeId>,
    mapper: TypeMapperId,
    arguments: Vec<TypeId>,
    identity: TypeAliasId,
    identity_symbol: SemanticSymbolId,
    identity_arguments: Vec<TypeId>,
    error_type: TypeId,
    physical_recovery: Vec<bool>,
    identity_recovery: Vec<bool>,
}

impl PropertyObjectAliasRecovery {
    pub(super) const fn result(&self) -> TypeId {
        self.result
    }

    pub(super) const fn error_type(&self) -> TypeId {
        self.error_type
    }

    pub(super) fn physical_slot_recovered(&self, index: usize) -> bool {
        self.physical_recovery.get(index) == Some(&true)
    }

    pub(super) fn identity_slot_recovered(&self, index: usize) -> bool {
        self.identity_recovery.get(index) == Some(&true)
    }

    /// Check direct source and result fields without entering full projection.
    #[allow(clippy::too_many_lines)] // One retained record binds both independent argument lists.
    pub(super) fn matches_current_result(&self, store: &CanonicalTypeMapperStore) -> bool {
        if store.intrinsic_bootstrap().is_none_or(|bootstrap| {
            bootstrap.error_type != self.error_type
                || !store.type_payload(self.error_type).is_some_and(|record| {
                    record.flags() == TypeFlags::ANY
                        && matches!(record.data(), TypeData::Intrinsic(data) if data.intrinsic_name == "error")
                })
                || store.validate_union_constituent(self.error_type).is_err()
        }) || self.physical_recovery.len() != self.arguments.len()
            || self.identity_recovery.len() != self.identity_arguments.len()
            || !self
                .physical_recovery
                .iter()
                .chain(&self.identity_recovery)
                .any(|marked| *marked)
            || self
                .physical_recovery
                .iter()
                .zip(&self.arguments)
                .any(|(marked, argument)| *marked && *argument != self.error_type)
            || self
                .identity_recovery
                .iter()
                .zip(&self.identity_arguments)
                .any(|(marked, argument)| *marked && *argument != self.error_type)
            || validate_property_object_alias_arguments(store, &self.arguments).is_err()
            || validate_property_object_alias_arguments(store, &self.identity_arguments).is_err()
        {
            return false;
        }
        let Ok(source) = property_object_alias_identity_source_header(store, self.alias_symbol)
        else {
            return false;
        };
        let Some(body) = store.source_direct_type_annotation(source.alias_declaration) else {
            return false;
        };
        if source.parameters.len() != self.parameters.len()
            || source
                .parameters
                .iter()
                .zip(&self.parameters)
                .any(|((_, symbol), type_)| {
                    cached_ordinary_type_parameter_owner(store, *type_) != Some(*symbol)
                })
            || !super::object_aliases::property_object_alias_template_matches(
                store,
                self.alias_symbol,
                body,
                self.target,
                &self.parameters,
            )
            .is_ok_and(|matches| matches)
            || store.type_payload(self.target).and_then(TypeRecord::symbol)
                != Some(self.source_symbol)
            || store
                .symbol(self.source_symbol)
                .and_then(ts_binder::semantic::Symbol::declarations)
                != Some(&[self.declaration])
            || store.source_declaration_symbol(self.declaration) != Some(self.source_symbol)
            || store.source_node_kind(self.declaration) != Some(SyntaxKind::TypeLiteral)
            || !property_object_alias_identity_source_header(store, self.identity_symbol)
                .is_ok_and(|header| header.parameters.len() == self.identity_arguments.len())
        {
            return false;
        }
        let Some(record) = store.type_payload(self.result) else {
            return false;
        };
        let TypeData::Object(object) = record.data() else {
            return false;
        };
        let Some(alias) = store.type_alias(self.identity) else {
            return false;
        };
        let Some(global_identity) = store
            .symbol_store()
            .assigned_global_symbol_id(self.identity_symbol)
        else {
            return false;
        };
        self.result != self.target
            && record.flags() == TypeFlags::OBJECT
            && record.symbol() == Some(self.source_symbol)
            && record
                .object_flags()
                .contains(ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATED)
            && object.target == Some(self.target)
            && object.mapper == Some(self.mapper)
            && object.instantiations == TypeCacheState::Unallocated
            && record.alias() == Some(self.identity)
            && alias.symbol() == Some(self.identity_symbol)
            && alias.type_arguments()
                == (!self.identity_arguments.is_empty())
                    .then_some(self.identity_arguments.as_slice())
            && store.type_mapper_has_exact_endpoints(self.mapper, &self.parameters, &self.arguments)
                == Some(true)
            && store.relation_object_instantiation(
                self.target,
                type_alias_instantiation_cache_key(
                    &self.arguments,
                    Some((global_identity, &self.identity_arguments)),
                ),
            ) == Some(self.result)
    }
}

/// Physical arguments recovered by the unaliased inline-object producer.
/// A lexical parameter owner is not a display alias for this object.
#[derive(Debug)]
#[cfg_attr(test, derive(Clone))]
pub(super) struct InlinePropertyObjectRecovery {
    result: TypeId,
    target: TypeId,
    declaration: NodeRef,
    source_symbol: SemanticSymbolId,
    parameter_owner: SemanticSymbolId,
    parameters: Vec<TypeId>,
    mapper: TypeMapperId,
    arguments: Vec<TypeId>,
    error_type: TypeId,
    physical_recovery: Vec<bool>,
}

impl InlinePropertyObjectRecovery {
    pub(super) const fn result(&self) -> TypeId {
        self.result
    }

    pub(super) const fn error_type(&self) -> TypeId {
        self.error_type
    }

    pub(super) fn physical_slot_recovered(&self, index: usize) -> bool {
        self.physical_recovery.get(index) == Some(&true)
    }

    /// Checks source and result fields without entering the full projection.
    pub(super) fn matches_current_result(&self, store: &CanonicalTypeMapperStore) -> bool {
        if store.intrinsic_bootstrap().is_none_or(|bootstrap| {
            bootstrap.error_type != self.error_type
                || !store.type_payload(self.error_type).is_some_and(|record| {
                    record.flags() == TypeFlags::ANY
                        && matches!(record.data(), TypeData::Intrinsic(data) if data.intrinsic_name == "error")
                })
                || store.validate_union_constituent(self.error_type).is_err()
        }) || self.parameters.is_empty()
            || self.arguments.len() != self.parameters.len()
            || self.physical_recovery.len() != self.arguments.len()
            || !self.physical_recovery.iter().any(|marked| *marked)
            || self
                .physical_recovery
                .iter()
                .zip(&self.arguments)
                .any(|(marked, argument)| *marked && *argument != self.error_type)
            || validate_property_object_alias_arguments(store, &self.arguments).is_err()
            || !inline_property_object_template_matches(
                store,
                self.declaration,
                self.target,
                self.parameter_owner,
                &self.parameters,
            )
            .is_ok_and(|matches| matches)
            || store.type_payload(self.target).and_then(TypeRecord::symbol)
                != Some(self.source_symbol)
            || store
                .symbol(self.source_symbol)
                .and_then(ts_binder::semantic::Symbol::declarations)
                != Some(&[self.declaration])
            || store.source_declaration_symbol(self.declaration) != Some(self.source_symbol)
            || store.source_node_kind(self.declaration) != Some(SyntaxKind::TypeLiteral)
        {
            return false;
        }
        let Some(record) = store.type_payload(self.result) else {
            return false;
        };
        let TypeData::Object(object) = record.data() else {
            return false;
        };
        self.result != self.target
            && record.flags() == TypeFlags::OBJECT
            && record.symbol() == Some(self.source_symbol)
            && record.alias().is_none()
            && object.target == Some(self.target)
            && object.mapper == Some(self.mapper)
            && object.instantiations == TypeCacheState::Unallocated
            && source_property_object_instance_flags_match(
                store,
                record.object_flags(),
                &self.arguments,
            )
            .is_ok_and(|matches| matches)
            && store.type_mapper_has_exact_endpoints(self.mapper, &self.parameters, &self.arguments)
                == Some(true)
            && store.relation_object_instantiation(
                self.target,
                type_alias_instantiation_cache_key(&self.arguments, None),
            ) == Some(self.result)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct IntersectionSlotLimitEvents {
    before: InstantiationLimitEventMark,
    after: InstantiationLimitEventMark,
}

impl IntersectionSlotLimitEvents {
    fn occurred(self) -> bool {
        self.after > self.before
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IntersectionObjectRecovery {
    None,
    Inline,
    DirectAlias,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct IntersectionObjectReceipt {
    source: SourcePropertyObjectProjection,
    result: SourcePropertyObjectProjection,
    recovery: IntersectionObjectRecovery,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct IntersectionConstituentReceipt {
    source: TypeId,
    result: TypeId,
    events: IntersectionSlotLimitEvents,
    object: Option<Box<IntersectionObjectReceipt>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct IntersectionAliasArgumentReceipt {
    source: TypeId,
    result: TypeId,
    events: IntersectionSlotLimitEvents,
    inherited: bool,
}

/// Exact slot results observed by one real ordinary-intersection mapper call.
/// Source queries retain this value with their actual alias request row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct OrdinaryIntersectionRecoveryReceipt {
    source: TypeId,
    source_key: IntersectionTypeCacheKey,
    parameters: Vec<TypeId>,
    arguments: Vec<TypeId>,
    alias_override: Option<(SemanticSymbolId, Vec<TypeId>)>,
    array_targets: Option<CanonicalArrayTargets>,
    error_type: TypeId,
    result: TypeId,
    result_key: IntersectionTypeCacheKey,
    constituents: Vec<IntersectionConstituentReceipt>,
    alias_arguments: Vec<IntersectionAliasArgumentReceipt>,
    inherited: Option<Box<Self>>,
}

impl OrdinaryIntersectionRecoveryReceipt {
    pub(super) const fn result(&self) -> TypeId {
        self.result
    }

    #[allow(clippy::too_many_arguments)] // Bind the receipt to the caller's complete mapping request.
    pub(super) fn matches_mapping_request(
        &self,
        store: &CanonicalTypeMapperStore,
        source: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
        alias_override: Option<(SemanticSymbolId, &[TypeId])>,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Result<bool, InstantiationError> {
        if self.source != source
            || self.parameters != parameters
            || self.arguments != arguments
            || self
                .alias_override
                .as_ref()
                .map(|(symbol, arguments)| (*symbol, arguments.as_slice()))
                != alias_override
        {
            return Ok(false);
        }
        self.validate_current_chain(store, array_targets)?;
        Ok(true)
    }

    fn validate_current_chain(
        &self,
        store: &CanonicalTypeMapperStore,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Result<(), InstantiationError> {
        let mut current = Some(self);
        let mut depth = 0;
        while let Some(receipt) = current {
            if depth == InstantiationLimits::default().max_depth {
                return Err(InstantiationError::UnsupportedType(self.source));
            }
            receipt.validate_current_result(store, receipt.array_targets)?;
            if receipt.array_targets != array_targets {
                receipt.validate_current_result(store, array_targets)?;
            }
            current = receipt.inherited.as_deref();
            depth += 1;
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)] // Ordered slots, exact keys, and inherited evidence form one proof.
    fn validate_current_result(
        &self,
        store: &CanonicalTypeMapperStore,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Result<(), InstantiationError> {
        let invalid = || InstantiationError::InvalidType(self.result);
        let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
        if self.error_type != bootstrap.error_type
            || self.result == self.error_type
            || self.parameters.len() != self.arguments.len()
            || self.parameters.is_empty()
            || self.parameters.iter().any(|parameter| cached_ordinary_type_parameter_owner(store, *parameter).is_none())
            || self.parameters.iter().copied().collect::<HashSet<_>>().len() != self.parameters.len()
            || store.validate_union_constituent(self.error_type).is_err()
            || !store.type_payload(self.error_type).is_some_and(|record| {
                record.flags() == TypeFlags::ANY
                    && matches!(record.data(), TypeData::Intrinsic(data) if data.intrinsic_name == "error")
            })
            || array_targets.is_some_and(|targets| {
                store.type_payload(targets.array_type()).is_none()
                    || store.type_payload(targets.readonly_array_type()).is_none()
            })
        {
            return Err(invalid());
        }
        validate_property_object_alias_arguments(store, &self.arguments).map_err(|_| invalid())?;
        let source = instantiable_intersection_projection(store, self.source, array_targets)?;
        let result = instantiable_intersection_projection(store, self.result, array_targets)?;
        if source.types != self.source_key.types
            || source.alias_symbol != self.source_key.alias_symbol
            || source.alias_arguments != self.source_key.alias_arguments
            || result.types != self.result_key.types
            || result.alias_symbol != self.result_key.alias_symbol
            || result.alias_arguments != self.result_key.alias_arguments
            || self.constituents.len() != source.types.len()
            || self.inherited.as_ref().is_some_and(|inherited| {
                inherited.result != self.source || inherited.result_key != self.source_key
            })
        {
            return Err(invalid());
        }
        let mut normalized = Vec::with_capacity(self.constituents.len());
        let mut last_event = None;
        let mut recovered = false;
        for (expected_source, slot) in source.types.iter().zip(&self.constituents) {
            if *expected_source != slot.source
                || slot.events.after < slot.events.before
                || last_event.is_some_and(|event| event != slot.events.before)
            {
                return Err(invalid());
            }
            last_event = Some(slot.events.after);
            recovered |= validate_intersection_constituent_receipt(
                store,
                slot,
                &self.parameters,
                &self.arguments,
                array_targets,
                self.error_type,
            )?;
            store
                .append_deferred_intersection_constituent_with_array_targets(
                    slot.result,
                    &mut normalized,
                    array_targets,
                )
                .map_err(|error| deferred_intersection_error(self.source, error))?;
        }
        if normalized != result.types {
            return Err(invalid());
        }
        if let Some((symbol, arguments)) = &self.alias_override {
            validate_borrowed_alias_input(store, self.source, *symbol, arguments)?;
            if !self.alias_arguments.is_empty()
                || result.alias_symbol != Some(*symbol)
                || result.alias_arguments != *arguments
            {
                return Err(invalid());
            }
        } else {
            if result.alias_symbol != source.alias_symbol
                || self.alias_arguments.len() != source.alias_arguments.len()
                || result.alias_arguments.len() != source.alias_arguments.len()
            {
                return Err(invalid());
            }
            for (index, ((source_argument, result_argument), slot)) in source
                .alias_arguments
                .iter()
                .zip(&result.alias_arguments)
                .zip(&self.alias_arguments)
                .enumerate()
            {
                if slot.source != *source_argument
                    || slot.result != *result_argument
                    || slot.events.after < slot.events.before
                    || last_event.is_some_and(|event| event != slot.events.before)
                {
                    return Err(invalid());
                }
                last_event = Some(slot.events.after);
                let inherited = self.inherited.as_ref().is_some_and(|inherited| {
                    inherited.alias_arguments.get(index).is_some_and(|prior| {
                        prior.result == self.error_type
                            && (prior.events.occurred() || prior.inherited)
                    }) && slot.source == self.error_type
                        && slot.result == self.error_type
                });
                if slot.inherited != inherited {
                    return Err(invalid());
                }
                if slot.events.occurred() || slot.inherited {
                    if slot.result != self.error_type {
                        return Err(invalid());
                    }
                    recovered = true;
                } else if cached_instantiation_with_vector(
                    store,
                    slot.source,
                    &self.parameters,
                    &self.arguments,
                    array_targets,
                    None,
                )? != Some(slot.result)
                {
                    return Err(invalid());
                }
            }
        }
        if !recovered {
            return Err(invalid());
        }
        Ok(())
    }
}

struct OrdinaryIntersectionReceiptBuilder {
    parameters: Vec<TypeId>,
    arguments: Vec<TypeId>,
    inherited: Option<Box<OrdinaryIntersectionRecoveryReceipt>>,
    receipt: Option<OrdinaryIntersectionRecoveryReceipt>,
}

struct IntersectionObjectSlotRecovery {
    kind: IntersectionObjectRecovery,
    error_type: TypeId,
    physical: Vec<bool>,
    identity: Vec<bool>,
}

fn intersection_object_slot_recovery(
    store: &CanonicalTypeMapperStore,
    projection: &SourcePropertyObjectProjection,
) -> Result<Option<IntersectionObjectSlotRecovery>, InstantiationError> {
    let invalid = || InstantiationError::InvalidType(projection.type_());
    match projection {
        SourcePropertyObjectProjection::Inline(source) => {
            let Some(recovery) = store.inline_property_object_recovery(source.type_) else {
                return Ok(None);
            };
            if recovery.result() != source.type_ || !recovery.matches_current_result(store) {
                return Err(invalid());
            }
            Ok(Some(IntersectionObjectSlotRecovery {
                kind: IntersectionObjectRecovery::Inline,
                error_type: recovery.error_type(),
                physical: (0..source.arguments.len())
                    .map(|slot| recovery.physical_slot_recovered(slot))
                    .collect(),
                identity: Vec::new(),
            }))
        }
        SourcePropertyObjectProjection::DirectAlias(source) => {
            let Some(recovery) = store.property_object_alias_recovery(source.type_) else {
                return Ok(None);
            };
            if recovery.result() != source.type_ || !recovery.matches_current_result(store) {
                return Err(invalid());
            }
            Ok(Some(IntersectionObjectSlotRecovery {
                kind: IntersectionObjectRecovery::DirectAlias,
                error_type: recovery.error_type(),
                physical: (0..source.arguments.len())
                    .map(|slot| recovery.physical_slot_recovered(slot))
                    .collect(),
                identity: (0..source.identity_arguments.len())
                    .map(|slot| recovery.identity_slot_recovered(slot))
                    .collect(),
            }))
        }
    }
}

#[allow(clippy::too_many_arguments)] // Check the two physical/display argument lists against their exact slot evidence.
fn intersection_recovered_argument_list_matches(
    store: &CanonicalTypeMapperStore,
    source: &[TypeId],
    actual: &[TypeId],
    recovered: &[bool],
    inherited: Option<&[bool]>,
    parameters: &[TypeId],
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    error_type: TypeId,
    events: IntersectionSlotLimitEvents,
) -> Result<bool, InstantiationError> {
    if source.len() != actual.len() || recovered.len() != actual.len() {
        return Ok(false);
    }
    for (index, ((source, actual), recovered)) in
        source.iter().zip(actual).zip(recovered).enumerate()
    {
        let expected = cached_instantiation_with_vector(
            store,
            *source,
            parameters,
            arguments,
            array_targets,
            None,
        )?;
        if *recovered {
            if *actual != error_type
                || !events.occurred()
                    && expected != Some(*actual)
                    && !(inherited.is_some_and(|slots| slots.get(index) == Some(&true))
                        && *source == error_type
                        && *actual == *source)
            {
                return Ok(false);
            }
        } else if expected != Some(*actual) {
            return Ok(false);
        }
    }
    Ok(true)
}

#[allow(clippy::too_many_lines)] // One saved constituent binds source fields, output fields, and exact recovery slots.
fn validate_intersection_constituent_receipt(
    store: &CanonicalTypeMapperStore,
    slot: &IntersectionConstituentReceipt,
    parameters: &[TypeId],
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    error_type: TypeId,
) -> Result<bool, InstantiationError> {
    let invalid = || InstantiationError::InvalidType(slot.result);
    let source = source_property_object_projection(store, slot.source).map_err(|_| invalid())?;
    let actual = source_property_object_projection(store, slot.result).map_err(|_| invalid())?;
    let Some(object) = &slot.object else {
        if source.is_some()
            || actual.is_some()
            || cached_instantiation_with_vector(
                store,
                slot.source,
                parameters,
                arguments,
                array_targets,
                None,
            )? != Some(slot.result)
        {
            return Err(invalid());
        }
        return Ok(slot.events.occurred());
    };
    if source.as_ref() != Some(&object.source)
        || actual.as_ref() != Some(&object.result)
        || object.source.type_() != slot.source
        || object.result.type_() != slot.result
        || object.source.target() != object.result.target()
        || object.source.source_symbol() != object.result.source_symbol()
        || object.source.parameter_owner() != object.result.parameter_owner()
        || object.source.parameters() != object.result.parameters()
        || object.source.display_identity().map(|(symbol, _)| symbol)
            != object.result.display_identity().map(|(symbol, _)| symbol)
    {
        return Err(invalid());
    }
    if object.recovery == IntersectionObjectRecovery::None {
        if cached_instantiation_with_vector(
            store,
            slot.source,
            parameters,
            arguments,
            array_targets,
            None,
        )? != Some(slot.result)
        {
            return Err(invalid());
        }
        return Ok(slot.events.occurred());
    }
    let recovery = intersection_object_slot_recovery(store, &object.result)?.ok_or_else(invalid)?;
    let inherited = intersection_object_slot_recovery(store, &object.source)?;
    if recovery.kind != object.recovery
        || recovery.error_type != error_type
        || inherited
            .as_ref()
            .is_some_and(|prior| prior.kind != recovery.kind || prior.error_type != error_type)
        || !intersection_recovered_argument_list_matches(
            store,
            object.source.arguments(),
            object.result.arguments(),
            &recovery.physical,
            inherited.as_ref().map(|prior| prior.physical.as_slice()),
            parameters,
            arguments,
            array_targets,
            error_type,
            slot.events,
        )?
        || !intersection_recovered_argument_list_matches(
            store,
            object.source.identity_arguments(),
            object.result.identity_arguments(),
            &recovery.identity,
            inherited.as_ref().map(|prior| prior.identity.as_slice()),
            parameters,
            arguments,
            array_targets,
            error_type,
            slot.events,
        )?
    {
        return Err(invalid());
    }
    Ok(true)
}

fn capture_intersection_constituent_receipt(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    source_object: Option<SourcePropertyObjectProjection>,
    result: TypeId,
    events: IntersectionSlotLimitEvents,
    builder: &OrdinaryIntersectionReceiptBuilder,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<IntersectionConstituentReceipt, InstantiationError> {
    let result_object = source_property_object_projection(store, result)
        .map_err(|_| InstantiationError::InvalidType(result))?;
    let object = match (source_object, result_object) {
        (Some(source), Some(result)) => {
            let actual_recovery = intersection_object_slot_recovery(store, &result)?;
            let source_recovery = intersection_object_slot_recovery(store, &source)?;
            if events.occurred() {
                let matches = if let Some(recovery) = &actual_recovery {
                    intersection_recovered_argument_list_matches(
                        store,
                        source.arguments(),
                        result.arguments(),
                        &recovery.physical,
                        source_recovery
                            .as_ref()
                            .map(|prior| prior.physical.as_slice()),
                        &builder.parameters,
                        &builder.arguments,
                        array_targets,
                        recovery.error_type,
                        events,
                    )? && intersection_recovered_argument_list_matches(
                        store,
                        source.identity_arguments(),
                        result.identity_arguments(),
                        &recovery.identity,
                        source_recovery
                            .as_ref()
                            .map(|prior| prior.identity.as_slice()),
                        &builder.parameters,
                        &builder.arguments,
                        array_targets,
                        recovery.error_type,
                        events,
                    )?
                } else {
                    cached_instantiation_with_vector(
                        store,
                        source.type_(),
                        &builder.parameters,
                        &builder.arguments,
                        array_targets,
                        None,
                    )? == Some(result.type_())
                };
                if !matches {
                    return Err(InstantiationError::UnsupportedType(source.type_()));
                }
            }
            let recovery = if events.occurred() || source_recovery.is_some() {
                actual_recovery.map_or(IntersectionObjectRecovery::None, |recovery| recovery.kind)
            } else {
                IntersectionObjectRecovery::None
            };
            Some(Box::new(IntersectionObjectReceipt {
                source,
                result,
                recovery,
            }))
        }
        (None, None) => None,
        _ => return Err(InstantiationError::UnsupportedType(source)),
    };
    if object.is_none()
        && cached_instantiation_with_vector(
            store,
            source,
            &builder.parameters,
            &builder.arguments,
            array_targets,
            None,
        )? != Some(result)
    {
        return Err(InstantiationError::UnsupportedType(source));
    }
    Ok(IntersectionConstituentReceipt {
        source,
        result,
        events,
        object,
    })
}

/// Checker-query-owned instantiation accounting and recursive mapper cache.
///
/// The per-query count is intentionally not reset by each instantiation call:
/// upstream shares it across all work caused by one checked source element or
/// expression. Query owners call [`Self::reset_query`] at that boundary. The
/// total count remains cumulative across resets, matching checker telemetry.
#[derive(Debug)]
#[allow(dead_code)] // Installed ahead of the source-element query owner.
pub(super) struct InstantiationSession {
    limits: InstantiationLimits,
    limit_policy: InstantiationLimitPolicy,
    limit_event_generation: u64,
    depth: usize,
    count: usize,
    total_count: usize,
    active_mappers: Vec<ActiveMapperFrame>,
}

impl InstantiationSession {
    /// Creates the compatibility policy used by standalone instantiation:
    /// limits fail immediately with a typed error.
    pub(super) fn new(limits: InstantiationLimits) -> Self {
        Self {
            limits,
            limit_policy: InstantiationLimitPolicy::FailFast,
            limit_event_generation: 0,
            depth: 0,
            count: 0,
            total_count: 0,
            active_mappers: Vec::new(),
        }
    }

    /// Creates a production policy that substitutes a store-owned canonical
    /// error type at the recursive boundary where a limit is reached.
    #[allow(dead_code)] // Installed ahead of the production checker-session owner.
    pub(super) fn new_recovering(
        store: &CanonicalTypeMapperStore,
        limits: InstantiationLimits,
        error_type: TypeId,
    ) -> Result<Self, InstantiationError> {
        if store.type_payload(error_type).is_none() {
            return Err(InstantiationError::InvalidRecoveryType(error_type));
        }
        Ok(Self {
            limits,
            limit_policy: InstantiationLimitPolicy::Recover { error_type },
            limit_event_generation: 0,
            depth: 0,
            count: 0,
            total_count: 0,
            active_mappers: Vec::new(),
        })
    }

    /// Starts the next source-element or expression query. Pinned query
    /// boundaries reset only this count; recursion depth and active mapper
    /// frames belong to the dynamic instantiation stack and must survive a
    /// re-entrant query boundary.
    #[allow(dead_code)] // Called by the future source-element query owner.
    pub(super) fn reset_query(&mut self) {
        self.count = 0;
    }

    /// Mirrors pinned `clearActiveMapperCaches` without changing the active
    /// mapper stack itself. Inference owns the eventual call site.
    #[allow(dead_code)] // Installed ahead of the inference query owner.
    pub(super) fn clear_active_mapper_caches(&mut self) {
        for frame in &mut self.active_mappers {
            frame.cache.clear();
        }
    }

    /// Records the current monotonic limit-event generation.
    #[allow(dead_code)] // Read by the future source-call diagnostic owner.
    pub(super) const fn limit_event_mark(&self) -> InstantiationLimitEventMark {
        InstantiationLimitEventMark(self.limit_event_generation)
    }

    #[cfg(test)]
    pub(super) const fn limit_event_count(&self) -> u64 {
        self.limit_event_generation
    }

    /// Whether a depth or count limit was reached after `mark`.
    #[allow(dead_code)] // Read by the future source-call diagnostic owner.
    pub(super) const fn limit_event_occurred_since(
        &self,
        mark: InstantiationLimitEventMark,
    ) -> bool {
        self.limit_event_generation > mark.0
    }

    /// The caller's recovery identity, without changing its budget or event state.
    pub(super) const fn recovery_error_type(&self) -> Option<TypeId> {
        match self.limit_policy {
            InstantiationLimitPolicy::FailFast => None,
            InstantiationLimitPolicy::Recover { error_type } => Some(error_type),
        }
    }

    fn handle_limit(
        &mut self,
        store: &CanonicalTypeMapperStore,
        error: InstantiationError,
    ) -> Result<TypeId, InstantiationError> {
        self.limit_event_generation = self
            .limit_event_generation
            .checked_add(1)
            .expect("instantiation limit-event generation overflowed");
        match self.limit_policy {
            InstantiationLimitPolicy::FailFast => Err(error),
            InstantiationLimitPolicy::Recover { error_type } => {
                if store.type_payload(error_type).is_none() {
                    Err(InstantiationError::InvalidRecoveryType(error_type))
                } else {
                    Ok(error_type)
                }
            }
        }
    }

    #[cfg(test)]
    pub(super) const fn query_count(&self) -> usize {
        self.count
    }

    /// Cumulative checker telemetry; unlike the query counter, this survives
    /// [`Self::reset_query`].
    #[allow(dead_code)] // Read by the future checker telemetry owner.
    pub(super) const fn total_count(&self) -> usize {
        self.total_count
    }
}

/// Instantiates one type through the dependency-closed mapper slice.
#[allow(dead_code)] // Installed ahead of the generic call/signature consumer.
pub(super) fn instantiate_type(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: TypeMapperId,
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_limits(store, type_, mapper, InstantiationLimits::default())
}

#[allow(dead_code)] // Configurable boundary used by checker-query integration and focused tests.
pub(super) fn instantiate_type_with_limits(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: TypeMapperId,
    limits: InstantiationLimits,
) -> Result<TypeId, InstantiationError> {
    let mut session = InstantiationSession::new(limits);
    instantiate_type_with_session(store, type_, mapper, None, &mut session)
}

/// Instantiates inside an existing checker query. The caller owns the
/// [`InstantiationSession::reset_query`] boundary.
#[allow(dead_code)] // Installed ahead of the source-element query owner.
pub(super) fn instantiate_type_with_session(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    if store.mapper_payload(mapper).is_none() {
        return Err(InstantiationError::InvalidMapper(mapper));
    }
    instantiate_type_with_alias(
        store,
        type_,
        InstantiationMapping::Stored(mapper),
        array_targets,
        None,
        session,
    )
}

/// Instantiates through the exact parallel vectors used by `newTypeMapper`
/// without publishing a mapper record.
///
/// Generic-call inference needs to project parameter and return types before
/// the owning signature cache is ready to commit. Keeping this representation
/// borrowed makes that resolution phase independent of mapper/signature cache
/// publication while preserving the pinned mapper's first-match behavior.
#[allow(dead_code)] // Retained for non-query callers and focused mapper tests.
pub(super) fn instantiate_type_with_vector(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_vector_and_optional_array_targets(store, type_, sources, targets, None)
}

/// Vector instantiation with retained canonical `Array` targets.
#[allow(dead_code)] // Retained for non-query callers and focused mapper tests.
pub(super) fn instantiate_type_with_vector_and_array_targets(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    array_targets: CanonicalArrayTargets,
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_vector_and_optional_array_targets(
        store,
        type_,
        sources,
        targets,
        Some(array_targets),
    )
}

fn instantiate_type_with_vector_and_optional_array_targets(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, InstantiationError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    instantiate_type_with_vector_and_session(
        store,
        type_,
        sources,
        targets,
        array_targets,
        &mut session,
    )
}

/// Instantiates through a borrowed vector inside an existing checker query.
///
/// The caller owns the [`InstantiationSession::reset_query`] boundary.
/// Existing visible alias arguments are mapped in the same session.
#[allow(dead_code)] // Installed ahead of the lazy generic-call consumer.
pub(super) fn instantiate_type_with_vector_and_session(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_vector_and_alias_and_session(
        store,
        type_,
        sources,
        targets,
        array_targets,
        None,
        session,
    )
}

/// Uses the ordinary mapper with one source-owned bound or default graph.
pub(super) fn instantiate_source_alias_operand_with_session(
    store: &mut CanonicalTypeMapperStore,
    graph: &SourceAliasOperandGraph,
    source_type: TypeId,
    formal_ids: &[TypeId],
    argument_ids: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    validate_source_alias_operand_mapping(
        store,
        graph,
        source_type,
        formal_ids,
        argument_ids,
        array_targets,
    )?;
    instantiate_type_with_alias_input_and_operand(
        store,
        source_type,
        InstantiationMapping::Vector {
            sources: formal_ids,
            targets: argument_ids,
        },
        array_targets,
        None,
        session,
        None,
        None,
        Some(graph),
    )
}

/// Replays the same source and mapper proof without allocating a type or mapper.
pub(super) fn cached_source_alias_operand_instantiation(
    store: &CanonicalTypeMapperStore,
    graph: &SourceAliasOperandGraph,
    source_type: TypeId,
    formal_ids: &[TypeId],
    argument_ids: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, InstantiationError> {
    validate_source_alias_operand_mapping(
        store,
        graph,
        source_type,
        formal_ids,
        argument_ids,
        array_targets,
    )?;
    cached_instantiated_type_with_operand_worker(
        store,
        source_type,
        InstantiationMapping::Vector {
            sources: formal_ids,
            targets: argument_ids,
        },
        array_targets,
        None,
        &mut HashSet::new(),
        None,
        Some(graph),
    )
}

fn validate_source_alias_operand_mapping(
    store: &CanonicalTypeMapperStore,
    graph: &SourceAliasOperandGraph,
    source_type: TypeId,
    formal_ids: &[TypeId],
    argument_ids: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), InstantiationError> {
    let invalid = || InstantiationError::InvalidType(source_type);
    graph
        .validate_retained(store, source_type, array_targets)
        .map_err(|_| invalid())?;
    if formal_ids.len() != argument_ids.len()
        || argument_ids
            .iter()
            .any(|&type_| store.type_payload(type_).is_none())
    {
        return Err(invalid());
    }
    let source = graph.source();
    let parameters = source.parameters();
    let selected_index = parameters
        .iter()
        .position(|&parameter| parameter == source.parameter())
        .ok_or_else(invalid)?;
    let matches = |type_, (declaration, symbol)| {
        cached_ordinary_type_parameter_owner(store, type_) == Some(symbol)
            && store.source_declaration_symbol(declaration) == Some(symbol)
            && store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                == Some(type_)
    };
    let prefix = (formal_ids.len() == parameters.len() || formal_ids.len() == selected_index)
        && formal_ids
            .iter()
            .zip(parameters)
            .all(|(&type_, &parameter)| matches(type_, parameter));
    let selected = matches!(formal_ids, [type_] if matches(*type_, source.parameter()));
    if !prefix && !selected {
        return Err(invalid());
    }
    Ok(())
}

struct InstantiationSource<'a> {
    globals: &'a CanonicalGlobalTypes,
    branches: &'a mut dyn ConditionalBranchSource,
}

pub(super) fn instantiate_type_with_vector_and_source(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
) -> Result<TypeId, InstantiationError> {
    if sources.len() != targets.len() {
        return Err(InstantiationError::InvalidType(type_));
    }
    for endpoint in sources.iter().chain(targets) {
        if store.type_payload(*endpoint).is_none() {
            return Err(InstantiationError::InvalidType(*endpoint));
        }
    }
    instantiate_type_with_alias_input_and_source(
        store,
        type_,
        InstantiationMapping::Vector { sources, targets },
        Some(CanonicalArrayTargets::from_global_types(globals)),
        None,
        session,
        None,
        Some(&mut InstantiationSource {
            globals,
            branches: source,
        }),
    )
}

pub(super) fn instantiate_type_with_source(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: TypeMapperId,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
) -> Result<TypeId, InstantiationError> {
    if store.mapper_payload(mapper).is_none() {
        return Err(InstantiationError::InvalidMapper(mapper));
    }
    instantiate_type_with_alias_input_and_source(
        store,
        type_,
        InstantiationMapping::Stored(mapper),
        Some(CanonicalArrayTargets::from_global_types(globals)),
        None,
        session,
        None,
        Some(&mut InstantiationSource {
            globals,
            branches: source,
        }),
    )
}

/// Instantiates one root with a borrowed alias identity in the caller's session.
/// Child substitutions do not inherit the override or remap its arguments.
pub(super) fn instantiate_type_with_vector_and_alias_and_session(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    if sources.len() != targets.len() {
        return Err(InstantiationError::InvalidType(type_));
    }
    for endpoint in sources.iter().chain(targets) {
        if store.type_payload(*endpoint).is_none() {
            return Err(InstantiationError::InvalidType(*endpoint));
        }
    }
    instantiate_type_with_alias_input(
        store,
        type_,
        InstantiationMapping::Vector { sources, targets },
        array_targets,
        alias_override
            .map(|(symbol, arguments)| InstantiationAliasInput::Borrowed(symbol, arguments)),
        session,
    )
}

/// Uses the normal caller frame and retains only real intersection recovery.
#[allow(clippy::too_many_arguments)] // Keep the source request, capability, and caller session together.
pub(super) fn instantiate_ordinary_intersection_with_vector_and_alias_and_session(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    inherited: Option<&OrdinaryIntersectionRecoveryReceipt>,
    session: &mut InstantiationSession,
) -> Result<(TypeId, Option<OrdinaryIntersectionRecoveryReceipt>), InstantiationError> {
    if parameters.len() != arguments.len() {
        return Err(InstantiationError::InvalidType(source));
    }
    for endpoint in parameters.iter().chain(arguments) {
        if store.type_payload(*endpoint).is_none() {
            return Err(InstantiationError::InvalidType(*endpoint));
        }
    }
    let mut builder = OrdinaryIntersectionReceiptBuilder {
        parameters: parameters.to_vec(),
        arguments: arguments.to_vec(),
        inherited: inherited.cloned().map(Box::new),
        receipt: None,
    };
    let result = instantiate_type_with_alias_input_and_receipt(
        store,
        source,
        InstantiationMapping::Vector {
            sources: parameters,
            targets: arguments,
        },
        array_targets,
        alias_override
            .map(|(symbol, arguments)| InstantiationAliasInput::Borrowed(symbol, arguments)),
        session,
        Some(&mut builder),
    )?;
    if let Some(receipt) = &builder.receipt
        && (receipt.result != result
            || !receipt.matches_mapping_request(
                store,
                source,
                parameters,
                arguments,
                alias_override,
                array_targets,
            )?)
    {
        return Err(InstantiationError::InvalidType(result));
    }
    Ok((result, builder.receipt))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MappedTemplateFrame {
    Optional { template: TypeId, sentinel: TypeId },
    Indexed(TypeId),
}

impl MappedTemplateFrame {
    const fn template(self) -> TypeId {
        match self {
            Self::Optional { template, .. } | Self::Indexed(template) => template,
        }
    }
}

/// Runs a caller-proved mapped template through the normal instantiation frame.
/// The caller keeps the same vector slices alive through all nested work.
pub(super) fn with_mapped_template_frame<E>(
    store: &mut CanonicalTypeMapperStore,
    frame: MappedTemplateFrame,
    sources: &[TypeId],
    targets: &[TypeId],
    session: &mut InstantiationSession,
    map_error: impl Fn(InstantiationError) -> E,
    work: impl FnOnce(&mut CanonicalTypeMapperStore, &mut InstantiationSession) -> Result<TypeId, E>,
) -> Result<TypeId, E> {
    if sources.len() != targets.len() {
        return Err(map_error(InstantiationError::InvalidType(frame.template())));
    }
    for endpoint in sources.iter().chain(targets) {
        if store.type_payload(*endpoint).is_none() {
            return Err(map_error(InstantiationError::InvalidType(*endpoint)));
        }
    }
    validate_mapped_template_frame(store, frame).map_err(&map_error)?;
    with_instantiation_frame(
        store,
        InstantiationMapping::Vector { sources, targets },
        session,
        |store| match frame {
            MappedTemplateFrame::Optional { template, sentinel } => {
                Ok(InstantiationCacheKey::MappedOptional { template, sentinel })
            }
            MappedTemplateFrame::Indexed(template) => {
                instantiation_cache_key(store, template, None)
            }
        },
        |_, _, _| Ok(()),
        map_error,
        |store, session, _| work(store, session),
    )
}

fn validate_mapped_template_frame(
    store: &CanonicalTypeMapperStore,
    frame: MappedTemplateFrame,
) -> Result<(), InstantiationError> {
    let template = frame.template();
    let record = store
        .type_payload(template)
        .ok_or(InstantiationError::InvalidType(template))?;
    let TypeData::IndexedAccess(indexed) = record.data() else {
        return Err(InstantiationError::InvalidType(template));
    };
    let computed_variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if record.flags() != TypeFlags::INDEXED_ACCESS
        || (record.object_flags() != ObjectFlags::NONE
            && record.object_flags() != computed_variable_flags)
        || record.symbol().is_some()
        || record.alias().is_some()
        || indexed.access_flags != AccessFlags::NONE
        || indexed.constrained.resolved_base_constraint.is_some()
    {
        return Err(InstantiationError::InvalidType(template));
    }
    if cached_deferred_indexed_access_type(
        store,
        indexed.object_type,
        indexed.index_type,
        indexed.access_flags,
    )
    .map_err(InstantiationError::InvalidType)?
        != Some(template)
    {
        return Err(InstantiationError::InvalidType(template));
    }
    if let MappedTemplateFrame::Optional { sentinel, .. } = frame {
        let record = store
            .type_payload(sentinel)
            .ok_or(InstantiationError::InvalidType(sentinel))?;
        if store
            .intrinsic_bootstrap()
            .is_none_or(|bootstrap| sentinel != bootstrap.undefined_or_missing_type)
            || record.flags() != TypeFlags::UNDEFINED
            || record.object_flags() != ObjectFlags::NONE
            || record.symbol().is_some()
            || record.alias().is_some()
            || !matches!(record.data(), TypeData::Intrinsic(intrinsic)
                if intrinsic.intrinsic_name == "undefined")
        {
            return Err(InstantiationError::InvalidType(sentinel));
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug)]
enum InstantiationMapping<'a> {
    Stored(TypeMapperId),
    Vector {
        sources: &'a [TypeId],
        targets: &'a [TypeId],
    },
}

impl InstantiationMapping<'_> {
    fn identity(self) -> InstantiationMappingIdentity {
        match self {
            Self::Stored(mapper) => InstantiationMappingIdentity::Stored(mapper),
            Self::Vector { sources, targets } => InstantiationMappingIdentity::Vector {
                sources: sources.as_ptr() as usize,
                source_count: sources.len(),
                targets: targets.as_ptr() as usize,
                target_count: targets.len(),
            },
        }
    }
}

fn instantiate_type_with_alias(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias: Option<TypeAliasId>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_alias_input(
        store,
        type_,
        mapping,
        array_targets,
        alias.map(InstantiationAliasInput::Stored),
        session,
    )
}

fn instantiate_type_with_alias_input(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias: Option<InstantiationAliasInput<'_>>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_alias_input_and_receipt(
        store,
        type_,
        mapping,
        array_targets,
        alias,
        session,
        None,
    )
}

fn instantiate_type_with_alias_input_and_receipt(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias: Option<InstantiationAliasInput<'_>>,
    session: &mut InstantiationSession,
    receipt: Option<&mut OrdinaryIntersectionReceiptBuilder>,
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_alias_input_and_source(
        store,
        type_,
        mapping,
        array_targets,
        alias,
        session,
        receipt,
        None,
    )
}

#[allow(clippy::too_many_arguments)] // Source queries share the same frame and mapper identity.
fn instantiate_type_with_alias_input_and_source(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias: Option<InstantiationAliasInput<'_>>,
    session: &mut InstantiationSession,
    receipt: Option<&mut OrdinaryIntersectionReceiptBuilder>,
    source: Option<&mut InstantiationSource<'_>>,
) -> Result<TypeId, InstantiationError> {
    instantiate_type_with_alias_input_and_operand(
        store,
        type_,
        mapping,
        array_targets,
        alias,
        session,
        receipt,
        source,
        None,
    )
}

#[allow(clippy::too_many_arguments)] // Both source proofs borrow the same ordinary mapper frame.
fn instantiate_type_with_alias_input_and_operand(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias: Option<InstantiationAliasInput<'_>>,
    session: &mut InstantiationSession,
    receipt: Option<&mut OrdinaryIntersectionReceiptBuilder>,
    source: Option<&mut InstantiationSource<'_>>,
    operand: Option<&SourceAliasOperandGraph>,
) -> Result<TypeId, InstantiationError> {
    if operand.is_none()
        && matches!(
            store.type_payload(type_).map(TypeRecord::data),
            Some(TypeData::Union(_))
        )
    {
        instantiable_union_source_types(store, type_, array_targets)?;
    }
    let conditional_source = source.as_ref().filter(|_| {
        matches!(
            store.type_payload(type_).map(TypeRecord::data),
            Some(TypeData::Conditional(_))
        )
    });
    let contains = if let Some(operand) = operand {
        !operand
            .mapping_type_is_closed(store, type_, array_targets)
            .map_err(|_| InstantiationError::InvalidType(type_))?
    } else if let Some(source) = conditional_source {
        conditional_remap_projection_with_source(store, type_, source.branches, array_targets)
            .map_err(|error| conditional_remap_error(type_, error))?;
        true
    } else {
        could_contain_installed_type_variables(store, type_, array_targets)?
    };
    if !contains {
        return Ok(type_);
    }
    // The frame invokes validation and work in sequence. Neither callback keeps
    // the source reader, and no source reader is installed in the session.
    let source = std::cell::RefCell::new(source);
    with_instantiation_frame(
        store,
        mapping,
        session,
        |store| instantiation_cache_key_for_input(store, type_, alias),
        |store, key, cached| {
            if operand.is_none()
                && !matches!(
                    store.type_payload(type_).map(TypeRecord::data),
                    Some(TypeData::Conditional(_))
                )
            {
                return Ok(());
            }
            let InstantiationCacheKey::Type { alias, .. } = key else {
                return Err(InstantiationError::InvalidType(type_));
            };
            let alias = match alias {
                InstantiationAliasCacheKey::None => None,
                InstantiationAliasCacheKey::Some {
                    symbol,
                    type_arguments,
                } => Some((*symbol, type_arguments.as_slice())),
            };
            let source = source.borrow();
            if cached_instantiated_type_with_operand_worker(
                store,
                type_,
                mapping,
                array_targets,
                alias,
                &mut HashSet::new(),
                source
                    .as_ref()
                    .map(|source| (source.globals, &*source.branches)),
                operand,
            )? != Some(cached)
            {
                return Err(InstantiationError::InvalidType(type_));
            }
            Ok(())
        },
        std::convert::identity,
        |store, session, key| {
            let InstantiationCacheKey::Type { alias, .. } = key else {
                return Err(InstantiationError::InvalidType(type_));
            };
            let alias = match alias {
                InstantiationAliasCacheKey::None => None,
                InstantiationAliasCacheKey::Some {
                    symbol,
                    type_arguments,
                } => Some((*symbol, type_arguments.as_slice())),
            };
            instantiate_type_worker(
                store,
                type_,
                mapping,
                array_targets,
                alias,
                session,
                receipt,
                source.borrow_mut().as_deref_mut(),
                operand,
            )
        },
    )
}

fn with_instantiation_frame<E>(
    store: &mut CanonicalTypeMapperStore,
    mapping: InstantiationMapping<'_>,
    session: &mut InstantiationSession,
    cache_key: impl FnOnce(
        &CanonicalTypeMapperStore,
    ) -> Result<InstantiationCacheKey, InstantiationError>,
    validate_cached: impl FnOnce(
        &CanonicalTypeMapperStore,
        &InstantiationCacheKey,
        TypeId,
    ) -> Result<(), InstantiationError>,
    map_error: impl Fn(InstantiationError) -> E,
    work: impl FnOnce(
        &mut CanonicalTypeMapperStore,
        &mut InstantiationSession,
        &InstantiationCacheKey,
    ) -> Result<TypeId, E>,
) -> Result<TypeId, E> {
    if session.depth == session.limits.max_depth {
        return session
            .handle_limit(
                store,
                InstantiationError::DepthLimit {
                    depth: session.depth,
                    limit: session.limits.max_depth,
                },
            )
            .map_err(map_error);
    }
    if session.count >= session.limits.max_count {
        return session
            .handle_limit(
                store,
                InstantiationError::CountLimit {
                    count: session.count,
                    limit: session.limits.max_count,
                },
            )
            .map_err(map_error);
    }

    // Rust IDs can carry foreign provenance, unlike the upstream pointers.
    // Validate the complete cache identity before mutating the dynamic stack.
    let key = cache_key(store).map_err(&map_error)?;
    let mapping_identity = mapping.identity();
    let existing_index = session
        .active_mappers
        .iter()
        .rposition(|frame| frame.mapping == mapping_identity);
    let frame_index = if let Some(index) = existing_index {
        index
    } else {
        session.active_mappers.push(ActiveMapperFrame {
            mapping: mapping_identity,
            cache: HashMap::new(),
        });
        session.active_mappers.len() - 1
    };
    if let Some(cached) = session.active_mappers[frame_index].cache.get(&key) {
        validate_cached(store, &key, *cached).map_err(map_error)?;
        return Ok(*cached);
    }

    session.total_count += 1;
    session.count += 1;
    session.depth += 1;
    let work_mark = session.limit_event_mark();
    let result = work(store, session, &key);
    if existing_index.is_none() {
        let popped = session
            .active_mappers
            .pop()
            .expect("a first active mapper owns its scratch cache");
        debug_assert_eq!(popped.mapping, mapping_identity);
    } else if let Ok(instantiated) = &result
        && !session.limit_event_occurred_since(work_mark)
    {
        // A recovered wrapper has no scratch-cache proof of its limit event.
        // Keep it out so a later caller must repeat that guarded work.
        session.active_mappers[frame_index]
            .cache
            .insert(key, *instantiated);
    }
    session.depth -= 1;
    result
}

fn instantiation_cache_key(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    alias: Option<TypeAliasId>,
) -> Result<InstantiationCacheKey, InstantiationError> {
    let alias = match alias {
        None => InstantiationAliasCacheKey::None,
        Some(alias_id) => {
            let alias = store
                .type_alias(alias_id)
                .ok_or(InstantiationError::InvalidAlias(alias_id))?;
            InstantiationAliasCacheKey::Some {
                symbol: alias
                    .symbol()
                    .ok_or(InstantiationError::InvalidAlias(alias_id))?,
                type_arguments: alias.type_arguments().unwrap_or_default().to_vec(),
            }
        }
    };
    Ok(InstantiationCacheKey::Type { type_, alias })
}

fn instantiation_cache_key_for_input(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    alias: Option<InstantiationAliasInput<'_>>,
) -> Result<InstantiationCacheKey, InstantiationError> {
    let (symbol, arguments) = match alias {
        None => return instantiation_cache_key(store, type_, None),
        Some(InstantiationAliasInput::Stored(identity)) => {
            return instantiation_cache_key(store, type_, Some(identity));
        }
        Some(InstantiationAliasInput::Borrowed(symbol, arguments)) => (symbol, arguments),
    };
    validate_borrowed_alias_input(store, type_, symbol, arguments)?;
    Ok(InstantiationCacheKey::Type {
        type_,
        alias: InstantiationAliasCacheKey::Some {
            symbol,
            type_arguments: arguments.to_vec(),
        },
    })
}

fn validate_borrowed_alias_input(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    symbol: SemanticSymbolId,
    arguments: &[TypeId],
) -> Result<(), InstantiationError> {
    if store.get_merged_symbol(symbol) != Some(symbol)
        || store
            .symbol(symbol)
            .is_none_or(|owner| !owner.flags().contains(SymbolFlags::TYPE_ALIAS))
        || arguments
            .iter()
            .any(|argument| store.type_payload(*argument).is_none())
    {
        return Err(InstantiationError::InvalidType(type_));
    }
    Ok(())
}

fn could_contain_installed_type_variables(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, InstantiationError> {
    could_contain_installed_type_variables_worker(store, type_, array_targets, &mut HashSet::new())
}

fn mapping_invariant_object_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, InstantiationError> {
    if closed_declared_property_object_is_mapping_invariant(store, type_)
        .map_err(|error| closed_mapping_identity_error(type_, error))?
    {
        return Ok(true);
    }
    if store.type_has_function_type_provenance(type_) {
        return closed_declared_function_type(store, type_, array_targets)
            .map_err(|error| closed_mapping_identity_error(type_, error));
    }
    Ok(false)
}

fn closed_mapping_identity_error(
    type_: TypeId,
    error: super::relater::RelationUnavailable,
) -> InstantiationError {
    use super::relater::RelationUnavailable;
    match error {
        RelationUnavailable::UnsupportedStructuredType(_)
        | RelationUnavailable::UnavailableCanonicalArrayTarget(_)
        | RelationUnavailable::UnresolvedStructuredMembers(_)
        | RelationUnavailable::UnresolvedFunctionType(_)
        | RelationUnavailable::UnresolvedSignatureReturn(_) => {
            InstantiationError::UnsupportedType(type_)
        }
        _ => InstantiationError::InvalidType(type_),
    }
}

fn instantiable_intersection_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<DeferredIntersectionTypeProjection, InstantiationError> {
    let record = store
        .type_payload(type_)
        .ok_or(InstantiationError::InvalidType(type_))?;
    if !record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        return store
            .validate_deferred_intersection_type_with_array_targets(type_, array_targets)
            .map_err(|error| deferred_intersection_error(type_, error));
    }
    let ready = store
        .validate_intersection_type_with_array_targets(type_, array_targets)
        .map_err(|error| deferred_intersection_error(type_, error))?;
    let key = store
        .intersection_keys_by_type
        .get(&type_)
        .ok_or(InstantiationError::InvalidType(type_))?;
    if key.types != ready.types || store.intersection_types.get(key) != Some(&type_) {
        return Err(InstantiationError::InvalidType(type_));
    }
    Ok(DeferredIntersectionTypeProjection {
        types: ready.types,
        alias_symbol: key.alias_symbol,
        alias_arguments: key.alias_arguments.clone(),
    })
}

fn could_contain_installed_type_variables_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    seen: &mut HashSet<TypeId>,
) -> Result<bool, InstantiationError> {
    if !seen.insert(type_) {
        // Deferred intersections must reject recursive graphs before any
        // mapped constituent can allocate a new generic reference.
        return if matches!(
            store.type_payload(type_).map(TypeRecord::data),
            Some(TypeData::Intersection(_))
        ) {
            Err(InstantiationError::UnsupportedType(type_))
        } else {
            Ok(true)
        };
    }
    let record = store
        .type_payload(type_)
        .ok_or(InstantiationError::InvalidType(type_))?;
    let result = match record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => Ok(false),
        TypeData::Object(_)
            if store
                .intrinsic_bootstrap()
                .is_some_and(|bootstrap| type_ == bootstrap.empty_type_literal_type) =>
        {
            if matches!(
                validate_resolved_declared_property_object(store, type_),
                DeclaredPropertyObjectValidation::Valid(_)
            ) {
                Ok(false)
            } else {
                Err(InstantiationError::UnsupportedType(type_))
            }
        }
        TypeData::Object(_) => {
            if mapping_invariant_object_type(store, type_, array_targets)? {
                Ok(false)
            } else if let Some(projection) = source_property_object_projection(store, type_)
                .map_err(|_| InstantiationError::InvalidType(type_))?
            {
                let identity_arguments =
                    if projection.arguments() == projection.identity_arguments() {
                        &[][..]
                    } else {
                        projection.identity_arguments()
                    };
                projection
                    .arguments()
                    .iter()
                    .chain(identity_arguments)
                    .try_fold(false, |contains, argument| {
                        Ok(contains
                            | could_contain_installed_type_variables_worker(
                                store,
                                *argument,
                                array_targets,
                                seen,
                            )?)
                    })
            } else if let Some(properties) =
                source_object_literal_property_types(store, type_, array_targets)?
            {
                properties.iter().try_fold(false, |contains, property| {
                    Ok(contains
                        | could_contain_installed_type_variables_worker(
                            store,
                            *property,
                            array_targets,
                            seen,
                        )?)
                })
            } else {
                Ok(true)
            }
        }
        TypeData::Index(_) => {
            let target = validate_generic_keyof_index_type(store, type_)
                .map_err(|error| instantiated_keyof_error(type_, error))?;
            could_contain_installed_type_variables_worker(store, target, array_targets, seen)
        }
        TypeData::Mapped(_) => {
            if let Some(projection) = source_mapped_lookup_projection(store, type_, array_targets)
                .map_err(|error| mapped_indexed_access_error(type_, error))?
            {
                projection
                    .arguments
                    .iter()
                    .try_fold(false, |contains, argument| {
                        Ok(contains
                            | could_contain_installed_type_variables_worker(
                                store,
                                *argument,
                                array_targets,
                                seen,
                            )?)
                    })
            } else {
                let projection = supported_mapped_alias_projection(store, type_, array_targets)
                    .map_err(|error| mapped_indexed_access_error(type_, error))?
                    .ok_or(InstantiationError::UnsupportedType(type_))?;
                projection
                    .arguments
                    .iter()
                    .chain(&projection.identity_arguments)
                    .try_fold(false, |contains, argument| {
                        Ok(contains
                            | could_contain_installed_type_variables_worker(
                                store,
                                *argument,
                                array_targets,
                                seen,
                            )?)
                    })
            }
        }
        TypeData::Conditional(_) => {
            conditional_remap_projection_with_array_targets(store, type_, array_targets)
                .map(|_| true)
                .map_err(|error| conditional_remap_error(type_, error))
        }
        TypeData::TemplateLiteral(template) => {
            if template.types.is_empty() || template.texts.len() != template.types.len() + 1 {
                Err(TemplateTypeError::InvalidTemplate(type_).into())
            } else {
                template
                    .types
                    .iter()
                    .try_fold(false, |contains, placeholder| {
                        Ok(contains
                            || could_contain_installed_type_variables_worker(
                                store,
                                *placeholder,
                                array_targets,
                                seen,
                            )?)
                    })
            }
        }
        TypeData::StringMapping(mapping) => {
            if record.symbol().is_none() {
                Err(InstantiationError::UnsupportedType(type_))
            } else {
                could_contain_installed_type_variables_worker(
                    store,
                    mapping.target,
                    array_targets,
                    seen,
                )
            }
        }
        TypeData::Union(data) => {
            let mut contains = false;
            for constituent in &data.union.types {
                contains |= could_contain_installed_type_variables_worker(
                    store,
                    *constituent,
                    array_targets,
                    seen,
                )?;
            }
            if !contains && let Some(alias_id) = record.alias() {
                let alias = store
                    .type_alias(alias_id)
                    .ok_or(InstantiationError::InvalidAlias(alias_id))?;
                if alias.symbol().is_none() {
                    return Err(InstantiationError::InvalidAlias(alias_id));
                }
                for argument in alias.type_arguments().unwrap_or_default() {
                    contains |= could_contain_installed_type_variables_worker(
                        store,
                        *argument,
                        array_targets,
                        seen,
                    )?;
                }
            }
            if !contains && let Some(origin) = data.origin {
                contains = could_contain_installed_type_variables_worker(
                    store,
                    origin,
                    array_targets,
                    seen,
                )?;
            }
            Ok(contains)
        }
        TypeData::Intersection(_) => {
            let projection = instantiable_intersection_projection(store, type_, array_targets)?;
            let mut contains = false;
            for constituent in projection.types.iter().chain(&projection.alias_arguments) {
                contains |= could_contain_installed_type_variables_worker(
                    store,
                    *constituent,
                    array_targets,
                    seen,
                )?;
            }
            Ok(contains)
        }
        TypeData::Interface(interface)
            if interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .is_none_or(Vec::is_empty) =>
        {
            Ok(false)
        }
        TypeData::TypeReference(_) | TypeData::Interface(_) => {
            if let Some(array_targets) = array_targets
                && let Some(reference) =
                    store.canonical_array_reference_with_targets(array_targets, type_)?
            {
                could_contain_installed_type_variables_worker(
                    store,
                    reference.element_type,
                    Some(array_targets),
                    seen,
                )
            } else {
                match validate_direct_generic_reference(store, type_) {
                    Ok(reference) => reference.type_arguments.into_iter().try_fold(
                        false,
                        |contains, argument| {
                            Ok(contains
                                || could_contain_installed_type_variables_worker(
                                    store,
                                    argument,
                                    array_targets,
                                    seen,
                                )?)
                        },
                    ),
                    Err(error) => Err(error.into()),
                }
            }
        }
        _ => Ok(true),
    };
    seen.remove(&type_);
    result
}

/// Concrete source objects can keep their identity. This does not admit
/// anonymous object substitution or replace the source and derived-cache proofs.
fn source_object_literal_property_types(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<Vec<TypeId>>, InstantiationError> {
    if !validate_source_object_literal_for_keyof(store, type_, array_targets)
        .map_err(|error| instantiated_keyof_error(type_, error))?
    {
        return Ok(None);
    }
    let structured = store
        .type_payload(type_)
        .and_then(|record| record.data().structured())
        .ok_or(InstantiationError::InvalidType(type_))?;
    structured
        .properties
        .as_deref()
        .unwrap_or_default()
        .iter()
        .map(|property| {
            store
                .value_symbol_links(*property)
                .and_then(|links| links.resolved_type)
                .ok_or(InstantiationError::InvalidType(type_))
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Some)
}

fn is_concrete_source_object_literal(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, InstantiationError> {
    let Some(properties) = source_object_literal_property_types(store, type_, array_targets)?
    else {
        return Ok(false);
    };
    let mut seen = HashSet::from([type_]);
    for property in properties {
        if could_contain_installed_type_variables_worker(store, property, array_targets, &mut seen)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Read-only proof for the value-type graph admitted by instantiated generic
/// interface properties.
///
/// This mirrors the exact families handled by [`instantiate_type_worker`].
/// Unlike the general predicate above, it also proves that every type
/// parameter belongs to the target interface's mapper domain. That prevents a
/// foreign or lexically captured parameter from being preserved by identity
/// and later masquerading as a successfully instantiated member.
pub(super) fn validate_instantiable_member_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), InstantiationError> {
    if mapper_parameters.is_empty()
        || mapper_parameters
            .iter()
            .any(|parameter| store.type_payload(*parameter).is_none())
        || mapper_parameters
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .len()
            != mapper_parameters.len()
    {
        return Err(InstantiationError::InvalidType(type_));
    }
    validate_instantiable_member_type_worker(
        store,
        type_,
        mapper_parameters,
        array_targets,
        &mut HashSet::new(),
    )
}

/// Proves the installed property-type domain and returns the pinned
/// `couldContainTypeVariables` classification used by `instantiateSymbol`.
pub(super) fn instantiable_member_type_contains_variables(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, InstantiationError> {
    validate_instantiable_member_type(store, type_, mapper_parameters, array_targets)?;
    could_contain_installed_type_variables(store, type_, array_targets)
}

fn authenticated_unique_symbol_identity(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
) -> bool {
    let TypeData::UniqueEsSymbol(unique) = record.data() else {
        return false;
    };
    let Some(symbol) = record.symbol() else {
        return false;
    };
    let Some(owner) = store.symbol(symbol) else {
        return false;
    };
    let Some(global_id) = store.symbol_store().assigned_global_symbol_id(symbol) else {
        return false;
    };
    let Some(suffix) = unique
        .name
        .as_bytes()
        .strip_prefix(b"\xFE@")
        .and_then(|name| name.strip_prefix(owner.name().as_bytes()))
        .and_then(|name| name.strip_prefix(b"@"))
    else {
        return false;
    };

    record.flags() == TypeFlags::UNIQUE_ES_SYMBOL
        && record.object_flags() == ObjectFlags::NONE
        && record.alias().is_none()
        && store.get_merged_symbol(symbol) == Some(symbol)
        && suffix == global_id.to_string().as_bytes()
        && store
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            == Some(type_)
}

fn authenticated_global_concat_array_reference(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<DirectGenericReference> {
    if !matches!(
        store.type_payload(type_)?.data(),
        TypeData::TypeReference(_)
    ) {
        return None;
    }
    let reference = validate_direct_generic_reference(store, type_).ok()?;
    if reference.type_arguments.len() != 1 {
        return None;
    }
    let target = store.type_payload(reference.target)?;
    let symbol = target.symbol()?;
    let owner = store.symbol(symbol)?;
    let global = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("ConcatArray"))?;
    (matches!(target.data(), TypeData::Interface(_))
        && target.object_flags().contains(ObjectFlags::INTERFACE)
        && owner.flags().contains(SymbolFlags::INTERFACE)
        && owner.name().as_utf8() == Some("ConcatArray")
        && store.get_merged_symbol(symbol) == store.get_merged_symbol(global))
    .then_some(reference)
}

fn authenticated_instantiable_interface_reference(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<DirectGenericReference> {
    let reference = validate_direct_generic_reference(store, type_).ok()?;
    if let Some(targets) = array_targets
        && [targets.array_type(), targets.readonly_array_type()].contains(&reference.target)
    {
        return store
            .canonical_array_reference_with_targets(targets, type_)
            .ok()?
            .map(|_| reference);
    }
    if let Some(concat) = authenticated_global_concat_array_reference(store, type_) {
        return Some(concat);
    }

    let target = store.type_payload(reference.target)?;
    let symbol = target.symbol()?;
    let owner = store.symbol(symbol)?;
    let declarations = owner.declarations()?;
    (matches!(target.data(), TypeData::Interface(_))
        && target.object_flags().contains(ObjectFlags::INTERFACE)
        && !target.object_flags().contains(ObjectFlags::CLASS)
        && owner.flags().contains(SymbolFlags::INTERFACE)
        && owner
            .flags()
            .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
            == SymbolFlags::NONE
        && owner.check_flags() == CheckFlags::NONE
        && store.get_merged_symbol(symbol) == Some(symbol)
        && store
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            == Some(reference.target)
        && !declarations.is_empty()
        && declarations.iter().all(|declaration| {
            store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
        }))
    .then_some(reference)
}

fn supported_instantiable_union_constituent(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, InstantiationError> {
    match store.type_payload(type_).map(TypeRecord::data) {
        Some(
            TypeData::Intrinsic(_)
            | TypeData::Literal(_)
            | TypeData::UniqueEsSymbol(_)
            | TypeData::TypeParameter(_)
            | TypeData::TemplateLiteral(_)
            | TypeData::StringMapping(_),
        ) => Ok(true),
        Some(TypeData::Index(_)) => validate_generic_keyof_index_type(store, type_)
            .map(|_| true)
            .map_err(|error| instantiated_keyof_error(type_, error)),
        Some(TypeData::Mapped(_)) => supported_mapped_alias_projection(store, type_, array_targets)
            .map(|projection| projection.is_some())
            .map_err(|error| mapped_indexed_access_error(type_, error)),
        Some(TypeData::IndexedAccess(_)) => Ok(store.validate_union_constituent(type_).is_ok()),
        Some(TypeData::TypeReference(_)) => {
            Ok(
                authenticated_instantiable_interface_reference(store, type_, array_targets)
                    .is_some(),
            )
        }
        Some(TypeData::Union(_)) => Ok(match array_targets {
            Some(targets) => store
                .validate_cached_union_result_with_array_targets(targets, type_, None)
                .is_ok(),
            None => store.validate_cached_union_result(type_, None).is_ok(),
        }),
        Some(TypeData::Object(_)) => {
            if mapping_invariant_object_type(store, type_, array_targets) == Ok(true)
                || matches!(source_property_object_projection(store, type_), Ok(Some(_)))
            {
                Ok(true)
            } else {
                is_concrete_source_object_literal(store, type_, array_targets)
            }
        }
        _ => Ok(false),
    }
}

fn validate_instantiable_member_type_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Result<(), InstantiationError> {
    if !active.insert(type_) {
        return Err(InstantiationError::UnsupportedType(type_));
    }
    let record = store
        .type_payload(type_)
        .ok_or(InstantiationError::InvalidType(type_))?;
    let result = match record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) => {
            if is_exact_optional_missing_type(store, type_) {
                Ok(())
            } else {
                store
                    .validate_union_constituent(type_)
                    .map_err(InstantiationError::Union)
            }
        }
        TypeData::UniqueEsSymbol(_) => {
            if authenticated_unique_symbol_identity(store, type_, record) {
                Ok(())
            } else {
                Err(InstantiationError::UnsupportedType(type_))
            }
        }
        TypeData::TypeParameter(_) if mapper_parameters.contains(&type_) => Ok(()),
        TypeData::Conditional(_) if is_signature_conditional_source(store, type_) => {
            let (projection, _) =
                conditional_signature_projection_with_array_targets(store, type_, array_targets)
                    .map_err(|error| conditional_remap_error(type_, error))?;
            projection.arguments().iter().try_for_each(|argument| {
                validate_instantiable_member_type_worker(
                    store,
                    *argument,
                    mapper_parameters,
                    array_targets,
                    active,
                )
            })
        }
        TypeData::Object(_) => {
            if mapping_invariant_object_type(store, type_, array_targets)? {
                Ok(())
            } else if let Some(projection) = source_property_object_projection(store, type_)
                .map_err(|_| InstantiationError::InvalidType(type_))?
            {
                let identity_arguments =
                    if projection.arguments() == projection.identity_arguments() {
                        &[][..]
                    } else {
                        projection.identity_arguments()
                    };
                projection
                    .arguments()
                    .iter()
                    .chain(identity_arguments)
                    .try_for_each(|argument| {
                        validate_instantiable_member_type_worker(
                            store,
                            *argument,
                            mapper_parameters,
                            array_targets,
                            active,
                        )
                    })
            } else if is_concrete_source_object_literal(store, type_, array_targets)? {
                Ok(())
            } else {
                Err(InstantiationError::UnsupportedType(type_))
            }
        }
        TypeData::Index(_) => {
            let target = validate_generic_keyof_index_type(store, type_)
                .map_err(|error| instantiated_keyof_error(type_, error))?;
            validate_instantiable_member_type_worker(
                store,
                target,
                mapper_parameters,
                array_targets,
                active,
            )
        }
        TypeData::Mapped(_) => {
            let projection = supported_mapped_alias_projection(store, type_, array_targets)
                .map_err(|error| mapped_indexed_access_error(type_, error))?
                .ok_or(InstantiationError::UnsupportedType(type_))?;
            projection
                .arguments
                .iter()
                .chain(&projection.identity_arguments)
                .try_for_each(|argument| {
                    validate_instantiable_member_type_worker(
                        store,
                        *argument,
                        mapper_parameters,
                        array_targets,
                        active,
                    )
                })
        }
        TypeData::IndexedAccess(indexed) => {
            if record.flags() != TypeFlags::INDEXED_ACCESS
                || record.symbol().is_some()
                || record.alias().is_some()
                || indexed.access_flags & !AccessFlags::PERSISTENT != AccessFlags::NONE
            {
                return Err(InstantiationError::InvalidType(type_));
            }
            validate_instantiable_member_type_worker(
                store,
                indexed.object_type,
                mapper_parameters,
                array_targets,
                active,
            )?;
            validate_instantiable_member_type_worker(
                store,
                indexed.index_type,
                mapper_parameters,
                array_targets,
                active,
            )
        }
        TypeData::TemplateLiteral(template) => {
            if template.types.is_empty() || template.texts.len() != template.types.len() + 1 {
                Err(TemplateTypeError::InvalidTemplate(type_).into())
            } else {
                template.types.iter().try_for_each(|placeholder| {
                    validate_instantiable_member_type_worker(
                        store,
                        *placeholder,
                        mapper_parameters,
                        array_targets,
                        active,
                    )
                })
            }
        }
        TypeData::StringMapping(mapping) => {
            let symbol = record
                .symbol()
                .ok_or(InstantiationError::UnsupportedType(type_))?;
            store.string_mapping_kind(symbol)?;
            validate_instantiable_member_type_worker(
                store,
                mapping.target,
                mapper_parameters,
                array_targets,
                active,
            )
        }
        TypeData::Union(data) => {
            instantiable_union_source_types(store, type_, array_targets)?;
            let contains_variables =
                could_contain_installed_type_variables(store, type_, array_targets)?;
            if (record.alias().is_some() || data.origin.is_some()) && !contains_variables {
                Ok(())
            } else {
                if data.union.types.len() < 2
                    || data
                        .union
                        .types
                        .iter()
                        .copied()
                        .collect::<HashSet<_>>()
                        .len()
                        != data.union.types.len()
                {
                    return Err(InstantiationError::UnsupportedUnionConstituent(type_));
                }
                if let Some(alias) = record.alias().and_then(|alias| store.type_alias(alias)) {
                    for argument in alias.type_arguments().unwrap_or_default() {
                        validate_instantiable_member_type_worker(
                            store,
                            *argument,
                            mapper_parameters,
                            array_targets,
                            active,
                        )?;
                    }
                }
                data.union.types.iter().try_for_each(|constituent| {
                    if !supported_instantiable_union_constituent(
                        store,
                        *constituent,
                        array_targets,
                    )? {
                        return Err(InstantiationError::UnsupportedUnionConstituent(
                            *constituent,
                        ));
                    }
                    validate_instantiable_member_type_worker(
                        store,
                        *constituent,
                        mapper_parameters,
                        array_targets,
                        active,
                    )
                })
            }
        }
        TypeData::TypeReference(_) | TypeData::Interface(_) => {
            if let Some(targets) = array_targets
                && let Some(reference) =
                    store.canonical_array_reference_with_targets(targets, type_)?
            {
                validate_instantiable_member_type_worker(
                    store,
                    reference.element_type,
                    mapper_parameters,
                    Some(targets),
                    active,
                )
            } else {
                let reference = validate_direct_generic_reference(store, type_)?;
                reference.type_arguments.iter().try_for_each(|argument| {
                    validate_instantiable_member_type_worker(
                        store,
                        *argument,
                        mapper_parameters,
                        array_targets,
                        active,
                    )
                })
            }
        }
        _ => Err(InstantiationError::UnsupportedType(type_)),
    };
    active.remove(&type_);
    result
}

fn is_exact_optional_missing_type(store: &CanonicalTypeMapperStore, type_: TypeId) -> bool {
    store.intrinsic_bootstrap().is_some_and(|bootstrap| {
        bootstrap.options.strict_null_checks
            && bootstrap.options.exact_optional_property_types
            && type_ == bootstrap.missing_type
    })
}

/// Checks an instantiated property result without allocating semantic records
/// or calling the normal, mutating instantiation path.
pub(super) fn instantiated_member_type_matches(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    actual: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, InstantiationError> {
    if store.mapper_payload(mapper).is_none() {
        return Err(InstantiationError::InvalidMapper(mapper));
    }
    if store.type_payload(actual).is_none() {
        return Err(InstantiationError::InvalidType(actual));
    }
    instantiated_member_type_matches_worker(
        store,
        template,
        actual,
        mapper,
        array_targets,
        &mut HashSet::new(),
    )
}

fn instantiated_member_type_matches_worker(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    actual: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Result<bool, InstantiationError> {
    if !active.insert(template) {
        return Err(InstantiationError::UnsupportedType(template));
    }
    let record = store
        .type_payload(template)
        .ok_or(InstantiationError::InvalidType(template))?;
    let result = match record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) => Ok(template == actual),
        TypeData::UniqueEsSymbol(_)
            if authenticated_unique_symbol_identity(store, template, record) =>
        {
            Ok(template == actual)
        }
        TypeData::TypeParameter(_) => cached_apply_mapping(
            store,
            template,
            InstantiationMapping::Stored(mapper),
            array_targets,
        )
        .map(|expected| expected == Some(actual)),
        TypeData::Conditional(_) if is_signature_conditional_source(store, template) => {
            cached_signature_conditional_type(store, template, mapper, array_targets, active)
                .map(|expected| expected == Some(actual))
        }
        TypeData::Object(_) if store.type_has_function_type_provenance(template) => {
            if mapping_invariant_object_type(store, template, array_targets)? {
                Ok(template == actual)
            } else {
                Ok(instantiated_function_member_type_matches(
                    store,
                    template,
                    actual,
                    mapper,
                    array_targets,
                ))
            }
        }
        TypeData::TemplateLiteral(_)
        | TypeData::StringMapping(_)
        | TypeData::Index(_)
        | TypeData::IndexedAccess(_)
        | TypeData::Mapped(_)
        | TypeData::Object(_) => cached_instantiated_member_type(
            store,
            template,
            mapper,
            array_targets,
            &mut HashSet::new(),
        )
        .map(|expected| expected == Some(actual)),
        TypeData::Union(_) => {
            instantiated_member_union_matches(store, template, actual, mapper, array_targets)
        }
        TypeData::TypeReference(_) | TypeData::Interface(_) => {
            if let Some(targets) = array_targets
                && let Some(source) =
                    store.canonical_array_reference_with_targets(targets, template)?
            {
                let actual = store.canonical_array_reference_with_targets(targets, actual)?;
                match actual {
                    Some(actual)
                        if source.readonly == actual.readonly
                            && source.array_literal == actual.array_literal =>
                    {
                        instantiated_member_type_matches_worker(
                            store,
                            source.element_type,
                            actual.element_type,
                            mapper,
                            array_targets,
                            active,
                        )
                    }
                    _ => Ok(false),
                }
            } else {
                let source = validate_direct_generic_reference(store, template)?;
                match validate_direct_generic_reference(store, actual) {
                    Ok(actual)
                        if source.target == actual.target
                            && source.type_arguments.len() == actual.type_arguments.len() =>
                    {
                        source
                            .type_arguments
                            .iter()
                            .zip(actual.type_arguments)
                            .try_fold(true, |matches, (source, actual)| {
                                if !matches {
                                    return Ok(false);
                                }
                                instantiated_member_type_matches_worker(
                                    store,
                                    *source,
                                    actual,
                                    mapper,
                                    array_targets,
                                    active,
                                )
                            })
                    }
                    Ok(_) | Err(_) => Ok(false),
                }
            }
        }
        _ => Err(InstantiationError::UnsupportedType(template)),
    };
    active.remove(&template);
    result
}

/// Reads the real method root cache with the same composed signature mapper.
fn cached_signature_conditional_type(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Result<Option<TypeId>, InstantiationError> {
    let (projection, _) =
        conditional_signature_projection_with_array_targets(store, template, array_targets)
            .map_err(|error| conditional_remap_error(template, error))?;
    let mapping = InstantiationMapping::Stored(mapper);
    let mut arguments = Vec::with_capacity(projection.arguments().len());
    for (parameter, argument) in projection.parameters().iter().zip(projection.arguments()) {
        let resolved = if parameter == argument {
            cached_apply_mapping(store, *parameter, mapping, array_targets)?
        } else {
            cached_instantiated_type_worker(store, *argument, mapping, array_targets, None, active)?
        };
        let Some(resolved) = resolved else {
            return Ok(None);
        };
        arguments.push(resolved);
    }
    cached_signature_conditional_result(store, &projection, &arguments, array_targets)
        .map_err(|error| conditional_remap_error(template, error))
}

fn cached_instantiated_member_type(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Result<Option<TypeId>, InstantiationError> {
    cached_instantiated_type_worker(
        store,
        template,
        InstantiationMapping::Stored(mapper),
        array_targets,
        None,
        active,
    )
}

/// Checks an alias instantiation cache before the mutable path can publish a result.
pub(super) fn cached_instantiation_with_vector(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
) -> Result<Option<TypeId>, InstantiationError> {
    if sources.len() != targets.len() {
        return Err(InstantiationError::InvalidType(template));
    }
    for type_ in sources.iter().chain(targets) {
        if store.type_payload(*type_).is_none() {
            return Err(InstantiationError::InvalidType(*type_));
        }
    }
    cached_instantiated_type_worker(
        store,
        template,
        InstantiationMapping::Vector { sources, targets },
        array_targets,
        alias_override,
        &mut HashSet::new(),
    )
}

fn cached_instantiated_type_worker(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    active: &mut HashSet<TypeId>,
) -> Result<Option<TypeId>, InstantiationError> {
    cached_instantiated_type_with_source_worker(
        store,
        template,
        mapping,
        array_targets,
        alias_override,
        active,
        None,
    )
}

pub(super) fn cached_instantiation_with_vector_and_source(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    sources: &[TypeId],
    targets: &[TypeId],
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<Option<TypeId>, InstantiationError> {
    if sources.len() != targets.len() {
        return Err(InstantiationError::InvalidType(template));
    }
    for endpoint in sources.iter().chain(targets) {
        if store.type_payload(*endpoint).is_none() {
            return Err(InstantiationError::InvalidType(*endpoint));
        }
    }
    cached_instantiated_type_with_source_worker(
        store,
        template,
        InstantiationMapping::Vector { sources, targets },
        Some(CanonicalArrayTargets::from_global_types(globals)),
        None,
        &mut HashSet::new(),
        Some((globals, source)),
    )
}

#[allow(clippy::too_many_arguments)] // Cached replay receives the same source capability as work.
fn cached_instantiated_type_with_source_worker(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    active: &mut HashSet<TypeId>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
) -> Result<Option<TypeId>, InstantiationError> {
    cached_instantiated_type_with_operand_worker(
        store,
        template,
        mapping,
        array_targets,
        alias_override,
        active,
        source,
        None,
    )
}

#[allow(clippy::too_many_arguments)] // Source operand replay uses the ordinary cached result matcher.
fn cached_instantiated_type_with_operand_worker(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    active: &mut HashSet<TypeId>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
    operand: Option<&SourceAliasOperandGraph>,
) -> Result<Option<TypeId>, InstantiationError> {
    if let Some(operand) = operand
        && operand
            .mapping_type_is_closed(store, template, array_targets)
            .map_err(|_| InstantiationError::InvalidType(template))?
    {
        return Ok(Some(template));
    }
    if !active.insert(template) {
        return Err(InstantiationError::UnsupportedType(template));
    }
    let record = store
        .type_payload(template)
        .ok_or(InstantiationError::InvalidType(template))?;
    let result = (|| match record.data() {
        TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => {
            Ok(Some(template))
        }
        TypeData::TypeParameter(_) => cached_apply_mapping(store, template, mapping, array_targets),
        TypeData::Index(_) => {
            let target = validate_generic_keyof_index_type(store, template)
                .map_err(|error| instantiated_keyof_error(template, error))?;
            let Some(target) = cached_instantiated_type_worker(
                store,
                target,
                mapping,
                array_targets,
                None,
                active,
            )?
            else {
                return Ok(None);
            };
            let plan = plan_nongeneric_keyof_type_with_array_targets(store, target, array_targets)
                .map_err(|error| instantiated_keyof_error(template, error))?;
            cached_nongeneric_keyof_type(store, &plan)
                .map_err(|error| instantiated_keyof_error(template, error))
        }
        TypeData::Mapped(_) => {
            if let Some(projection) =
                source_mapped_lookup_projection(store, template, array_targets)
                    .map_err(|error| mapped_indexed_access_error(template, error))?
            {
                if let Some((symbol, arguments)) = alias_override {
                    validate_borrowed_alias_input(store, template, symbol, arguments)?;
                    return Err(InstantiationError::UnsupportedType(template));
                }
                let mut arguments = Vec::with_capacity(projection.arguments.len());
                for argument in &projection.arguments {
                    let Some(mapped) = cached_instantiated_type_worker(
                        store,
                        *argument,
                        mapping,
                        array_targets,
                        None,
                        active,
                    )?
                    else {
                        return Ok(None);
                    };
                    arguments.push(mapped);
                }
                return cached_source_mapped_lookup_instance(
                    store,
                    &projection,
                    &arguments,
                    array_targets,
                )
                .map_err(|error| mapped_indexed_access_error(template, error));
            }
            let projection = supported_mapped_alias_projection(store, template, array_targets)
                .map_err(|error| mapped_indexed_access_error(template, error))?
                .ok_or(InstantiationError::UnsupportedType(template))?;
            cached_instantiated_mapped_alias(
                store,
                &projection,
                mapping,
                array_targets,
                alias_override,
                active,
            )
        }
        TypeData::Conditional(_) => {
            let projection = match source {
                Some((_, source)) => {
                    conditional_remap_projection_with_source(store, template, source, array_targets)
                }
                None => {
                    conditional_remap_projection_with_array_targets(store, template, array_targets)
                }
            }
            .map_err(|error| conditional_remap_error(template, error))?;
            cached_instantiated_deferred_conditional(
                store,
                &projection,
                mapping,
                array_targets,
                alias_override,
                active,
                source,
            )
        }
        TypeData::IndexedAccess(indexed) => {
            let object = cached_instantiated_type_with_source_worker(
                store,
                indexed.object_type,
                mapping,
                array_targets,
                None,
                active,
                source,
            )?;
            let index = cached_instantiated_type_with_source_worker(
                store,
                indexed.index_type,
                mapping,
                array_targets,
                None,
                active,
                source,
            )?;
            let (Some(object), Some(index)) = (object, index) else {
                return Ok(None);
            };
            match indexed_access_resolution(
                store,
                object,
                index,
                indexed.access_flags,
                array_targets,
            )? {
                IndexedAccessResolution::Type(type_) => Ok(Some(type_)),
                IndexedAccessResolution::TypeWithSentinel(type_, sentinel) => store
                    .cached_literal_union_type_with_alias(&[type_, sentinel], None, array_targets)
                    .map_err(Into::into),
                IndexedAccessResolution::Deferred => {
                    cached_deferred_indexed_access_type(store, object, index, indexed.access_flags)
                        .map_err(InstantiationError::InvalidType)
                }
                IndexedAccessResolution::Property(name) => {
                    let Some(structured) =
                        resolved_indexed_access_members(store, object, array_targets)?
                    else {
                        return Ok(None);
                    };
                    let property = structured
                        .members
                        .and_then(|members| store.symbol_table(members))
                        .and_then(|members| members.get(name.as_ref()));
                    let Some(property) = property else {
                        return Ok(None);
                    };
                    if !structured
                        .properties
                        .as_deref()
                        .unwrap_or_default()
                        .contains(&property)
                    {
                        return Err(InstantiationError::InvalidType(object));
                    }
                    let Some(value) = store
                        .value_symbol_links(property)
                        .and_then(|links| links.resolved_type)
                    else {
                        return Ok(None);
                    };
                    store
                        .type_payload(value)
                        .ok_or(InstantiationError::InvalidType(value))?;
                    match indexed_access_property_optional_sentinel(store, property, value)? {
                        Some(sentinel) => store
                            .cached_literal_union_type_with_alias(
                                &[value, sentinel],
                                None,
                                array_targets,
                            )
                            .map_err(Into::into),
                        None => Ok(Some(value)),
                    }
                }
            }
        }
        TypeData::TemplateLiteral(data) => {
            let mut types = Vec::with_capacity(data.types.len());
            for type_ in &data.types {
                let Some(mapped) = cached_instantiated_type_worker(
                    store,
                    *type_,
                    mapping,
                    array_targets,
                    None,
                    active,
                )?
                else {
                    return Ok(None);
                };
                types.push(mapped);
            }
            if types == data.types {
                Ok(Some(template))
            } else {
                store
                    .cached_resolved_template_literal_type(&data.texts, &types)
                    .map_err(Into::into)
            }
        }
        TypeData::StringMapping(data) => {
            let symbol = record
                .symbol()
                .ok_or(InstantiationError::UnsupportedType(template))?;
            let target = cached_instantiated_type_worker(
                store,
                data.target,
                mapping,
                array_targets,
                None,
                active,
            )?;
            match target {
                Some(target) if target == data.target => Ok(Some(template)),
                Some(target) => store
                    .cached_resolved_string_mapping_type(symbol, target)
                    .map_err(Into::into),
                None => Ok(None),
            }
        }
        TypeData::Union(_) => {
            let constituents = instantiable_union_source_types_with_operand(
                store,
                template,
                array_targets,
                operand,
            )?;
            if operand.is_none()
                && !could_contain_installed_type_variables(store, template, array_targets)?
            {
                return Ok(Some(template));
            }
            let mut types = Vec::with_capacity(constituents.len());
            for constituent in constituents {
                let Some(instantiated) = cached_instantiated_type_with_operand_worker(
                    store,
                    *constituent,
                    mapping,
                    array_targets,
                    None,
                    active,
                    None,
                    operand,
                )?
                else {
                    return Ok(None);
                };
                types.push(instantiated);
            }
            let source_alias = record
                .alias()
                .and_then(|identity| store.type_alias(identity));
            let mut arguments = Vec::new();
            let alias = if let Some(alias) = alias_override {
                Some(alias)
            } else if let Some(alias) = source_alias {
                for argument in alias.type_arguments().unwrap_or_default() {
                    let Some(mapped) = cached_instantiated_type_with_operand_worker(
                        store,
                        *argument,
                        mapping,
                        array_targets,
                        None,
                        active,
                        None,
                        operand,
                    )?
                    else {
                        return Ok(None);
                    };
                    arguments.push(mapped);
                }
                Some((
                    alias
                        .symbol()
                        .ok_or(InstantiationError::UnsupportedAliasedUnion(template))?,
                    arguments.as_slice(),
                ))
            } else {
                None
            };
            let original_alias = source_alias.and_then(|alias| {
                alias
                    .symbol()
                    .map(|symbol| (symbol, alias.type_arguments().unwrap_or_default()))
            });
            if types == constituents && alias == original_alias {
                return Ok(Some(template));
            }
            if alias.is_none()
                && types.iter().any(|type_| {
                    matches!(
                        store.type_payload(*type_).map(TypeRecord::data),
                        Some(TypeData::TemplateLiteral(_) | TypeData::StringMapping(_))
                    )
                })
            {
                store
                    .cached_template_result_union(&types)
                    .map_err(Into::into)
            } else {
                store
                    .cached_literal_union_type_with_alias(&types, alias, array_targets)
                    .map_err(Into::into)
            }
        }
        TypeData::Intersection(_) => cached_instantiated_intersection_type(
            store,
            template,
            mapping,
            array_targets,
            alias_override,
            active,
        ),
        TypeData::Interface(data)
            if data
                .reference
                .resolved_type_arguments
                .as_ref()
                .is_none_or(Vec::is_empty) =>
        {
            Ok(Some(template))
        }
        TypeData::Object(_)
            if store
                .intrinsic_bootstrap()
                .is_some_and(|bootstrap| bootstrap.empty_type_literal_type == template) =>
        {
            if matches!(
                validate_resolved_declared_property_object(store, template),
                DeclaredPropertyObjectValidation::Valid(_)
            ) {
                Ok(Some(template))
            } else {
                Err(InstantiationError::UnsupportedType(template))
            }
        }
        TypeData::Object(_) => {
            if mapping_invariant_object_type(store, template, array_targets)? {
                return Ok(Some(template));
            }
            let Some(projection) = source_property_object_projection(store, template)
                .map_err(|_| InstantiationError::InvalidType(template))?
            else {
                return if is_concrete_source_object_literal(store, template, array_targets)? {
                    Ok(Some(template))
                } else {
                    Err(InstantiationError::UnsupportedType(template))
                };
            };
            if matches!(&projection, SourcePropertyObjectProjection::Inline(_))
                && alias_override.is_some()
            {
                return Err(InstantiationError::UnsupportedType(template));
            }
            if !could_contain_installed_type_variables(store, template, array_targets)? {
                return Ok(Some(template));
            }
            let mut arguments = Vec::with_capacity(projection.arguments().len());
            for argument in projection.arguments() {
                let mapped = if projection.mapper().is_none() {
                    cached_apply_mapping(store, *argument, mapping, array_targets)?
                } else {
                    cached_instantiated_type_worker(
                        store,
                        *argument,
                        mapping,
                        array_targets,
                        None,
                        active,
                    )?
                };
                let Some(mapped) = mapped else {
                    return Ok(None);
                };
                arguments.push(mapped);
            }
            let projection = match projection {
                SourcePropertyObjectProjection::DirectAlias(projection) => projection,
                SourcePropertyObjectProjection::Inline(projection) => {
                    return cached_inline_property_object_instance(store, &projection, &arguments);
                }
            };
            let (identity_symbol, identity_arguments) =
                if let Some((symbol, arguments)) = alias_override {
                    (symbol, arguments.to_vec())
                } else if projection.arguments == projection.identity_arguments {
                    (projection.identity_symbol, arguments.clone())
                } else {
                    let mut arguments = Vec::with_capacity(projection.identity_arguments.len());
                    for argument in &projection.identity_arguments {
                        let Some(mapped) = cached_instantiated_type_worker(
                            store,
                            *argument,
                            mapping,
                            array_targets,
                            None,
                            active,
                        )?
                        else {
                            return Ok(None);
                        };
                        arguments.push(mapped);
                    }
                    (projection.identity_symbol, arguments)
                };
            cached_property_object_alias_instance(
                store,
                &projection,
                &arguments,
                (identity_symbol, &identity_arguments),
            )
        }
        TypeData::TypeReference(_) | TypeData::Interface(_) => {
            if let Some(targets) = array_targets {
                store.canonical_array_reference_with_targets(targets, template)?;
            }
            let reference = validate_direct_generic_reference(store, template)?;
            let mut arguments = Vec::with_capacity(reference.type_arguments.len());
            for argument in &reference.type_arguments {
                let Some(mapped) = cached_instantiated_type_with_operand_worker(
                    store,
                    *argument,
                    mapping,
                    array_targets,
                    None,
                    active,
                    None,
                    operand,
                )?
                else {
                    return Ok(None);
                };
                arguments.push(mapped);
            }
            if arguments == reference.type_arguments {
                return Ok(Some(template));
            }
            let Some(cached) =
                store.relation_object_instantiation(reference.target, type_list_key(&arguments))
            else {
                return Ok(None);
            };
            let actual = validate_direct_generic_reference(store, cached)?;
            if actual.target != reference.target || actual.type_arguments != arguments {
                return Err(InstantiationError::InvalidType(cached));
            }
            if operand.is_some() {
                let targets = array_targets.ok_or(InstantiationError::InvalidType(template))?;
                store
                    .canonical_array_reference_with_targets(targets, cached)?
                    .ok_or(InstantiationError::InvalidType(cached))?;
            }
            Ok(Some(cached))
        }
        _ => Err(InstantiationError::UnsupportedType(template)),
    })();
    active.remove(&template);
    result
}

fn conditional_remap_error(source: TypeId, error: ConditionalTypeError) -> InstantiationError {
    match error {
        ConditionalTypeError::Instantiation(error) => error,
        ConditionalTypeError::Declared(error) => InstantiationError::Declared(error),
        ConditionalTypeError::InvalidMapper(mapper) => InstantiationError::InvalidMapper(mapper),
        ConditionalTypeError::Capacity => {
            InstantiationError::Union(LiteralTypeCacheError::Capacity)
        }
        _ => InstantiationError::InvalidType(source),
    }
}

fn conditional_source_error(source: TypeId, error: ConditionalTypeError) -> InstantiationError {
    match error {
        ConditionalTypeError::UnsupportedInference { .. }
        | ConditionalTypeError::TailRecursionLimit { .. } => {
            InstantiationError::UnsupportedType(source)
        }
        _ => conditional_remap_error(source, error),
    }
}

fn validate_conditional_alias_override(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
) -> Result<(), InstantiationError> {
    if let Some((symbol, arguments)) = alias_override {
        validate_borrowed_alias_input(store, projection.type_id(), symbol, arguments)?;
        if projection
            .alias()
            .map(|alias| (alias.symbol, alias.type_arguments.len()))
            != Some((symbol, arguments.len()))
        {
            return Err(InstantiationError::UnsupportedType(projection.type_id()));
        }
    }
    Ok(())
}

fn cached_instantiated_deferred_conditional(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    active: &mut HashSet<TypeId>,
    source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
) -> Result<Option<TypeId>, InstantiationError> {
    validate_conditional_alias_override(store, projection, alias_override)?;
    let mut arguments = Vec::with_capacity(projection.arguments().len());
    for (parameter, argument) in projection.parameters().iter().zip(projection.arguments()) {
        let mapped = if parameter == argument {
            cached_apply_mapping(store, *parameter, mapping, array_targets)?
        } else {
            cached_instantiated_type_with_source_worker(
                store,
                *argument,
                mapping,
                array_targets,
                None,
                active,
                source,
            )?
        };
        let Some(mapped) = mapped else {
            return Ok(None);
        };
        arguments.push(mapped);
    }
    let mut alias_arguments = Vec::new();
    if let Some(alias) = projection.alias() {
        for argument in alias.type_arguments {
            let Some(mapped) = cached_instantiated_type_with_source_worker(
                store,
                *argument,
                mapping,
                array_targets,
                None,
                active,
                source,
            )?
            else {
                return Ok(None);
            };
            alias_arguments.push(mapped);
        }
    }
    let alias = projection.alias().map(|alias| ConditionalAliasIdentity {
        symbol: alias.symbol,
        type_arguments: &alias_arguments,
    });
    if alias_override.is_some()
        && alias_override != alias.map(|alias| (alias.symbol, alias.type_arguments))
    {
        return Err(InstantiationError::UnsupportedType(projection.type_id()));
    }
    if let Some((globals, source)) = source {
        return cached_conditional_remap_with_source(
            store, projection, &arguments, alias, globals, source,
        )
        .map_err(|error| conditional_remap_error(projection.type_id(), error));
    }
    match cached_deferred_conditional_remap(store, projection, &arguments, alias, array_targets)
        .map_err(|error| conditional_remap_error(projection.type_id(), error))?
    {
        ConditionalRemapLookup::Cold => Ok(None),
        ConditionalRemapLookup::Hit(type_) => Ok(Some(type_)),
        ConditionalRemapLookup::NeedsSourceEvaluation => {
            Err(InstantiationError::UnsupportedType(projection.type_id()))
        }
    }
}

fn cached_instantiated_mapped_alias(
    store: &CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    active: &mut HashSet<TypeId>,
) -> Result<Option<TypeId>, InstantiationError> {
    if !could_contain_installed_type_variables(store, projection.type_, array_targets)? {
        return Ok(Some(projection.type_));
    }
    if let Some((symbol, arguments)) = alias_override {
        validate_borrowed_alias_input(store, projection.type_, symbol, arguments)?;
        if symbol != projection.alias {
            return Err(InstantiationError::UnsupportedType(projection.type_));
        }
    }
    let mut arguments = Vec::with_capacity(projection.arguments.len());
    for argument in &projection.arguments {
        let Some(mapped) = cached_instantiated_type_worker(
            store,
            *argument,
            mapping,
            array_targets,
            None,
            active,
        )?
        else {
            return Ok(None);
        };
        arguments.push(mapped);
    }
    let (identity_symbol, identity_arguments) = if let Some((symbol, arguments)) = alias_override {
        (symbol, arguments.to_vec())
    } else if projection.arguments == projection.identity_arguments {
        (projection.identity_symbol, arguments.clone())
    } else {
        let mut arguments = Vec::with_capacity(projection.identity_arguments.len());
        for argument in &projection.identity_arguments {
            let Some(mapped) = cached_instantiated_type_worker(
                store,
                *argument,
                mapping,
                array_targets,
                None,
                active,
            )?
            else {
                return Ok(None);
            };
            arguments.push(mapped);
        }
        (projection.identity_symbol, arguments)
    };
    cached_supported_mapped_alias_instance(
        store,
        projection,
        &arguments,
        (identity_symbol, &identity_arguments),
        array_targets,
    )
    .map_err(|error| mapped_indexed_access_error(projection.type_, error))
}

fn cached_instantiated_intersection_type(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    active: &mut HashSet<TypeId>,
) -> Result<Option<TypeId>, InstantiationError> {
    let projection = instantiable_intersection_projection(store, source, array_targets)?;
    if !could_contain_installed_type_variables(store, source, array_targets)? {
        return Ok(Some(source));
    }
    if let Some((symbol, arguments)) = alias_override {
        validate_borrowed_alias_input(store, source, symbol, arguments)?;
    }
    let mut constituents = Vec::with_capacity(projection.types.len());
    for constituent in &projection.types {
        let Some(instantiated) = cached_instantiated_type_worker(
            store,
            *constituent,
            mapping,
            array_targets,
            None,
            active,
        )?
        else {
            return Ok(None);
        };
        constituents.push(instantiated);
    }
    if constituents == projection.types
        && alias_override.map(|(symbol, _)| symbol) == projection.alias_symbol
    {
        return Ok(Some(source));
    }
    let mut arguments = Vec::new();
    let alias = if let Some(alias) = alias_override {
        Some(alias)
    } else {
        for argument in &projection.alias_arguments {
            let Some(instantiated) = cached_instantiated_type_worker(
                store,
                *argument,
                mapping,
                array_targets,
                None,
                active,
            )?
            else {
                return Ok(None);
            };
            arguments.push(instantiated);
        }
        projection
            .alias_symbol
            .map(|symbol| (symbol, arguments.as_slice()))
    };
    let reduction_arguments = if alias_override.is_some() {
        &constituents[..1]
    } else {
        arguments.as_slice()
    };
    if let Some(reduced) = reduce_default_library_non_nullable_intersection(
        store,
        source,
        &projection,
        &constituents,
        reduction_arguments,
        array_targets,
    )? {
        return Ok(Some(reduced));
    }
    cached_deferred_intersection_result(store, source, &constituents, alias, array_targets)
}

/// Mirrors the deferred constructor's flattening without publishing a result.
fn cached_deferred_intersection_result(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    constituents: &[TypeId],
    alias: Option<(SemanticSymbolId, &[TypeId])>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, InstantiationError> {
    let invalid = || InstantiationError::InvalidType(source);
    if let Some((symbol, arguments)) = alias {
        validate_borrowed_alias_input(store, source, symbol, arguments)?;
        let Some([declaration]) = store.symbol(symbol).and_then(|owner| owner.declarations())
        else {
            return Err(invalid());
        };
        if store.source_node_kind(*declaration) != Some(SyntaxKind::TypeAliasDeclaration)
            || store
                .type_alias_links(symbol)
                .and_then(|links| links.type_parameters.as_deref())
                .is_some_and(|parameters| parameters.len() != arguments.len())
        {
            return Err(invalid());
        }
    }
    if let Some(reduced) = store
        .reduce_numeric_literal_intersection(constituents)
        .map_err(|error| deferred_intersection_error(source, error))?
    {
        return Ok(Some(reduced));
    }
    let mut types = Vec::with_capacity(constituents.len());
    for constituent in constituents {
        store
            .append_deferred_intersection_constituent_with_array_targets(
                *constituent,
                &mut types,
                array_targets,
            )
            .map_err(|error| deferred_intersection_error(source, error))?;
    }
    if let Some(reduced) = store
        .reduce_numeric_literal_intersection(&types)
        .map_err(|error| deferred_intersection_error(source, error))?
    {
        return Ok(Some(reduced));
    }
    match types.as_slice() {
        [] => {
            return store
                .intrinsic_bootstrap()
                .map(|bootstrap| Some(bootstrap.unknown_type))
                .ok_or_else(invalid);
        }
        [single] => return Ok(Some(*single)),
        _ => {}
    }
    let key = IntersectionTypeCacheKey {
        types,
        alias_symbol: alias.map(|(symbol, _)| symbol),
        alias_arguments: alias.map_or_else(Vec::new, |(_, arguments)| arguments.to_vec()),
    };
    let Some(cached) = store.intersection_types.get(&key).copied() else {
        return if store
            .intersection_keys_by_type
            .values()
            .any(|reverse| reverse == &key)
        {
            Err(invalid())
        } else {
            Ok(None)
        };
    };
    if store.intersection_keys_by_type.get(&cached) != Some(&key) {
        return Err(invalid());
    }
    let record = store.type_payload(cached).ok_or_else(invalid)?;
    if record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        store
            .validate_intersection_type_with_array_targets(cached, array_targets)
            .map_err(|error| deferred_intersection_error(source, error))?;
    } else {
        store
            .validate_deferred_intersection_type_with_array_targets(cached, array_targets)
            .map_err(|error| deferred_intersection_error(source, error))?;
    }
    Ok(Some(cached))
}

fn instantiated_member_union_matches(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    actual: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, InstantiationError> {
    if matches!(
        store.type_payload(actual).map(TypeRecord::data),
        Some(TypeData::Union(_))
    ) {
        instantiable_union_source_types(store, actual, array_targets)?;
    }
    cached_instantiated_type_worker(
        store,
        template,
        InstantiationMapping::Stored(mapper),
        array_targets,
        None,
        &mut HashSet::new(),
    )
    .map(|expected| expected == Some(actual))
}

fn cached_property_object_alias_instance(
    store: &CanonicalTypeMapperStore,
    source: &PropertyObjectAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
) -> Result<Option<TypeId>, InstantiationError> {
    if arguments.len() != source.parameters.len() {
        return Err(InstantiationError::InvalidType(source.type_));
    }
    validate_property_object_alias_arguments(store, arguments)
        .map_err(|_| InstantiationError::UnsupportedType(source.type_))?;
    let identity_source = property_object_alias_identity_source_header(store, identity.0)
        .map_err(|_| InstantiationError::InvalidType(source.type_))?;
    if identity_source.parameters.len() != identity.1.len() {
        return Err(InstantiationError::UnsupportedType(source.type_));
    }
    validate_property_object_alias_arguments(store, identity.1)
        .map_err(|_| InstantiationError::UnsupportedType(source.type_))?;
    if arguments == source.arguments
        && identity.0 == source.identity_symbol
        && identity.1 == source.identity_arguments
    {
        return Ok(Some(source.type_));
    }
    let Some(alias_id) = store.symbol_store().assigned_global_symbol_id(identity.0) else {
        return Ok(None);
    };
    let key = type_alias_instantiation_cache_key(arguments, Some((alias_id, identity.1)));
    let Some(cached) = store.relation_object_instantiation(source.target, key) else {
        return Ok(None);
    };
    let actual = property_object_alias_projection(store, cached)
        .map_err(|_| InstantiationError::InvalidType(cached))?
        .ok_or(InstantiationError::InvalidType(cached))?;
    if actual.target != source.target
        || actual.alias_symbol != source.alias_symbol
        || actual.parameters != source.parameters
        || actual.arguments != arguments
        || actual.identity_symbol != identity.0
        || actual.identity_arguments != identity.1
    {
        return Err(InstantiationError::InvalidType(cached));
    }
    Ok(Some(cached))
}

fn cached_inline_property_object_instance(
    store: &CanonicalTypeMapperStore,
    source: &InlinePropertyObjectProjection,
    arguments: &[TypeId],
) -> Result<Option<TypeId>, InstantiationError> {
    if arguments.len() != source.parameters.len() {
        return Err(InstantiationError::InvalidType(source.type_));
    }
    validate_property_object_alias_arguments(store, arguments)
        .map_err(|_| InstantiationError::UnsupportedType(source.type_))?;
    if arguments == source.arguments {
        return Ok(Some(source.type_));
    }
    let key = type_alias_instantiation_cache_key(arguments, None);
    let Some(cached) = store.relation_object_instantiation(source.target, key) else {
        return Ok(None);
    };
    let actual = inline_property_object_projection(store, cached)
        .map_err(|_| InstantiationError::InvalidType(cached))?
        .ok_or(InstantiationError::InvalidType(cached))?;
    if actual.target != source.target
        || actual.declaration != source.declaration
        || actual.source_symbol != source.source_symbol
        || actual.parameter_owner != source.parameter_owner
        || actual.parameters != source.parameters
        || actual.arguments != arguments
    {
        return Err(InstantiationError::InvalidType(cached));
    }
    Ok(Some(cached))
}

/// Keeps the original anonymous target and maps its ordered outer parameters.
/// Property symbols and their value types are resolved by member demand.
#[allow(clippy::too_many_lines)] // Argument mapping, exact cache identity, and recovery publication are one operation.
fn instantiate_property_object_alias(
    store: &mut CanonicalTypeMapperStore,
    source: &PropertyObjectAliasProjection,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    let error_type = store
        .intrinsic_bootstrap()
        .ok_or(InstantiationError::InvalidType(source.type_))?
        .error_type;
    let (inherited_physical, inherited_identity) =
        if let Some(recovery) = store.property_object_alias_recovery(source.type_) {
            if recovery.result() != source.type_ || !recovery.matches_current_result(store) {
                return Err(InstantiationError::InvalidType(source.type_));
            }
            (
                (0..source.arguments.len())
                    .map(|index| recovery.physical_slot_recovered(index))
                    .collect::<Vec<_>>(),
                (0..source.identity_arguments.len())
                    .map(|index| recovery.identity_slot_recovered(index))
                    .collect::<Vec<_>>(),
            )
        } else {
            (
                vec![false; source.arguments.len()],
                vec![false; source.identity_arguments.len()],
            )
        };
    let mut arguments = Vec::with_capacity(source.arguments.len());
    let mut physical_recovery = Vec::with_capacity(source.arguments.len());
    for (index, argument) in source.arguments.iter().enumerate() {
        let mark = session.limit_event_mark();
        let mapped = if source.mapper.is_none() {
            apply_mapping(store, *argument, mapping, array_targets, session)?
        } else {
            instantiate_type_with_alias(store, *argument, mapping, array_targets, None, session)?
        };
        physical_recovery.push(recovered_property_alias_argument(
            session,
            mark,
            error_type,
            *argument,
            mapped,
            inherited_physical[index],
        )?);
        arguments.push(mapped);
    }
    let mut identity_recovery = Vec::new();
    let (identity_symbol, identity_arguments) = if let Some((symbol, arguments)) = alias_override {
        identity_recovery.resize(arguments.len(), false);
        (symbol, arguments.to_vec())
    } else {
        let mut arguments = Vec::with_capacity(source.identity_arguments.len());
        identity_recovery.reserve(source.identity_arguments.len());
        for (index, argument) in source.identity_arguments.iter().enumerate() {
            let mark = session.limit_event_mark();
            let mapped = instantiate_type_with_alias(
                store,
                *argument,
                mapping,
                array_targets,
                None,
                session,
            )?;
            identity_recovery.push(recovered_property_alias_argument(
                session,
                mark,
                error_type,
                *argument,
                mapped,
                inherited_identity[index],
            )?);
            arguments.push(mapped);
        }
        (source.identity_symbol, arguments)
    };
    if let Some(cached) = cached_property_object_alias_instance(
        store,
        source,
        &arguments,
        (identity_symbol, &identity_arguments),
    )? {
        return Ok(cached);
    }

    let has_recovery = physical_recovery
        .iter()
        .chain(&identity_recovery)
        .any(|marked| *marked);
    if has_recovery && !store.try_reserve_property_object_alias_recoveries() {
        return Err(LiteralTypeCacheError::Capacity.into());
    }

    let global_alias = store
        .global_symbol_id(identity_symbol)
        .ok_or(InstantiationError::InvalidType(source.target))?;
    let global_source_alias = store
        .global_symbol_id(source.alias_symbol)
        .ok_or(InstantiationError::InvalidType(source.target))?;
    let key =
        type_alias_instantiation_cache_key(&arguments, Some((global_alias, &identity_arguments)));
    let identity_key = type_alias_instantiation_cache_key(
        &source.parameters,
        Some((global_source_alias, &source.parameters)),
    );
    let Some(TypeData::Object(target)) = store.type_payload(source.target).map(TypeRecord::data)
    else {
        return Err(InstantiationError::InvalidType(source.target));
    };
    let mut new_cache = if matches!(target.instantiations, TypeCacheState::Unallocated) {
        let mut entries = HashMap::new();
        entries
            .try_reserve(2)
            .map_err(|_| LiteralTypeCacheError::Capacity)?;
        entries.insert(identity_key, source.target);
        Some(entries)
    } else {
        if !store.try_reserve_object_instantiations(source.target, 1) {
            return Err(LiteralTypeCacheError::Capacity.into());
        }
        None
    };
    if !store.try_reserve_types(1)
        || !store.try_reserve_type_aliases(1)
        || !store.try_reserve_mappers(1)
        || !store.try_reserve_type_node_links(1)
    {
        return Err(LiteralTypeCacheError::Capacity.into());
    }
    let mut links = store
        .type_node_links(source.declaration)
        .cloned()
        .ok_or(InstantiationError::InvalidType(source.target))?;
    let mapper = store
        .new_type_mapper(source.parameters.clone(), arguments.clone())
        .ok_or(InstantiationError::InvalidType(source.target))?;
    let propagating_flags = identity_arguments
        .iter()
        .fold(ObjectFlags::NONE, |flags, argument| {
            flags
                | store
                    .type_payload(*argument)
                    .expect("the alias argument proof checked every type")
                    .object_flags()
                    & ObjectFlags::PROPAGATING_FLAGS
        });
    let alias = store
        .alloc_type_alias(Some(identity_symbol))
        .ok_or(InstantiationError::InvalidType(source.target))?;
    if !store.set_type_alias_arguments(
        alias,
        (!identity_arguments.is_empty()).then(|| identity_arguments.clone()),
    ) {
        return Err(InstantiationError::InvalidAlias(alias));
    }
    let instantiated = store
        .alloc_plain_object_type(
            ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATED | propagating_flags,
            Some(source.source_symbol),
        )
        .ok_or(InstantiationError::InvalidType(source.target))?;
    if !store.set_type_alias(instantiated, Some(alias))
        || !store.set_object_target_and_mapper(instantiated, Some(source.target), Some(mapper))
    {
        return Err(InstantiationError::InvalidType(instantiated));
    }
    if let Some(entries) = new_cache.as_mut() {
        entries.insert(key, instantiated);
    }
    if let Some(entries) = new_cache {
        if !store.set_object_instantiations(source.target, TypeCacheState::Allocated(entries)) {
            return Err(InstantiationError::InvalidType(source.target));
        }
    } else if store.insert_object_instantiation(source.target, key, instantiated)
        != Some(instantiated)
    {
        return Err(InstantiationError::InvalidType(source.target));
    }
    if links.outer_type_parameters.is_none() {
        links.outer_type_parameters = Some(source.parameters.clone());
        if !store.set_type_node_links(source.declaration, links) {
            return Err(InstantiationError::InvalidType(source.target));
        }
    }
    if has_recovery
        && !store.publish_property_object_alias_recovery(PropertyObjectAliasRecovery {
            result: instantiated,
            target: source.target,
            declaration: source.declaration,
            source_symbol: source.source_symbol,
            alias_symbol: source.alias_symbol,
            parameters: source.parameters.clone(),
            mapper,
            arguments,
            identity: alias,
            identity_symbol,
            identity_arguments,
            error_type,
            physical_recovery,
            identity_recovery,
        })
    {
        return Err(InstantiationError::InvalidType(instantiated));
    }
    Ok(instantiated)
}

/// Maps an inline literal from its original lexical parameters without an alias.
#[allow(clippy::too_many_lines)] // Mapping, reservation, and exact recovery publication form one operation.
fn instantiate_inline_property_object(
    store: &mut CanonicalTypeMapperStore,
    source: &InlinePropertyObjectProjection,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    let error_type = store
        .intrinsic_bootstrap()
        .ok_or(InstantiationError::InvalidType(source.type_))?
        .error_type;
    let inherited_recovery =
        if let Some(recovery) = store.inline_property_object_recovery(source.type_) {
            if recovery.result() != source.type_
                || recovery.error_type() != error_type
                || !recovery.matches_current_result(store)
            {
                return Err(InstantiationError::InvalidType(source.type_));
            }
            (0..source.arguments.len())
                .map(|index| recovery.physical_slot_recovered(index))
                .collect::<Vec<_>>()
        } else {
            vec![false; source.arguments.len()]
        };
    let mut arguments = Vec::with_capacity(source.arguments.len());
    let mut physical_recovery = Vec::with_capacity(source.arguments.len());
    for (index, argument) in source.arguments.iter().enumerate() {
        let mark = session.limit_event_mark();
        let mapped = if source.mapper.is_none() {
            apply_mapping(store, *argument, mapping, array_targets, session)?
        } else {
            instantiate_type_with_alias(store, *argument, mapping, array_targets, None, session)?
        };
        physical_recovery.push(recovered_property_alias_argument(
            session,
            mark,
            error_type,
            *argument,
            mapped,
            inherited_recovery[index],
        )?);
        arguments.push(mapped);
    }
    if let Some(cached) = cached_inline_property_object_instance(store, source, &arguments)? {
        return Ok(cached);
    }
    let has_recovery = physical_recovery.iter().any(|marked| *marked);
    if has_recovery && !store.try_reserve_inline_property_object_recoveries() {
        return Err(LiteralTypeCacheError::Capacity.into());
    }
    let key = type_alias_instantiation_cache_key(&arguments, None);
    let identity_key = type_alias_instantiation_cache_key(&source.parameters, None);
    let Some(TypeData::Object(target)) = store.type_payload(source.target).map(TypeRecord::data)
    else {
        return Err(InstantiationError::InvalidType(source.target));
    };
    let mut new_cache = if matches!(target.instantiations, TypeCacheState::Unallocated) {
        let mut entries = HashMap::new();
        entries
            .try_reserve(2)
            .map_err(|_| LiteralTypeCacheError::Capacity)?;
        entries.insert(identity_key, source.target);
        Some(entries)
    } else {
        if !store.try_reserve_object_instantiations(source.target, 1) {
            return Err(LiteralTypeCacheError::Capacity.into());
        }
        None
    };
    if !store.try_reserve_types(1) || !store.try_reserve_mappers(1) {
        return Err(LiteralTypeCacheError::Capacity.into());
    }
    let mapper = store
        .new_type_mapper(source.parameters.clone(), arguments.clone())
        .ok_or(InstantiationError::InvalidType(source.target))?;
    let propagating_flags = arguments.iter().fold(ObjectFlags::NONE, |flags, argument| {
        flags
            | store
                .type_payload(*argument)
                .expect("the inline argument proof checked every type")
                .object_flags()
                & ObjectFlags::PROPAGATING_FLAGS
    });
    let instantiated = store
        .alloc_plain_object_type(
            ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATED | propagating_flags,
            Some(source.source_symbol),
        )
        .ok_or(InstantiationError::InvalidType(source.target))?;
    if !store.set_object_target_and_mapper(instantiated, Some(source.target), Some(mapper)) {
        return Err(InstantiationError::InvalidType(instantiated));
    }
    if let Some(entries) = new_cache.as_mut() {
        entries.insert(key, instantiated);
    }
    if let Some(entries) = new_cache {
        if !store.set_object_instantiations(source.target, TypeCacheState::Allocated(entries)) {
            return Err(InstantiationError::InvalidType(source.target));
        }
    } else if store.insert_object_instantiation(source.target, key, instantiated)
        != Some(instantiated)
    {
        return Err(InstantiationError::InvalidType(source.target));
    }
    if has_recovery
        && !store.publish_inline_property_object_recovery(InlinePropertyObjectRecovery {
            result: instantiated,
            target: source.target,
            declaration: source.declaration,
            source_symbol: source.source_symbol,
            parameter_owner: source.parameter_owner,
            parameters: source.parameters.clone(),
            mapper,
            arguments,
            error_type,
            physical_recovery,
        })
    {
        return Err(InstantiationError::InvalidType(instantiated));
    }
    Ok(instantiated)
}

fn recovered_property_alias_argument(
    session: &InstantiationSession,
    mark: InstantiationLimitEventMark,
    error_type: TypeId,
    source: TypeId,
    result: TypeId,
    inherited: bool,
) -> Result<bool, InstantiationError> {
    let recovered = session.limit_event_occurred_since(mark);
    if recovered && session.recovery_error_type() != Some(error_type) {
        return Err(InstantiationError::InvalidRecoveryType(
            session.recovery_error_type().unwrap_or(error_type),
        ));
    }
    Ok(result == error_type && (recovered || inherited && source == result))
}

enum InstantiationWork {
    TypeParameter,
    Identity,
    TemplateLiteral {
        texts: Vec<String>,
        types: Vec<TypeId>,
    },
    StringMapping {
        symbol: SemanticSymbolId,
        target: TypeId,
    },
    Union,
    Intersection(DeferredIntersectionTypeProjection),
    TypeReference,
    PropertyObjectAlias(PropertyObjectAliasProjection),
    InlinePropertyObject(InlinePropertyObjectProjection),
    SupportedMappedAlias(SupportedMappedAliasProjection),
    DeferredConditional(Box<ConditionalRemapProjection>),
    Index {
        target: TypeId,
    },
    IndexedAccess {
        object: TypeId,
        index: TypeId,
        flags: AccessFlags,
    },
    Unsupported,
}

#[allow(clippy::too_many_arguments)] // The source reader borrows the existing frame and caller session.
fn instantiate_type_worker(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias: Option<(SemanticSymbolId, &[TypeId])>,
    session: &mut InstantiationSession,
    receipt: Option<&mut OrdinaryIntersectionReceiptBuilder>,
    mut source: Option<&mut InstantiationSource<'_>>,
    operand: Option<&SourceAliasOperandGraph>,
) -> Result<TypeId, InstantiationError> {
    let work = {
        let record = store
            .type_payload(type_)
            .ok_or(InstantiationError::InvalidType(type_))?;
        match record.data() {
            TypeData::TypeParameter(_) => InstantiationWork::TypeParameter,
            TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => {
                InstantiationWork::Identity
            }
            TypeData::TemplateLiteral(template) => InstantiationWork::TemplateLiteral {
                texts: template.texts.clone(),
                types: template.types.clone(),
            },
            TypeData::StringMapping(mapping) => InstantiationWork::StringMapping {
                symbol: record
                    .symbol()
                    .ok_or(InstantiationError::UnsupportedType(type_))?,
                target: mapping.target,
            },
            TypeData::Union(_) => InstantiationWork::Union,
            TypeData::Intersection(_) => InstantiationWork::Intersection(
                instantiable_intersection_projection(store, type_, array_targets)?,
            ),
            TypeData::TypeReference(_) => InstantiationWork::TypeReference,
            TypeData::Index(_) => InstantiationWork::Index {
                target: validate_generic_keyof_index_type(store, type_)
                    .map_err(|error| instantiated_keyof_error(type_, error))?,
            },
            TypeData::Mapped(_) => {
                if let Some(projection) =
                    source_mapped_lookup_projection(store, type_, array_targets)
                        .map_err(|error| mapped_indexed_access_error(type_, error))?
                {
                    if let Some((symbol, arguments)) = alias {
                        validate_borrowed_alias_input(store, type_, symbol, arguments)?;
                        return Err(InstantiationError::UnsupportedType(type_));
                    }
                    let mut arguments = Vec::with_capacity(projection.arguments.len());
                    for argument in &projection.arguments {
                        let mark = session.limit_event_mark();
                        let mapped = instantiate_type_with_alias(
                            store,
                            *argument,
                            mapping,
                            array_targets,
                            None,
                            session,
                        )?;
                        if session.limit_event_occurred_since(mark)
                            && let Some(error) = session.recovery_error_type()
                        {
                            return Ok(error);
                        }
                        arguments.push(mapped);
                    }
                    return instantiate_source_mapped_lookup_instance(
                        store,
                        &projection,
                        &arguments,
                        array_targets,
                    )
                    .map_err(|error| mapped_indexed_access_error(type_, error));
                }
                InstantiationWork::SupportedMappedAlias(
                    supported_mapped_alias_projection(store, type_, array_targets)
                        .map_err(|error| mapped_indexed_access_error(type_, error))?
                        .ok_or(InstantiationError::UnsupportedType(type_))?,
                )
            }
            TypeData::Conditional(_) => {
                let projection = match source.as_ref() {
                    Some(source) => conditional_remap_projection_with_source(
                        store,
                        type_,
                        source.branches,
                        array_targets,
                    ),
                    None => {
                        conditional_remap_projection_with_array_targets(store, type_, array_targets)
                    }
                }
                .map_err(|error| conditional_remap_error(type_, error))?;
                InstantiationWork::DeferredConditional(Box::new(projection))
            }
            TypeData::IndexedAccess(indexed) => InstantiationWork::IndexedAccess {
                object: indexed.object_type,
                index: indexed.index_type,
                flags: indexed.access_flags,
            },
            TypeData::Interface(interface)
                if interface
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .is_some_and(|arguments| !arguments.is_empty()) =>
            {
                InstantiationWork::TypeReference
            }
            TypeData::Interface(_) => InstantiationWork::Identity,
            TypeData::Object(_) => {
                if mapping_invariant_object_type(store, type_, array_targets)? {
                    InstantiationWork::Identity
                } else {
                    match source_property_object_projection(store, type_)
                        .map_err(|_| InstantiationError::InvalidType(type_))?
                    {
                        Some(SourcePropertyObjectProjection::DirectAlias(projection)) => {
                            InstantiationWork::PropertyObjectAlias(projection)
                        }
                        Some(SourcePropertyObjectProjection::Inline(projection)) => {
                            if alias.is_some() {
                                return Err(InstantiationError::UnsupportedType(type_));
                            }
                            InstantiationWork::InlinePropertyObject(projection)
                        }
                        None if is_concrete_source_object_literal(store, type_, array_targets)? => {
                            InstantiationWork::Identity
                        }
                        None => InstantiationWork::Unsupported,
                    }
                }
            }
            _ => InstantiationWork::Unsupported,
        }
    };
    match work {
        InstantiationWork::Index { target } => {
            let mark = session.limit_event_mark();
            let target =
                instantiate_type_with_alias(store, target, mapping, array_targets, None, session)?;
            if session.limit_event_occurred_since(mark)
                && session.recovery_error_type() == Some(target)
            {
                return Ok(target);
            }
            let plan = plan_nongeneric_keyof_type_with_array_targets(store, target, array_targets)
                .map_err(|error| instantiated_keyof_error(type_, error))?;
            resolve_nongeneric_keyof_type_with_session(store, &plan, session)
                .map_err(|error| instantiated_keyof_error(type_, error))
        }
        InstantiationWork::IndexedAccess {
            object,
            index,
            flags,
        } => {
            let object = instantiate_type_with_alias_input_and_source(
                store,
                object,
                mapping,
                array_targets,
                None,
                session,
                None,
                source.as_deref_mut(),
            )?;
            let index = instantiate_type_with_alias_input_and_source(
                store,
                index,
                mapping,
                array_targets,
                None,
                session,
                None,
                source.as_deref_mut(),
            )?;
            resolve_instantiated_indexed_access(
                store,
                type_,
                object,
                index,
                flags,
                array_targets,
                session,
                source,
            )
        }
        InstantiationWork::TypeParameter => {
            apply_mapping_with_source(store, type_, mapping, array_targets, session, source)
        }
        InstantiationWork::Identity => Ok(type_),
        InstantiationWork::TemplateLiteral { texts, types } => instantiate_template_literal(
            store,
            type_,
            &texts,
            &types,
            mapping,
            array_targets,
            session,
        ),
        InstantiationWork::StringMapping { symbol, target } => instantiate_string_mapping(
            store,
            type_,
            symbol,
            target,
            mapping,
            array_targets,
            session,
        ),
        InstantiationWork::Union => instantiate_union(
            store,
            type_,
            mapping,
            array_targets,
            alias,
            session,
            operand,
        ),
        InstantiationWork::Intersection(projection) => instantiate_intersection(
            store,
            type_,
            &projection,
            mapping,
            array_targets,
            alias,
            session,
            receipt,
        ),
        InstantiationWork::TypeReference => {
            if operand.is_some() {
                instantiate_array_reference_with_operand(
                    store,
                    type_,
                    mapping,
                    array_targets.ok_or(InstantiationError::InvalidType(type_))?,
                    session,
                    operand,
                )
            } else {
                instantiate_reference(store, type_, mapping, array_targets, session)
            }
        }
        InstantiationWork::PropertyObjectAlias(projection) => instantiate_property_object_alias(
            store,
            &projection,
            mapping,
            array_targets,
            alias,
            session,
        ),
        InstantiationWork::InlinePropertyObject(projection) => {
            instantiate_inline_property_object(store, &projection, mapping, array_targets, session)
        }
        InstantiationWork::SupportedMappedAlias(projection) => instantiate_supported_mapped_alias(
            store,
            &projection,
            mapping,
            array_targets,
            alias,
            session,
        ),
        InstantiationWork::DeferredConditional(projection) => instantiate_deferred_conditional(
            store,
            &projection,
            mapping,
            array_targets,
            alias,
            session,
            source,
        ),
        InstantiationWork::Unsupported => Err(InstantiationError::UnsupportedType(type_)),
    }
}

/// Performs an explicit one-key demand without an empty-mapper identity shortcut.
pub(super) fn resolve_indexed_access_with_source(
    store: &mut CanonicalTypeMapperStore,
    lookup: TypeId,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
) -> Result<TypeId, InstantiationError> {
    let Some(TypeData::IndexedAccess(indexed)) = store.type_payload(lookup).map(TypeRecord::data)
    else {
        return Err(InstantiationError::InvalidType(lookup));
    };
    let (object, index, flags) = (
        indexed.object_type,
        indexed.index_type,
        indexed.access_flags,
    );
    if cached_deferred_indexed_access_type(store, object, index, flags)
        .map_err(InstantiationError::InvalidType)?
        != Some(lookup)
    {
        return Err(InstantiationError::InvalidType(lookup));
    }
    resolve_instantiated_indexed_access(
        store,
        lookup,
        object,
        index,
        flags,
        Some(CanonicalArrayTargets::from_global_types(globals)),
        session,
        Some(&mut InstantiationSource {
            globals,
            branches: source,
        }),
    )
}

#[allow(clippy::too_many_arguments)] // Shares the indexed-access operation with ordinary substitution.
fn resolve_instantiated_indexed_access(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    object: TypeId,
    index: TypeId,
    flags: AccessFlags,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
    source: Option<&mut InstantiationSource<'_>>,
) -> Result<TypeId, InstantiationError> {
    match indexed_access_resolution(store, object, index, flags, array_targets)? {
        IndexedAccessResolution::Type(type_) => Ok(type_),
        IndexedAccessResolution::TypeWithSentinel(type_, sentinel) => store
            .literal_union_type_with_alias_and_array_targets_and_session(
                &[type_, sentinel],
                None,
                array_targets,
                session,
            )
            .map_err(Into::into),
        IndexedAccessResolution::Deferred => {
            get_instantiated_indexed_access_type(store, object, index, flags)
                .ok_or(InstantiationError::InvalidType(type_))
        }
        IndexedAccessResolution::Property(name) => {
            if matches!(
                store.type_payload(object).map(TypeRecord::data),
                Some(TypeData::Mapped(_))
            ) {
                if let Some(source) = source {
                    return store
                        .resolve_mapped_type_property_with_source(
                            object,
                            name.as_ref(),
                            MappedTypeModifiers::NONE,
                            source.globals,
                            session,
                            source.branches,
                        )
                        .map_err(|error| mapped_indexed_access_error(object, error))?
                        .map(super::mapped_types::ResolvedMappedProperty::type_id)
                        .ok_or(InstantiationError::UnsupportedType(type_));
                }
                store
                    .validate_mapped_type_relation_endpoint(object)
                    .map_err(|error| mapped_indexed_access_error(object, error))?;
                let members = store
                    .resolve_mapped_type_members_with_session(
                        object,
                        MappedTypeModifiers::NONE,
                        session,
                    )
                    .map_err(|error| mapped_indexed_access_error(object, error))?;
                let symbol = store
                    .symbol_table(members.members())
                    .and_then(|members| members.get(name.as_ref()))
                    .ok_or(InstantiationError::UnsupportedType(type_))?;
                if !members.properties().contains(&symbol) {
                    return Err(InstantiationError::InvalidType(object));
                }
                return store
                    .resolve_mapped_symbol_type_with_session(symbol, session)
                    .map_err(|error| mapped_indexed_access_error(object, error));
            }
            let property = super::object_members::resolve_object_property_by_key(
                store,
                source.as_ref().map(|source| source.globals),
                object,
                name.as_ref(),
                session,
            )
            .map_err(|_| InstantiationError::UnsupportedType(type_))?
            .ok_or(InstantiationError::UnsupportedType(type_))?;
            match indexed_access_property_optional_sentinel(store, property.symbol, property.type_)?
            {
                Some(sentinel) => store
                    .literal_union_type_with_alias_and_array_targets_and_session(
                        &[property.type_, sentinel],
                        None,
                        array_targets,
                        session,
                    )
                    .map_err(Into::into),
                None => Ok(property.type_),
            }
        }
    }
}

/// Reads the checked source property with the caller that owns the type-node query.
pub(super) fn resolve_source_alias_indexed_read_with_session(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceAliasIndexedBoundPlan,
    graph: &SourceAliasOperandGraph,
    object: TypeId,
    key: TypeId,
    globals: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    let targets = globals.map(CanonicalArrayTargets::from_global_types);
    let (selection, name) =
        checked_source_alias_indexed_property(store, plan, graph, object, key, targets)?;
    let property = super::object_members::resolve_object_property_by_key_with_alias_operand(
        store,
        globals,
        object,
        name.as_ref(),
        session,
        Some((graph, plan.object())),
    )
    .map_err(|_| InstantiationError::InvalidType(object))?
    .ok_or(InstantiationError::InvalidType(object))?;
    if property.symbol != selection.property()
        || property.type_ != selection.value_type()
        || property.optional != selection.optional()
    {
        return Err(InstantiationError::InvalidType(object));
    }
    match indexed_access_property_optional_sentinel_with_mode(
        store,
        property.symbol,
        property.type_,
        Some(selection.read_mode()),
    )? {
        Some(sentinel) => store
            .literal_union_type_with_alias_and_array_targets_and_session(
                &[property.type_, sentinel],
                None,
                targets,
                session,
            )
            .map_err(Into::into),
        None => Ok(property.type_),
    }
}

/// Selects the same member and optional read union without warming either cache.
pub(super) fn cached_source_alias_indexed_read(
    store: &CanonicalTypeMapperStore,
    plan: &SourceAliasIndexedBoundPlan,
    graph: &SourceAliasOperandGraph,
    object: TypeId,
    key: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, InstantiationError> {
    let (selection, _) =
        checked_source_alias_indexed_property(store, plan, graph, object, key, array_targets)?;
    match indexed_access_property_optional_sentinel_with_mode(
        store,
        selection.property(),
        selection.value_type(),
        Some(selection.read_mode()),
    )? {
        Some(sentinel) => store
            .cached_literal_union_type_with_alias(
                &[selection.value_type(), sentinel],
                None,
                array_targets,
            )
            .map_err(Into::into),
        None => Ok(Some(selection.value_type())),
    }
}

fn checked_source_alias_indexed_property(
    store: &CanonicalTypeMapperStore,
    plan: &SourceAliasIndexedBoundPlan,
    graph: &SourceAliasOperandGraph,
    object: TypeId,
    key: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(SourceAliasIndexedSelection, EscapedName), InstantiationError> {
    let invalid = || InstantiationError::InvalidType(object);
    let selection = plan
        .checked_selection(store, graph, object, key, array_targets)
        .map_err(|_| invalid())?;
    let IndexedAccessResolution::Property(name) =
        indexed_access_resolution(store, object, key, AccessFlags::NONE, array_targets)?
    else {
        return Err(invalid());
    };
    let property = super::object_members::property_from_source_alias_members(
        store,
        graph,
        plan.object(),
        object,
        name.as_ref(),
        array_targets,
    )
    .map_err(|_| invalid())?
    .ok_or_else(invalid)?;
    if property.symbol != selection.property()
        || property.type_ != selection.value_type()
        || property.optional != selection.optional()
    {
        return Err(invalid());
    }
    Ok((selection, name))
}

fn instantiate_deferred_conditional(
    store: &mut CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    session: &mut InstantiationSession,
    mut source: Option<&mut InstantiationSource<'_>>,
) -> Result<TypeId, InstantiationError> {
    validate_conditional_alias_override(store, projection, alias_override)?;
    let mark = session.limit_event_mark();
    let mut arguments = Vec::with_capacity(projection.arguments().len());
    for (parameter, argument) in projection.parameters().iter().zip(projection.arguments()) {
        // Go's composite mapper traverses a changed first result through the
        // second mapper. An unchanged parameter needs only its direct mapping.
        let mapped = if parameter == argument {
            apply_mapping_with_source(
                store,
                *parameter,
                mapping,
                array_targets,
                session,
                source.as_deref_mut(),
            )?
        } else {
            instantiate_type_with_alias_input_and_source(
                store,
                *argument,
                mapping,
                array_targets,
                None,
                session,
                None,
                source.as_deref_mut(),
            )?
        };
        if session.limit_event_occurred_since(mark)
            && let Some(error) = session.recovery_error_type()
        {
            return Ok(error);
        }
        arguments.push(mapped);
    }
    let mut alias_arguments = Vec::new();
    if let Some(alias) = projection.alias() {
        for argument in alias.type_arguments {
            let mapped = instantiate_type_with_alias_input_and_source(
                store,
                *argument,
                mapping,
                array_targets,
                None,
                session,
                None,
                source.as_deref_mut(),
            )?;
            if session.limit_event_occurred_since(mark)
                && let Some(error) = session.recovery_error_type()
            {
                return Ok(error);
            }
            alias_arguments.push(mapped);
        }
    }
    let alias = projection.alias().map(|alias| ConditionalAliasIdentity {
        symbol: alias.symbol,
        type_arguments: &alias_arguments,
    });
    if alias_override.is_some()
        && alias_override != alias.map(|alias| (alias.symbol, alias.type_arguments))
    {
        return Err(InstantiationError::UnsupportedType(projection.type_id()));
    }
    if let Some(source) = source {
        return remap_conditional_with_source(
            store,
            projection,
            &arguments,
            alias,
            source.globals,
            session,
            source.branches,
        )
        .map_err(|error| conditional_source_error(projection.type_id(), error));
    }
    match remap_deferred_conditional_with_session(
        store,
        projection,
        &arguments,
        alias,
        array_targets,
        session,
    )
    .map_err(|error| conditional_remap_error(projection.type_id(), error))?
    {
        ConditionalRemapResult::Deferred(type_) | ConditionalRemapResult::Recovered(type_) => {
            Ok(type_)
        }
        ConditionalRemapResult::NeedsSourceEvaluation => {
            Err(InstantiationError::UnsupportedType(projection.type_id()))
        }
    }
}

fn instantiate_supported_mapped_alias(
    store: &mut CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    if let Some((symbol, arguments)) = alias_override {
        validate_borrowed_alias_input(store, projection.type_, symbol, arguments)?;
        if symbol != projection.alias {
            return Err(InstantiationError::UnsupportedType(projection.type_));
        }
    }
    let mut arguments = Vec::with_capacity(projection.arguments.len());
    for argument in &projection.arguments {
        let mark = session.limit_event_mark();
        let mapped =
            instantiate_type_with_alias(store, *argument, mapping, array_targets, None, session)?;
        // A limit result belongs to this request. It is not an ordinary alias
        // instance and must not enter the producer's persistent cache.
        if session.limit_event_occurred_since(mark)
            && let Some(error) = session.recovery_error_type()
        {
            return Ok(error);
        }
        arguments.push(mapped);
    }
    let (identity_symbol, identity_arguments) = if let Some((symbol, arguments)) = alias_override {
        (symbol, arguments.to_vec())
    } else if projection.arguments == projection.identity_arguments {
        (projection.identity_symbol, arguments.clone())
    } else {
        let mut arguments = Vec::with_capacity(projection.identity_arguments.len());
        for argument in &projection.identity_arguments {
            let mark = session.limit_event_mark();
            let mapped = instantiate_type_with_alias(
                store,
                *argument,
                mapping,
                array_targets,
                None,
                session,
            )?;
            if session.limit_event_occurred_since(mark)
                && let Some(error) = session.recovery_error_type()
            {
                return Ok(error);
            }
            arguments.push(mapped);
        }
        (projection.identity_symbol, arguments)
    };
    instantiate_supported_mapped_alias_instance_with_session(
        store,
        projection,
        &arguments,
        (identity_symbol, &identity_arguments),
        array_targets,
        session,
    )
    .map_err(|error| mapped_indexed_access_error(projection.type_, error))
}

enum IndexedAccessResolution {
    Type(TypeId),
    TypeWithSentinel(TypeId, TypeId),
    Deferred,
    Property(EscapedName),
}

fn indexed_access_resolution(
    store: &CanonicalTypeMapperStore,
    object: TypeId,
    index: TypeId,
    access_flags: AccessFlags,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<IndexedAccessResolution, InstantiationError> {
    let object_record = store
        .type_payload(object)
        .ok_or(InstantiationError::InvalidType(object))?;
    let index_record = store
        .type_payload(index)
        .ok_or(InstantiationError::InvalidType(index))?;
    if object_record.flags().contains(TypeFlags::ANY) {
        return Ok(IndexedAccessResolution::Type(object));
    }
    if index_record.flags().contains(TypeFlags::NEVER) {
        return Ok(IndexedAccessResolution::Type(index));
    }
    if object_record
        .flags()
        .intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE)
        || index_record.flags().intersects(TypeFlags::INSTANTIABLE)
    {
        if object_record.flags().contains(TypeFlags::UNKNOWN) {
            return Ok(IndexedAccessResolution::Type(object));
        }
        return Ok(IndexedAccessResolution::Deferred);
    }
    if let Some(targets) = array_targets
        && index_record.flags().intersects(TypeFlags::NUMBER_LIKE)
        && let Some(array) = store.canonical_array_reference_with_targets(targets, object)?
    {
        return Ok(if access_flags.contains(AccessFlags::INCLUDE_UNDEFINED) {
            IndexedAccessResolution::TypeWithSentinel(
                array.element_type,
                store
                    .intrinsic_bootstrap()
                    .ok_or(InstantiationError::InvalidType(array.element_type))?
                    .missing_type,
            )
        } else {
            IndexedAccessResolution::Type(array.element_type)
        });
    }
    let name = escaped_property_name_from_type(store, index);
    let has_resolved_indexes = object_record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
        && object_record
            .data()
            .structured()
            .and_then(|structured| structured.index_infos.as_ref())
            .is_some_and(|indexes| !indexes.is_empty());
    if !has_resolved_indexes {
        return name
            .map(IndexedAccessResolution::Property)
            .ok_or(InstantiationError::UnsupportedType(index));
    }
    let structured = resolved_indexed_access_members(store, object, array_targets)?
        .ok_or(InstantiationError::UnsupportedType(object))?;
    if let Some(name) = name.as_ref()
        && let Some(property) = structured
            .members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(name.as_ref()))
    {
        if !structured
            .properties
            .as_deref()
            .unwrap_or_default()
            .contains(&property)
        {
            return Err(InstantiationError::InvalidType(object));
        }
        return match store
            .value_symbol_links(property)
            .and_then(|links| links.resolved_type)
        {
            Some(value) => {
                store
                    .type_payload(value)
                    .ok_or(InstantiationError::InvalidType(value))?;
                Ok(
                    match indexed_access_property_optional_sentinel(store, property, value)? {
                        Some(sentinel) => {
                            IndexedAccessResolution::TypeWithSentinel(value, sentinel)
                        }
                        None => IndexedAccessResolution::Type(value),
                    },
                )
            }
            None => Ok(IndexedAccessResolution::Property(name.clone())),
        };
    }
    if !index_record
        .flags()
        .intersects(TypeFlags::STRING_LIKE | TypeFlags::NUMBER_LIKE | TypeFlags::ES_SYMBOL_LIKE)
    {
        return Err(InstantiationError::UnsupportedType(index));
    }
    let numeric = index_record.flags().intersects(TypeFlags::NUMBER_LIKE)
        || index_record.flags().intersects(TypeFlags::STRING_LITERAL)
            && name
                .as_ref()
                .and_then(|name| name.as_ref().as_utf8())
                .is_some_and(|name| ts_jsnum::from_string(name).to_string() == name);
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(InstantiationError::InvalidType(object))?;
    let mut string_value = None;
    let mut number_value = None;
    for index in structured.index_infos.as_deref().unwrap_or_default() {
        let info = store
            .index_info(*index)
            .ok_or(InstantiationError::InvalidType(object))?;
        let value = info.value_type();
        store
            .type_payload(value)
            .ok_or(InstantiationError::InvalidType(value))?;
        let slot = if info.key_type() == bootstrap.string_type {
            &mut string_value
        } else if info.key_type() == bootstrap.number_type {
            &mut number_value
        } else {
            // Pattern and symbol indexes need their own applicability proof.
            return Err(InstantiationError::UnsupportedType(object));
        };
        if slot.replace(value).is_some() {
            return Err(InstantiationError::InvalidType(object));
        }
    }
    // Go also falls back to a string index for symbol-like keys. Instantiation
    // passes no access node, so this fallback does not report an index error.
    let value = numeric
        .then_some(number_value)
        .flatten()
        .or(string_value)
        .ok_or(InstantiationError::UnsupportedType(index))?;
    Ok(if access_flags.contains(AccessFlags::INCLUDE_UNDEFINED) {
        IndexedAccessResolution::TypeWithSentinel(value, bootstrap.missing_type)
    } else {
        IndexedAccessResolution::Type(value)
    })
}

fn resolved_indexed_access_members(
    store: &CanonicalTypeMapperStore,
    object: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<&StructuredTypeData>, InstantiationError> {
    let record = store
        .type_payload(object)
        .ok_or(InstantiationError::InvalidType(object))?;
    if matches!(record.data(), TypeData::Mapped(_)) {
        return match store
            .validate_mapped_type_relation_endpoint(object)
            .map_err(|error| mapped_indexed_access_error(object, error))?
        {
            None => Ok(None),
            Some(_) => record
                .data()
                .structured()
                .map(Some)
                .ok_or(InstantiationError::InvalidType(object)),
        };
    }
    if !record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        return Ok(None);
    }
    let declared = matches!(
        validate_resolved_declared_property_object(store, object),
        DeclaredPropertyObjectValidation::Valid(_)
    );
    let indexed = matches!(record.data(), TypeData::Object(_) | TypeData::Interface(_))
        && plan_nongeneric_keyof_type(store, object).is_ok();
    if !declared && !indexed {
        super::instantiated_members::validate_generic_interface_members(
            store,
            object,
            array_targets,
        )
        .map_err(|_| InstantiationError::InvalidType(object))?
        .ok_or(InstantiationError::UnsupportedType(object))?;
    }
    record
        .data()
        .structured()
        .map(Some)
        .ok_or(InstantiationError::InvalidType(object))
}

/// Declared property caches can retain the annotation and a separate OPTIONAL
/// flag. Read them like getTypeOfSymbol without changing the declaration cache.
fn indexed_access_property_optional_sentinel(
    store: &CanonicalTypeMapperStore,
    property: SemanticSymbolId,
    value: TypeId,
) -> Result<Option<TypeId>, InstantiationError> {
    indexed_access_property_optional_sentinel_with_mode(store, property, value, None)
}

fn indexed_access_property_optional_sentinel_with_mode(
    store: &CanonicalTypeMapperStore,
    property: SemanticSymbolId,
    value: TypeId,
    source_mode: Option<SourceAliasIndexedReadMode>,
) -> Result<Option<TypeId>, InstantiationError> {
    let symbol = store
        .symbol(property)
        .ok_or(InstantiationError::InvalidType(value))?;
    if !symbol
        .flags()
        .contains(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
        || symbol
            .check_flags()
            .intersects(CheckFlags::MAPPED | CheckFlags::INSTANTIATED)
        || !matches!(
            symbol
                .value_declaration()
                .and_then(|declaration| store.source_node_kind(declaration)),
            Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
        )
    {
        return Ok(None);
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(InstantiationError::InvalidType(value))?;
    if !bootstrap.options.strict_null_checks {
        return Ok(None);
    }
    let record = store
        .type_payload(value)
        .ok_or(InstantiationError::InvalidType(value))?;
    let sentinel = match source_mode {
        Some(SourceAliasIndexedReadMode::SourceTypeNode) => bootstrap.undefined_type,
        None => bootstrap.undefined_or_missing_type,
    };
    // Match getOptionalType's identity return, including an existing alias.
    // A nil access node does not replace an exact-optional missing sentinel.
    if value == sentinel
        || matches!(
            record.data(),
            TypeData::Union(union) if union.union.types.first() == Some(&sentinel)
        )
    {
        return Ok(None);
    }
    Ok(Some(sentinel))
}

fn instantiated_keyof_error(source: TypeId, error: NongenericKeyofError) -> InstantiationError {
    match error {
        NongenericKeyofError::InvalidType(type_)
        | NongenericKeyofError::MalformedObject(type_)
        | NongenericKeyofError::InvalidCachedResult(type_)
        | NongenericKeyofError::CachePublication(type_) => InstantiationError::InvalidType(type_),
        NongenericKeyofError::UnsupportedObject(_)
        | NongenericKeyofError::UnsupportedPropertyName { .. }
        | NongenericKeyofError::PropertiesCacheRequired { .. } => {
            InstantiationError::UnsupportedType(source)
        }
        NongenericKeyofError::LiteralCache(error) => InstantiationError::Union(error),
    }
}

fn mapped_indexed_access_error(object: TypeId, error: MappedTypeError) -> InstantiationError {
    match error {
        MappedTypeError::Declared(error) => InstantiationError::Declared(error),
        MappedTypeError::InstantiationDepthLimit { depth, limit } => {
            InstantiationError::DepthLimit { depth, limit }
        }
        MappedTypeError::InstantiationCountLimit { count, limit } => {
            InstantiationError::CountLimit { count, limit }
        }
        MappedTypeError::Capacity => InstantiationError::Union(LiteralTypeCacheError::Capacity),
        MappedTypeError::UnsupportedSource(_)
        | MappedTypeError::UnsupportedConstraint(_)
        | MappedTypeError::UnsupportedNameType(_)
        | MappedTypeError::UnsupportedTemplate(_)
        | MappedTypeError::RecursiveMembers(_)
        | MappedTypeError::CircularProperty(_)
        | MappedTypeError::CrossProductTooLarge { .. } => {
            InstantiationError::UnsupportedType(object)
        }
        _ => InstantiationError::InvalidType(object),
    }
}

fn instantiate_template_literal(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    texts: &[String],
    types: &[TypeId],
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    if types.is_empty() || texts.len() != types.len() + 1 {
        return Err(TemplateTypeError::InvalidTemplate(source).into());
    }
    let mut placeholders = Vec::with_capacity(types.len());
    let mut changed = false;
    for type_ in types {
        let instantiated =
            instantiate_type_with_alias(store, *type_, mapping, array_targets, None, session)?;
        changed |= instantiated != *type_;
        placeholders.push(instantiated);
    }
    if !changed {
        return Ok(source);
    }
    store
        .get_template_literal_type(texts, &placeholders)
        .map_err(Into::into)
}

fn instantiate_string_mapping(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    symbol: SemanticSymbolId,
    target: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    let target = instantiate_type_with_alias(store, target, mapping, array_targets, None, session)?;
    let Some(TypeData::StringMapping(original)) = store.type_payload(source).map(TypeRecord::data)
    else {
        return Err(InstantiationError::UnsupportedType(source));
    };
    if target == original.target {
        return Ok(source);
    }
    store
        .get_string_mapping_type(symbol, target)
        .map_err(Into::into)
}

fn instantiate_reference(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    if let Some(array_targets) = array_targets
        && store
            .canonical_array_reference_with_targets(array_targets, source)?
            .is_some()
    {
        return instantiate_array_reference(store, source, mapping, array_targets, session);
    }

    let reference = validate_direct_generic_reference(store, source)?;
    let mut mapped_arguments = Vec::with_capacity(reference.type_arguments.len());
    let mut changed = false;
    for argument in &reference.type_arguments {
        let mapped =
            instantiate_type_with_alias(store, *argument, mapping, array_targets, None, session)?;
        changed |= mapped != *argument;
        mapped_arguments.push(mapped);
    }
    if !changed {
        return Ok(source);
    }
    create_direct_generic_reference(
        store,
        reference.target,
        &mapped_arguments,
        ObjectFlags::NONE,
    )
    .map_err(Into::into)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // One caller frame maps slots and retains their real limit events.
fn instantiate_intersection(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    projection: &DeferredIntersectionTypeProjection,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    session: &mut InstantiationSession,
    mut receipt: Option<&mut OrdinaryIntersectionReceiptBuilder>,
) -> Result<TypeId, InstantiationError> {
    if let Some(builder) = receipt.as_deref() {
        if builder.parameters.is_empty()
            || builder
                .parameters
                .iter()
                .any(|parameter| cached_ordinary_type_parameter_owner(store, *parameter).is_none())
            || builder
                .parameters
                .iter()
                .copied()
                .collect::<HashSet<_>>()
                .len()
                != builder.parameters.len()
        {
            return Err(InstantiationError::InvalidType(source));
        }
        if let Some(inherited) = &builder.inherited {
            if inherited.result != source {
                return Err(InstantiationError::InvalidType(source));
            }
            inherited.validate_current_chain(store, array_targets)?;
        }
    }
    let mut constituents = Vec::with_capacity(projection.types.len());
    let mut constituent_receipts = Vec::new();
    let mut alias_receipts = Vec::new();
    if receipt.is_some() {
        constituent_receipts
            .try_reserve(projection.types.len())
            .map_err(|_| LiteralTypeCacheError::Capacity)?;
        alias_receipts
            .try_reserve(projection.alias_arguments.len())
            .map_err(|_| LiteralTypeCacheError::Capacity)?;
    }
    let mut changed = false;
    for constituent in &projection.types {
        let source_object = if receipt.is_some() {
            source_property_object_projection(store, *constituent)
                .map_err(|_| InstantiationError::InvalidType(*constituent))?
        } else {
            None
        };
        let before = session.limit_event_mark();
        let instantiated = instantiate_type_with_alias(
            store,
            *constituent,
            mapping,
            array_targets,
            None,
            session,
        )?;
        if let Some(builder) = receipt.as_deref() {
            constituent_receipts.push(capture_intersection_constituent_receipt(
                store,
                *constituent,
                source_object,
                instantiated,
                IntersectionSlotLimitEvents {
                    before,
                    after: session.limit_event_mark(),
                },
                builder,
                array_targets,
            )?);
        }
        changed |= instantiated != *constituent;
        constituents.push(instantiated);
    }

    if !changed && alias_override.map(|(symbol, _)| symbol) == projection.alias_symbol {
        return Ok(source);
    }

    let mut alias_arguments = Vec::new();
    let alias = if let Some(alias) = alias_override {
        Some(alias)
    } else {
        for (index, argument) in projection.alias_arguments.iter().enumerate() {
            let before = session.limit_event_mark();
            let mapped = instantiate_type_with_alias(
                store,
                *argument,
                mapping,
                array_targets,
                None,
                session,
            )?;
            if let Some(builder) = receipt.as_deref() {
                let error_type = store
                    .intrinsic_bootstrap()
                    .ok_or(InstantiationError::InvalidType(source))?
                    .error_type;
                let events = IntersectionSlotLimitEvents {
                    before,
                    after: session.limit_event_mark(),
                };
                if events.occurred()
                    && (mapped != error_type || session.recovery_error_type() != Some(error_type))
                {
                    return Err(InstantiationError::UnsupportedType(source));
                }
                let inherited = builder.inherited.as_ref().is_some_and(|prior| {
                    prior.alias_arguments.get(index).is_some_and(|slot| {
                        slot.result == error_type && (slot.events.occurred() || slot.inherited)
                    }) && *argument == error_type
                        && mapped == error_type
                });
                alias_receipts.push(IntersectionAliasArgumentReceipt {
                    source: *argument,
                    result: mapped,
                    events,
                    inherited,
                });
            }
            alias_arguments.push(mapped);
        }
        projection
            .alias_symbol
            .map(|symbol| (symbol, alias_arguments.as_slice()))
    };
    let reduction_arguments = if alias_override.is_some() {
        &constituents[..1]
    } else {
        alias_arguments.as_slice()
    };
    if let Some(reduced) = reduce_default_library_non_nullable_intersection(
        store,
        source,
        projection,
        &constituents,
        reduction_arguments,
        array_targets,
    )? {
        return Ok(reduced);
    }

    let result = store
        .canonical_deferred_intersection_type_with_array_targets(
            &constituents,
            alias,
            array_targets,
        )
        .map_err(|error| deferred_intersection_error(source, error))?;
    if let Some(builder) = receipt.as_mut() {
        let recovered = constituent_receipts.iter().any(|slot| {
            slot.events.occurred()
                || slot
                    .object
                    .as_ref()
                    .is_some_and(|object| object.recovery != IntersectionObjectRecovery::None)
        }) || alias_receipts
            .iter()
            .any(|slot| slot.events.occurred() || slot.inherited);
        if recovered {
            let error_type = store
                .intrinsic_bootstrap()
                .ok_or(InstantiationError::InvalidType(source))?
                .error_type;
            let result_key = store
                .intersection_keys_by_type
                .get(&result)
                .cloned()
                .ok_or(InstantiationError::UnsupportedType(source))?;
            let retained = OrdinaryIntersectionRecoveryReceipt {
                source,
                source_key: IntersectionTypeCacheKey {
                    types: projection.types.clone(),
                    alias_symbol: projection.alias_symbol,
                    alias_arguments: projection.alias_arguments.clone(),
                },
                parameters: builder.parameters.clone(),
                arguments: builder.arguments.clone(),
                alias_override: alias_override
                    .map(|(symbol, arguments)| (symbol, arguments.to_vec())),
                array_targets,
                error_type,
                result,
                result_key,
                constituents: constituent_receipts,
                alias_arguments: alias_receipts,
                inherited: builder.inherited.clone(),
            };
            retained.validate_current_chain(store, array_targets)?;
            builder.receipt = Some(retained);
        }
    }
    Ok(result)
}

fn authenticated_default_library_non_nullable_empty_object(
    store: &CanonicalTypeMapperStore,
    projection: &DeferredIntersectionTypeProjection,
) -> Option<TypeId> {
    let bootstrap = store.intrinsic_bootstrap()?;
    let alias = projection.alias_symbol?;
    let [parameter, empty_object] = projection.types.as_slice() else {
        return None;
    };
    let [argument] = projection.alias_arguments.as_slice() else {
        return None;
    };
    if argument != parameter
        || *empty_object != bootstrap.empty_type_literal_type
        || !matches!(
            validate_resolved_declared_property_object(store, *empty_object),
            DeclaredPropertyObjectValidation::Valid(_)
        )
        || store
            .symbol_table(bootstrap.globals)
            .and_then(|globals| globals.get_source("NonNullable"))
            .and_then(|global| store.get_merged_symbol(global))
            != Some(alias)
    {
        return None;
    }

    let owner = store.symbol(alias)?;
    let [declaration] = owner.declarations()? else {
        return None;
    };
    let SourceNodeParent::Parent(source_file) = store.source_node_parent(*declaration)? else {
        return None;
    };
    if owner.flags() != SymbolFlags::TYPE_ALIAS
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some("NonNullable")
        || owner.parent().is_some()
        || owner.value_declaration().is_some()
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(alias) != Some(alias)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::TypeAliasDeclaration)
        || store.source_node_kind(source_file) != Some(SyntaxKind::SourceFile)
    {
        return None;
    }

    let links = store.type_alias_links(alias)?;
    let [declared_parameter] = links.type_parameters.as_deref()? else {
        return None;
    };
    let declared_type = links.declared_type?;
    if links
        .instantiations
        .as_ref()?
        .get(&type_list_key(&[*declared_parameter]))
        != Some(&declared_type)
    {
        return None;
    }

    let declared_owner = cached_ordinary_type_parameter_owner(store, *declared_parameter)?;
    let declared_symbol = store.symbol(declared_owner)?;
    let [parameter_declaration] = declared_symbol.declarations()? else {
        return None;
    };
    if declared_symbol.flags() != SymbolFlags::TYPE_PARAMETER
        || declared_symbol.check_flags() != CheckFlags::NONE
        || declared_symbol.name().as_utf8() != Some("T")
        || declared_symbol.parent().is_some()
        || declared_symbol.value_declaration().is_some()
        || declared_symbol.members().is_some()
        || declared_symbol.exports().is_some()
        || declared_symbol.export_symbol().is_some()
        || store.get_merged_symbol(declared_owner) != Some(declared_owner)
        || store.source_node_kind(*parameter_declaration) != Some(SyntaxKind::TypeParameter)
        || store.source_node_parent(*parameter_declaration)
            != Some(SourceNodeParent::Parent(*declaration))
        || cached_ordinary_type_parameter_owner(store, *parameter).is_none()
    {
        return None;
    }

    let declared = store
        .validate_deferred_intersection_type(declared_type)
        .ok()?;
    (declared.alias_symbol == Some(alias)
        && declared.alias_arguments == [*declared_parameter]
        && declared.types == [*declared_parameter, *empty_object])
    .then_some(*empty_object)
}

fn reduce_default_library_non_nullable_intersection(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    projection: &DeferredIntersectionTypeProjection,
    constituents: &[TypeId],
    alias_arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, InstantiationError> {
    let Some(empty_object) =
        authenticated_default_library_non_nullable_empty_object(store, projection)
    else {
        return Ok(None);
    };
    let [argument, mapped_empty_object] = constituents else {
        return Err(InstantiationError::UnsupportedType(source));
    };
    let [mapped_argument] = alias_arguments else {
        return Err(InstantiationError::UnsupportedType(source));
    };
    if argument != mapped_argument || *mapped_empty_object != empty_object {
        return Err(InstantiationError::UnsupportedType(source));
    }

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(InstantiationError::UnsupportedType(source))?;
    let record = store
        .type_payload(*argument)
        .ok_or(InstantiationError::InvalidType(*argument))?;
    if matches!(record.data(), TypeData::TypeParameter(_)) {
        return Ok(None);
    }
    if matches!(record.data(), TypeData::Conditional(_)) {
        conditional_alias_projection_with_array_targets(store, *argument, array_targets)
            .map_err(|_| InstantiationError::InvalidType(*argument))?;
        return Ok(None);
    }
    if record.flags().intersects(TypeFlags::NULLABLE) {
        return Ok(Some(bootstrap.never_type));
    }
    if record.flags().intersects(TypeFlags::UNKNOWN) {
        return Ok(Some(empty_object));
    }
    if record
        .flags()
        .intersects(TypeFlags::ANY | TypeFlags::NEVER | TypeFlags::DEFINITELY_NON_NULLABLE)
    {
        return Ok(Some(*argument));
    }

    let TypeData::Union(union) = record.data() else {
        return Err(InstantiationError::UnsupportedType(source));
    };
    match array_targets {
        Some(targets) => {
            store.validate_cached_union_result_with_array_targets(targets, *argument, None)
        }
        None => store.validate_cached_union_result(*argument, None),
    }
    .map_err(InstantiationError::Union)?;

    let mut survivor = None;
    for constituent in &union.union.types {
        let constituent_record = store
            .type_payload(*constituent)
            .ok_or(InstantiationError::InvalidType(*constituent))?;
        if constituent_record.flags().intersects(TypeFlags::NULLABLE) {
            continue;
        }
        if !constituent_record
            .flags()
            .intersects(TypeFlags::DEFINITELY_NON_NULLABLE)
            || survivor.replace(*constituent).is_some()
        {
            return Err(if record.alias().is_some() {
                InstantiationError::UnsupportedAliasedUnion(*argument)
            } else {
                InstantiationError::UnsupportedType(source)
            });
        }
    }
    Ok(Some(survivor.unwrap_or(bootstrap.never_type)))
}

fn deferred_intersection_error(source: TypeId, error: IntersectionTypeError) -> InstantiationError {
    match error {
        IntersectionTypeError::Capacity => {
            InstantiationError::Union(LiteralTypeCacheError::Capacity)
        }
        IntersectionTypeError::MalformedConstituent(_)
        | IntersectionTypeError::InvalidAliasSymbol(_)
        | IntersectionTypeError::InvalidCachedIntersection(_) => {
            InstantiationError::InvalidType(source)
        }
        _ => InstantiationError::UnsupportedType(source),
    }
}

fn cached_apply_mapping(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, InstantiationError> {
    store
        .type_payload(type_)
        .ok_or(InstantiationError::InvalidType(type_))?;
    let mapper = match mapping {
        InstantiationMapping::Vector { sources, targets } => {
            return Ok(Some(
                sources
                    .iter()
                    .position(|source| *source == type_)
                    .map_or(type_, |index| targets[index]),
            ));
        }
        InstantiationMapping::Stored(mapper) => mapper,
    };
    let application = store
        .mapper_application(mapper, type_)
        .ok_or(InstantiationError::InvalidMapper(mapper))?;
    match application {
        TypeMapperApplication::Direct(replacement) => Ok(Some(replacement)),
        TypeMapperApplication::Merged { first, second }
        | TypeMapperApplication::Composite { first, second } => {
            let Some(intermediate) = cached_apply_mapping(
                store,
                type_,
                InstantiationMapping::Stored(first),
                array_targets,
            )?
            else {
                return Ok(None);
            };
            if intermediate != type_
                && matches!(application, TypeMapperApplication::Composite { .. })
            {
                // The second mapper starts a separate type traversal.
                cached_instantiated_type_worker(
                    store,
                    intermediate,
                    InstantiationMapping::Stored(second),
                    array_targets,
                    None,
                    &mut HashSet::new(),
                )
            } else {
                cached_apply_mapping(
                    store,
                    intermediate,
                    InstantiationMapping::Stored(second),
                    array_targets,
                )
            }
        }
    }
}

fn apply_mapping(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    apply_mapping_with_source(store, type_, mapping, array_targets, session, None)
}

fn apply_mapping_with_source(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
    mut source: Option<&mut InstantiationSource<'_>>,
) -> Result<TypeId, InstantiationError> {
    match mapping {
        InstantiationMapping::Vector { sources, targets } => {
            if store.type_payload(type_).is_none() {
                return Err(InstantiationError::InvalidType(type_));
            }
            Ok(sources
                .iter()
                .position(|source| *source == type_)
                .map_or(type_, |index| targets[index]))
        }
        InstantiationMapping::Stored(mapper) => {
            if store.type_payload(type_).is_none() {
                return Err(InstantiationError::InvalidType(type_));
            }
            let application = store
                .mapper_application(mapper, type_)
                .ok_or(InstantiationError::InvalidMapper(mapper))?;
            match application {
                TypeMapperApplication::Direct(mapped_type) => Ok(mapped_type),
                TypeMapperApplication::Merged { first, second } => {
                    let intermediate = apply_mapping_with_source(
                        store,
                        type_,
                        InstantiationMapping::Stored(first),
                        array_targets,
                        session,
                        source.as_deref_mut(),
                    )?;
                    apply_mapping_with_source(
                        store,
                        intermediate,
                        InstantiationMapping::Stored(second),
                        array_targets,
                        session,
                        source,
                    )
                }
                TypeMapperApplication::Composite { first, second } => {
                    let intermediate = apply_mapping_with_source(
                        store,
                        type_,
                        InstantiationMapping::Stored(first),
                        array_targets,
                        session,
                        source.as_deref_mut(),
                    )?;
                    if intermediate == type_ {
                        apply_mapping_with_source(
                            store,
                            type_,
                            InstantiationMapping::Stored(second),
                            array_targets,
                            session,
                            source,
                        )
                    } else {
                        instantiate_type_with_alias_input_and_source(
                            store,
                            intermediate,
                            InstantiationMapping::Stored(second),
                            array_targets,
                            None,
                            session,
                            None,
                            source,
                        )
                    }
                }
            }
        }
    }
}

fn instantiate_array_reference(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: CanonicalArrayTargets,
    session: &mut InstantiationSession,
) -> Result<TypeId, InstantiationError> {
    instantiate_array_reference_with_operand(store, source, mapping, array_targets, session, None)
}

fn instantiate_array_reference_with_operand(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: CanonicalArrayTargets,
    session: &mut InstantiationSession,
    operand: Option<&SourceAliasOperandGraph>,
) -> Result<TypeId, InstantiationError> {
    let Some(reference) = store.canonical_array_reference_with_targets(array_targets, source)?
    else {
        return Err(InstantiationError::UnsupportedType(source));
    };
    let element = instantiate_type_with_alias_input_and_operand(
        store,
        reference.element_type,
        mapping,
        Some(array_targets),
        None,
        session,
        None,
        None,
        operand,
    )?;
    if element == reference.element_type {
        return Ok(source);
    }
    store
        .create_canonical_array_type_with_targets(array_targets, element, reference.readonly)
        .map_err(Into::into)
}

fn instantiable_union_source_types(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<&[TypeId], InstantiationError> {
    let record = store
        .type_payload(source)
        .ok_or(InstantiationError::InvalidType(source))?;
    let TypeData::Union(union) = record.data() else {
        return Err(InstantiationError::UnsupportedType(source));
    };
    if record.alias().is_some()
        || union.origin.is_some()
        || store.canonical_union_creation(source).is_some()
    {
        let validation = match array_targets {
            Some(targets) => {
                store.validate_cached_union_result_with_array_targets(targets, source, None)
            }
            None => store.validate_cached_union_result(source, None),
        };
        validation.map_err(|_| {
            if record.alias().is_some() {
                InstantiationError::UnsupportedAliasedUnion(source)
            } else {
                InstantiationError::UnsupportedUnionOrigin(source)
            }
        })?;
    }
    if let Some(origin) = union.origin
        && let Some(TypeData::Union(origin)) = store.type_payload(origin).map(TypeRecord::data)
    {
        return Ok(&origin.union.types);
    }
    Ok(&union.union.types)
}

fn instantiable_union_source_types_with_operand<'a>(
    store: &'a CanonicalTypeMapperStore,
    source: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    operand: Option<&SourceAliasOperandGraph>,
) -> Result<&'a [TypeId], InstantiationError> {
    let Some(operand) = operand else {
        return instantiable_union_source_types(store, source, array_targets);
    };
    // The graph checks every written child before the annotation-union cache,
    // including children removed by normal reduction.
    operand
        .mapping_type_is_closed(store, source, array_targets)
        .map_err(|_| InstantiationError::InvalidType(source))?;
    let Some(TypeData::Union(union)) = store.type_payload(source).map(TypeRecord::data) else {
        return Err(InstantiationError::InvalidType(source));
    };
    if let Some(origin) = union.origin
        && let Some(TypeData::Union(origin)) = store.type_payload(origin).map(TypeRecord::data)
    {
        return Ok(&origin.union.types);
    }
    Ok(&union.union.types)
}

fn instantiate_union(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    mapping: InstantiationMapping<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    alias_override: Option<(SemanticSymbolId, &[TypeId])>,
    session: &mut InstantiationSession,
    operand: Option<&SourceAliasOperandGraph>,
) -> Result<TypeId, InstantiationError> {
    let constituents =
        instantiable_union_source_types_with_operand(store, source, array_targets, operand)?
            .to_vec();
    let source_alias = store.type_payload(source).and_then(TypeRecord::alias);
    let alias = if let Some((symbol, arguments)) = alias_override {
        Some((symbol, arguments.to_vec()))
    } else {
        source_alias
            .map(|identity| {
                let alias = store
                    .type_alias(identity)
                    .ok_or(InstantiationError::InvalidAlias(identity))?;
                let symbol = alias
                    .symbol()
                    .ok_or(InstantiationError::InvalidAlias(identity))?;
                Ok::<_, InstantiationError>((
                    symbol,
                    alias.type_arguments().unwrap_or_default().to_vec(),
                ))
            })
            .transpose()?
    };
    let mut mapped_types = Vec::with_capacity(constituents.len());
    let mut changed = false;
    let mut contains_type_variable = false;
    for constituent in &constituents {
        if store.type_payload(*constituent).is_none() {
            return Err(InstantiationError::InvalidType(*constituent));
        }
        if operand.is_none()
            && !supported_instantiable_union_constituent(store, *constituent, array_targets)?
        {
            return Err(InstantiationError::UnsupportedUnionConstituent(
                *constituent,
            ));
        }
        contains_type_variable |= match operand {
            Some(operand) => !operand
                .mapping_type_is_closed(store, *constituent, array_targets)
                .map_err(|_| InstantiationError::InvalidType(*constituent))?,
            None => could_contain_installed_type_variables(store, *constituent, array_targets)?,
        };
    }
    if !contains_type_variable && alias.is_none() {
        return Ok(source);
    }
    for constituent in &constituents {
        let instantiated = instantiate_type_with_alias_input_and_operand(
            store,
            *constituent,
            mapping,
            array_targets,
            None,
            session,
            None,
            None,
            operand,
        )?;
        changed |= instantiated != *constituent;
        mapped_types.push(instantiated);
    }
    if !changed && alias.is_none() {
        return Ok(source);
    }
    if let Some((symbol, arguments)) = alias {
        let mut mapped_arguments = Vec::with_capacity(arguments.len());
        for argument in arguments {
            mapped_arguments.push(if alias_override.is_some() {
                argument
            } else {
                instantiate_type_with_alias_input_and_operand(
                    store,
                    argument,
                    mapping,
                    array_targets,
                    None,
                    session,
                    None,
                    None,
                    operand,
                )?
            });
        }
        return store
            .literal_union_type_with_alias_and_array_targets_and_session(
                &mapped_types,
                Some((symbol, &mapped_arguments)),
                array_targets,
                session,
            )
            .map_err(Into::into);
    }
    if mapped_types.iter().any(|type_| {
        matches!(
            store.type_payload(*type_).map(TypeRecord::data),
            Some(TypeData::TemplateLiteral(_) | TypeData::StringMapping(_))
        )
    }) {
        store
            .template_result_union_with_array_targets_and_session(
                &mapped_types,
                array_targets,
                session,
            )
            .map_err(Into::into)
    } else {
        store
            .literal_union_type_with_alias_and_array_targets_and_session(
                &mapped_types,
                None,
                array_targets,
                session,
            )
            .map_err(Into::into)
    }
}

pub(super) fn canonical_anonymous_union(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
) -> Result<TypeId, LiteralTypeCacheError> {
    let mut prepared = store.prepare_type_query_types(&[], &[], &[], 1, 0)?;
    store.literal_union_type_prepared(types, None, &mut prepared)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
        DeclaredTypeHost, DeclaredTypeLinks, IntrinsicBootstrapOptions, SemanticStore, SignatureId,
        ValueSymbolLinks,
        bootstrap::UnionReduction,
        conditional_types::{
            conditional_alias_projection, conditional_remap_projection,
            conditional_signature_projection,
        },
        declared::{get_declared_class_interface_or_type_parameter, type_list_key},
        keyof_types::resolve_nongeneric_keyof_type,
        links::TypeAliasLinks,
        mapper::TypeMapper,
        production::GlobalMergeCompletion,
        signatures::ElementFlags,
        template_types::MAX_TEMPLATE_UNION_SIZE,
        tuple_types::CanonicalTupleTypeRequest,
        type_nodes::CanonicalTypeQuery,
        type_records::{LiteralValue, TypeRecord},
        types::ObjectFlags,
    };
    use ts_ast::{FileId, NodeData, NodeRef, decode_js_string, encode_js_string};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SymbolData, SymbolFlags,
    };
    use ts_core::JsString;
    use ts_parser::{ParseResult, parse_source_file};

    #[test]
    #[allow(clippy::too_many_lines)] // One real source graph covers identity, mapper work, and both optional read modes.
    fn source_alias_bound_mapping_keeps_closed_identity_and_spent_caller() {
        use crate::semantic::object_aliases::source_alias_bound_test_support as fixture;

        let state = |session: &InstantiationSession| {
            (
                session.query_count(),
                session.total_count(),
                session.limit_event_count(),
                session.depth,
                session.active_mappers.len(),
            )
        };
        fixture::with_fixture(|context, files| {
            let mut closed = Vec::new();
            for name in ["EnvBound", "SchemaBound", "InputBound"] {
                let node = fixture::operand(context, files, name, 0, false);
                let (type_, graph) = fixture::prepare_graph(context, files, node);
                let parameter = context
                    .store()
                    .declared_type_links(graph.source().parameter().1)
                    .and_then(|links| links.declared_type)
                    .unwrap();
                closed.push((type_, graph, parameter));
            }
            let env = closed[0].0;
            let dependent_node = fixture::operand(context, files, "Dependent", 1, true);
            let (dependent, dependent_graph) =
                fixture::prepare_graph(context, files, dependent_node);
            let parameters = dependent_graph
                .source()
                .parameters()
                .iter()
                .map(|&(_, symbol)| {
                    context
                        .store()
                        .declared_type_links(symbol)
                        .and_then(|links| links.declared_type)
                        .unwrap()
                })
                .collect::<Vec<_>>();
            let [first, second] = parameters.as_slice() else {
                panic!("the source has two ordered alias formals");
            };
            let (first, second) = (*first, *second);
            assert_eq!(dependent, first);
            assert_eq!(
                cached_ordinary_type_parameter_owner(context.store(), second),
                Some(dependent_graph.source().parameter().1)
            );
            let array_node = fixture::operand(context, files, "ArrayDefault", 1, true);
            let (array, array_graph) = fixture::prepare_graph(context, files, array_node);
            let array_parameter = context
                .store()
                .declared_type_links(array_graph.source().parameters()[0].1)
                .and_then(|links| links.declared_type)
                .unwrap();
            let targets = CanonicalArrayTargets::from_global_types(context.global_types());
            let (error_type, empty, undefined, missing) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                assert!(bootstrap.options.strict_null_checks);
                assert!(bootstrap.options.exact_optional_property_types);
                assert_eq!(bootstrap.undefined_or_missing_type, bootstrap.missing_type);
                (
                    bootstrap.error_type,
                    bootstrap.empty_type_literal_type,
                    bootstrap.undefined_type,
                    bootstrap.missing_type,
                )
            };
            let store = context.store_mut_for_test();
            let before = format!("{store:?}");
            let zero_limits = InstantiationLimits {
                max_depth: 100,
                max_count: 0,
            };
            let mut zero =
                InstantiationSession::new_recovering(store, zero_limits, error_type).unwrap();
            for (type_, graph, parameter) in &closed {
                let alias = store.type_payload(*type_).unwrap().alias();
                assert_eq!(
                    instantiate_source_alias_operand_with_session(
                        store,
                        graph,
                        *type_,
                        &[*parameter],
                        &[*type_],
                        Some(targets),
                        &mut zero,
                    ),
                    Ok(*type_)
                );
                assert_eq!(
                    cached_source_alias_operand_instantiation(
                        store,
                        graph,
                        *type_,
                        &[*parameter],
                        &[*type_],
                        Some(targets),
                    ),
                    Ok(Some(*type_))
                );
                assert_eq!(store.type_payload(*type_).unwrap().alias(), alias);
                assert_eq!(state(&zero), (0, 0, 0, 0, 0));
                assert_eq!(format!("{store:?}"), before);
            }

            let changed_graph = fixture::without_closed_object(&closed[0].1);
            assert_eq!(
                instantiate_source_alias_operand_with_session(
                    store,
                    &changed_graph,
                    env,
                    &[closed[0].2],
                    &[env],
                    Some(targets),
                    &mut zero,
                ),
                Err(InstantiationError::InvalidType(env))
            );
            assert_eq!(
                cached_source_alias_operand_instantiation(
                    store,
                    &changed_graph,
                    env,
                    &[closed[0].2],
                    &[env],
                    Some(targets),
                ),
                Err(InstantiationError::InvalidType(env))
            );
            assert_eq!(state(&zero), (0, 0, 0, 0, 0));
            assert_eq!(format!("{store:?}"), before);

            let mut success = InstantiationSession::new(InstantiationLimits {
                max_depth: 100,
                max_count: 2,
            });
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    first,
                    &[first],
                    &[env],
                    Some(targets),
                    &mut success,
                ),
                Ok(env)
            );
            assert_eq!(state(&success), (1, 1, 0, 0, 0));
            assert_eq!(
                instantiate_source_alias_operand_with_session(
                    store,
                    &dependent_graph,
                    dependent,
                    &[first],
                    &[env],
                    Some(targets),
                    &mut success,
                ),
                Ok(env)
            );
            assert_eq!(state(&success), (2, 2, 0, 0, 0));
            assert_eq!(
                cached_source_alias_operand_instantiation(
                    store,
                    &dependent_graph,
                    dependent,
                    &[first],
                    &[env],
                    Some(targets),
                ),
                Ok(Some(env))
            );
            assert_eq!(format!("{store:?}"), before);

            // Source-default comparison substitutes the actual selected formal,
            // even when that formal is not the first row.
            let mut selected = InstantiationSession::new(InstantiationLimits::default());
            assert_eq!(
                instantiate_source_alias_operand_with_session(
                    store,
                    &dependent_graph,
                    dependent,
                    &[second],
                    &[env],
                    Some(targets),
                    &mut selected,
                ),
                Ok(first)
            );
            assert_eq!(state(&selected), (1, 1, 0, 0, 0));
            assert_eq!(format!("{store:?}"), before);

            for recover in [false, true] {
                let limits = InstantiationLimits {
                    max_depth: 100,
                    max_count: 1,
                };
                let mut spent = if recover {
                    InstantiationSession::new_recovering(store, limits, error_type).unwrap()
                } else {
                    InstantiationSession::new(limits)
                };
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        store,
                        first,
                        &[first],
                        &[env],
                        Some(targets),
                        &mut spent,
                    ),
                    Ok(env)
                );
                assert_eq!(state(&spent), (1, 1, 0, 0, 0));
                let result = instantiate_source_alias_operand_with_session(
                    store,
                    &dependent_graph,
                    dependent,
                    &[first],
                    &[env],
                    Some(targets),
                    &mut spent,
                );
                assert_eq!(
                    result,
                    if recover {
                        Ok(error_type)
                    } else {
                        Err(InstantiationError::CountLimit { count: 1, limit: 1 })
                    }
                );
                assert_eq!(state(&spent), (1, 1, 1, 0, 0));
                assert_eq!(format!("{store:?}"), before);
            }
            assert_eq!(
                instantiate_source_alias_operand_with_session(
                    store,
                    &dependent_graph,
                    dependent,
                    &[first],
                    &[env],
                    Some(targets),
                    &mut zero,
                ),
                Ok(error_type)
            );
            assert_eq!(state(&zero), (0, 0, 1, 0, 0));
            assert_eq!(format!("{store:?}"), before);

            let mut array_caller = InstantiationSession::new(InstantiationLimits {
                max_depth: 100,
                max_count: 3,
            });
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    array_parameter,
                    &[array_parameter],
                    &[env],
                    Some(targets),
                    &mut array_caller,
                ),
                Ok(env)
            );
            let array_result = instantiate_source_alias_operand_with_session(
                store,
                &array_graph,
                array,
                &[array_parameter],
                &[env],
                Some(targets),
                &mut array_caller,
            )
            .unwrap();
            assert_eq!(state(&array_caller), (3, 3, 0, 0, 0));
            let reference = store
                .canonical_array_reference_with_targets(targets, array_result)
                .unwrap()
                .unwrap();
            assert_eq!(reference.element_type, env);
            assert!(!reference.readonly);
            let warm = format!("{store:?}");
            assert_eq!(
                cached_source_alias_operand_instantiation(
                    store,
                    &array_graph,
                    array,
                    &[array_parameter],
                    &[env],
                    Some(targets),
                ),
                Ok(Some(array_result))
            );
            let mut nested_spent = InstantiationSession::new(InstantiationLimits {
                max_depth: 100,
                max_count: 2,
            });
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    array_parameter,
                    &[array_parameter],
                    &[env],
                    Some(targets),
                    &mut nested_spent,
                ),
                Ok(env)
            );
            assert_eq!(
                instantiate_source_alias_operand_with_session(
                    store,
                    &array_graph,
                    array,
                    &[array_parameter],
                    &[env],
                    Some(targets),
                    &mut nested_spent,
                ),
                Err(InstantiationError::CountLimit { count: 2, limit: 2 })
            );
            assert_eq!(state(&nested_spent), (2, 2, 1, 0, 0));
            let mut missing_targets = InstantiationSession::new(InstantiationLimits::default());
            assert_eq!(
                instantiate_source_alias_operand_with_session(
                    store,
                    &array_graph,
                    array,
                    &[array_parameter],
                    &[env],
                    None,
                    &mut missing_targets,
                ),
                Err(InstantiationError::InvalidType(array))
            );
            assert_eq!(state(&missing_targets), (0, 0, 0, 0, 0));
            assert_eq!(format!("{store:?}"), warm);

            let input_graph = &closed[2].1;
            let indexed = context
                .store()
                .source_direct_children(input_graph.source().root())
                .unwrap()
                .into_iter()
                .find(|&node| {
                    context.store().source_node_kind(node) == Some(SyntaxKind::IndexedAccessType)
                })
                .unwrap();
            let host = context
                .declared_type_host()
                .unwrap()
                .with_module_resolutions(context.module_resolutions());
            let plan = super::super::indexed_access_types::plan_source_alias_indexed_bound(
                context.store(),
                &host,
                input_graph.source(),
                indexed,
            )
            .unwrap();
            let store = context.store();
            let object = store
                .type_node_links(plan.object())
                .and_then(|links| links.resolved_type)
                .unwrap();
            let key = store
                .type_node_links(plan.index())
                .and_then(|links| links.resolved_type)
                .unwrap();
            let selection = plan
                .checked_selection(store, input_graph, object, key, Some(targets))
                .unwrap();
            assert!(selection.optional());
            assert_eq!(selection.value_type(), empty);
            assert_ne!(undefined, missing);
            let before_read = format!("{store:?}");
            assert_eq!(
                indexed_access_property_optional_sentinel(
                    store,
                    selection.property(),
                    selection.value_type(),
                ),
                Ok(Some(missing))
            );
            assert_eq!(
                resolved_indexed_access_members(store, object, Some(targets)),
                Err(InstantiationError::InvalidType(object))
            );
            let source_read = cached_source_alias_indexed_read(
                store,
                &plan,
                input_graph,
                object,
                key,
                Some(targets),
            )
            .unwrap()
            .unwrap();
            assert_eq!(
                store
                    .type_node_links(indexed)
                    .and_then(|links| links.resolved_type),
                Some(source_read)
            );
            let TypeData::Union(union) = store.type_payload(source_read).unwrap().data() else {
                panic!("the optional source read keeps its undefined union");
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&empty));
            assert!(union.union.types.contains(&undefined));
            assert!(!union.union.types.contains(&missing));
            assert_eq!(
                store
                    .value_symbol_links(selection.property())
                    .and_then(|links| links.resolved_type),
                Some(empty)
            );
            assert_eq!(format!("{store:?}"), before_read);
            assert!(context.diagnostics().is_empty());
        });
    }

    struct DeferredGenericIntersectionFixture {
        store: CanonicalTypeMapperStore,
        intersection: TypeId,
        class_reference: TypeId,
        attributes_reference: TypeId,
        element: TypeId,
        props: TypeId,
        string: TypeId,
        alias: SemanticSymbolId,
        outer_aliases: [SemanticSymbolId; 2],
        argument_alias: SemanticSymbolId,
        outer_parameters: [TypeId; 2],
    }

    #[allow(clippy::too_many_lines)] // The fixture binds one complete generic alias graph.
    fn deferred_generic_intersection_fixture() -> DeferredGenericIntersectionFixture {
        let parsed = parse_source_file(concat!(
            "interface ClassAttributes<T> {}\n",
            "interface HTMLAttributes<T> {}\n",
            "type DetailedHTMLProps<E, T> = ClassAttributes<T> & E;\n",
            "type Probe = unknown; type Other = unknown;\n",
            "type Forward<Left, Right> = unknown;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_551);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/deferred-intersection.ts\""),
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
        let locals = bound.locals(bound.source_file()).unwrap();
        let class_symbol = store
            .symbol_table(locals)
            .unwrap()
            .get_source("ClassAttributes")
            .unwrap();
        let attributes_symbol = store
            .symbol_table(locals)
            .unwrap()
            .get_source("HTMLAttributes")
            .unwrap();
        let alias = store
            .symbol_table(locals)
            .unwrap()
            .get_source("DetailedHTMLProps")
            .unwrap();
        let outer_aliases = ["Probe", "Other"].map(|name| {
            store
                .symbol_table(locals)
                .unwrap()
                .get_source(name)
                .unwrap()
        });
        let argument_alias = store
            .symbol_table(locals)
            .unwrap()
            .get_source("Forward")
            .unwrap();
        let declaration = store.symbol(alias).unwrap().declarations().unwrap()[0];
        let NodeData::TypeAliasDeclaration(alias_declaration) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("the deferred intersection fixture must bind its alias")
        };
        let [props_node, element_node] = alias_declaration
            .type_parameters
            .as_ref()
            .unwrap()
            .nodes
            .as_slice()
        else {
            panic!("the deferred intersection fixture must bind E and T")
        };
        let props_symbol = bound
            .symbol(NodeRef::new(parsed.arena.id(), file, *props_node))
            .unwrap();
        let element_symbol = bound
            .symbol(NodeRef::new(parsed.arena.id(), file, *element_node))
            .unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let class_target = get_declared_class_interface_or_type_parameter(
            &mut store,
            &host,
            class_symbol,
            SymbolFlags::INTERFACE,
        )
        .unwrap()
        .unwrap();
        let attributes_target = get_declared_class_interface_or_type_parameter(
            &mut store,
            &host,
            attributes_symbol,
            SymbolFlags::INTERFACE,
        )
        .unwrap()
        .unwrap();
        let props = get_declared_class_interface_or_type_parameter(
            &mut store,
            &host,
            props_symbol,
            SymbolFlags::TYPE_PARAMETER,
        )
        .unwrap()
        .unwrap();
        let element = get_declared_class_interface_or_type_parameter(
            &mut store,
            &host,
            element_symbol,
            SymbolFlags::TYPE_PARAMETER,
        )
        .unwrap()
        .unwrap();
        let outer_declaration = store
            .symbol(argument_alias)
            .unwrap()
            .declarations()
            .unwrap()[0];
        let NodeData::TypeAliasDeclaration(outer) =
            &parsed.arena.get(outer_declaration.node).unwrap().data
        else {
            panic!("Forward retains its bound type parameters")
        };
        let outer_parameters = outer
            .type_parameters
            .as_ref()
            .unwrap()
            .nodes
            .iter()
            .map(|node| {
                let symbol = bound
                    .symbol(NodeRef::new(parsed.arena.id(), file, *node))
                    .unwrap();
                get_declared_class_interface_or_type_parameter(
                    &mut store,
                    &host,
                    symbol,
                    SymbolFlags::TYPE_PARAMETER,
                )
                .unwrap()
                .unwrap()
            })
            .collect::<Vec<_>>();
        let outer_parameters: [TypeId; 2] = outer_parameters.try_into().unwrap();
        assert!(store.set_type_alias_links(
            argument_alias,
            TypeAliasLinks {
                type_parameters: Some(outer_parameters.to_vec()),
                ..TypeAliasLinks::default()
            }
        ));
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let class_reference = create_direct_generic_reference(
            &mut store,
            class_target,
            &[element],
            ObjectFlags::NONE,
        )
        .unwrap();
        let attributes_reference = create_direct_generic_reference(
            &mut store,
            attributes_target,
            &[string],
            ObjectFlags::NONE,
        )
        .unwrap();
        let intersection = store
            .canonical_deferred_intersection_type(
                &[class_reference, props],
                Some((alias, &[props, element])),
            )
            .unwrap();
        DeferredGenericIntersectionFixture {
            store,
            intersection,
            class_reference,
            attributes_reference,
            element,
            props,
            string,
            alias,
            outer_aliases,
            argument_alias,
            outer_parameters,
        }
    }

    struct NonemptyDeferredGenericIntersectionFixture<'arena> {
        context: CanonicalCheckerContext<'arena>,
        intersection: TypeId,
        sources: [TypeId; 2],
        targets: [TypeId; 2],
        source_alias: SemanticSymbolId,
        owner: SemanticSymbolId,
    }

    #[allow(clippy::too_many_lines)] // Keep checked properties and unchecked alias identities in one fixture.
    fn nonempty_deferred_generic_intersection_fixture<'arena>(
        parsed: &'arena ParseResult,
        template: &'arena ParseResult,
    ) -> NonemptyDeferredGenericIntersectionFixture<'arena> {
        let file = FileId::new(8_552);
        let template_file = FileId::new(8_553);
        let mut binder = CanonicalBinder::new();
        for (source, file, path) in [
            (parsed, file, "\"/nonempty-deferred-intersection.ts\""),
            (
                template,
                template_file,
                "\"/deferred-intersection-template.ts\"",
            ),
        ] {
            assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&source.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena), (template_file, &template.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        // Check only the concrete reference source to publish its declared property
        // types. The generic intersection stays on the kernel construction path.
        context.check_source_file(file).unwrap();
        let [source_alias, owner, left, right] = [
            (template_file, "DetailedHTMLProps"),
            (template_file, "Probe"),
            (file, "Left"),
            (file, "Right"),
        ]
        .map(|(file, name)| {
            let bound = context.file(file).unwrap().1;
            let locals = bound.locals(bound.source_file()).unwrap();
            context
                .store()
                .symbol_table(locals)
                .unwrap()
                .get_source(name)
                .unwrap()
        });
        let [class, attributes] = [left, right].map(|symbol| {
            context
                .store()
                .type_alias_links(symbol)
                .unwrap()
                .declared_type
                .unwrap()
        });
        let declaration = context
            .store()
            .symbol(source_alias)
            .unwrap()
            .declarations()
            .unwrap()[0];
        let NodeData::TypeAliasDeclaration(alias) =
            &template.arena.get(declaration.node).unwrap().data
        else {
            panic!("the nonempty fixture must retain its declared intersection alias")
        };
        let [props_node, element_node] = alias.type_parameters.as_ref().unwrap().nodes.as_slice()
        else {
            panic!("the nonempty fixture must bind E and T")
        };
        let parameter_symbols = [props_node, element_node].map(|node| {
            context
                .file(template_file)
                .unwrap()
                .1
                .symbol(NodeRef::new(template.arena.id(), template_file, *node))
                .unwrap()
        });
        let [props, element] =
            parameter_symbols.map(|symbol| context.get_declared_type_of_symbol(symbol).unwrap());
        let store = context.store_mut_for_test();
        let class_target = validate_direct_generic_reference(store, class)
            .unwrap()
            .target;
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let class_reference =
            create_direct_generic_reference(store, class_target, &[element], ObjectFlags::NONE)
                .unwrap();
        let intersection = store
            .canonical_deferred_intersection_type(
                &[class_reference, props],
                Some((source_alias, &[props, element])),
            )
            .unwrap();
        NonemptyDeferredGenericIntersectionFixture {
            context,
            intersection,
            sources: [props, element],
            targets: [attributes, string],
            source_alias,
            owner,
        }
    }

    fn deferred_intersection_store_state(
        store: &CanonicalTypeMapperStore,
    ) -> ([usize; 7], [usize; 26]) {
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
    }

    const SELECTION_INSTANTIATION_SOURCE: &str = concat!(
        "type Selection<S, K extends keyof S> = { [P in K]: S[P] }; ",
        "declare function select<O, K extends keyof O>(object: O, key: K): Selection<O, K>;",
    );

    struct SelectionInstantiationFixture<'arena> {
        context: CanonicalCheckerContext<'arena>,
        signature: SignatureId,
        returned: TypeId,
        parameters: [TypeId; 2],
        alias: SemanticSymbolId,
        fresh: TypeId,
    }

    #[allow(clippy::too_many_lines)] // The fixture retains both the signature and real object source.
    fn selection_instantiation_fixture<'arena>(
        template: &'arena ParseResult,
        values: &'arena ParseResult,
    ) -> SelectionInstantiationFixture<'arena> {
        let template_file = FileId::new(202_721);
        let values_file = FileId::new(202_722);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path) in [
            (template, template_file, "\"/selection-template.ts\""),
            (values, values_file, "\"/selection-values.ts\""),
        ] {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
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
            vec![
                (template_file, &template.arena),
                (values_file, &values.arena),
            ],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(values_file).unwrap();
        assert!(context.diagnostics().is_empty());
        let template_bound = context.file(template_file).unwrap().1.clone();
        let values_bound = context.file(values_file).unwrap().1.clone();
        let options = context.options();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&template.arena, &template_bound),
                (&values.arena, &values_bound),
            ],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let declaration = template
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    template.arena.id(),
                    template_file,
                    node,
                ))
            })
            .unwrap();
        let owner = template_bound.symbol(declaration).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let store = context.store_mut_for_test();
        let callable = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
        )
        .unwrap()
        .get_type_of_source_callable(declaration, owner)
        .unwrap();
        let signature = store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let parameters = store
            .signature(signature)
            .unwrap()
            .type_parameters()
            .to_vec();
        let returned = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
        )
        .unwrap()
        .get_return_type_of_signature(signature)
        .unwrap();
        assert!(diagnostics.is_empty());
        assert!(
            store
                .source_callable_type_query(signature)
                .unwrap()
                .is_exact(store)
        );
        let projection = supported_mapped_alias_projection(store, returned, None)
            .unwrap()
            .unwrap();
        assert_eq!(projection.identity_arguments, projection.arguments);
        let initializer = values
            .arena
            .iter()
            .find_map(|(_, record)| match &record.data {
                NodeData::VariableDeclaration(variable) => variable
                    .initializer
                    .map(|node| NodeRef::new(values.arena.id(), values_file, node)),
                _ => None,
            })
            .unwrap();
        let fresh = store
            .type_node_links(initializer)
            .unwrap()
            .resolved_type
            .unwrap();
        assert!(store.validate_fresh_object_literal_for_relation(fresh));
        SelectionInstantiationFixture {
            context,
            signature,
            returned,
            parameters: parameters.try_into().unwrap(),
            alias: projection.alias,
            fresh,
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One source checks fresh, regular, and widened identities.
    fn generic_keyof_instantiation_keeps_source_object_identity_and_warm_caches() {
        let template = parse_source_file(SELECTION_INSTANTIATION_SOURCE);
        let values = parse_source_file(
            "const object: any = { a: 'a', b: 'b', nested: { missing: undefined } };",
        );
        let mut fixture = selection_instantiation_fixture(&template, &values);
        let sources = fixture.parameters;
        let store = fixture.context.store_mut_for_test();
        let plan = plan_nongeneric_keyof_type(store, sources[0]).unwrap();
        let index = resolve_nongeneric_keyof_type(store, &plan).unwrap();
        assert_eq!(
            validate_generic_keyof_index_type(store, index),
            Ok(sources[0])
        );
        assert_eq!(
            validate_instantiable_member_type(store, index, &sources, None),
            Ok(())
        );
        let regular = store
            .get_regular_type_of_object_literal(fixture.fresh)
            .unwrap();
        let widened = store.get_widened_type(regular).unwrap();
        assert_ne!(regular, fixture.fresh);
        assert_ne!(widened, regular);
        let keys = ["a", "b", "nested"]
            .map(|name| store.regular_string_literal_type(name.into()).unwrap());
        let expected = store.literal_union_type(&keys, None).unwrap();
        for object in [fixture.fresh, regular, widened] {
            let targets = [object, keys[1]];
            let mapper = store
                .new_type_mapper(sources.to_vec(), targets.to_vec())
                .unwrap();
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    index,
                    &sources,
                    &targets,
                    None,
                    &mut session,
                ),
                Ok(expected)
            );
            assert_eq!(
                validate_instantiable_member_type(store, object, &sources, None),
                Ok(())
            );
            let before = deferred_intersection_store_state(store);
            for _ in 0..2 {
                assert_eq!(
                    instantiate_type_with_session(store, index, mapper, None, &mut session),
                    Ok(expected)
                );
                assert_eq!(
                    cached_instantiation_with_vector(store, index, &sources, &targets, None, None),
                    Ok(Some(expected))
                );
                assert_eq!(
                    instantiated_member_type_matches(store, index, expected, mapper, None),
                    Ok(true)
                );
            }
            let mut zero = InstantiationSession::new(InstantiationLimits {
                max_depth: 0,
                max_count: 0,
            });
            let mark = zero.limit_event_mark();
            assert_eq!(
                instantiate_type_with_session(store, object, mapper, None, &mut zero),
                Ok(object)
            );
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store, object, &sources, &targets, None, &mut zero,
                ),
                Ok(object)
            );
            assert_eq!(
                cached_instantiation_with_vector(store, object, &sources, &targets, None, None),
                Ok(Some(object))
            );
            assert_eq!(
                (zero.depth, zero.query_count(), zero.total_count()),
                (0, 0, 0)
            );
            assert_eq!(zero.limit_event_mark(), mark);
            assert_eq!(deferred_intersection_store_state(store), before);
        }
    }

    #[test]
    fn generic_keyof_instantiation_substitutes_authenticated_union_members() {
        let template = parse_source_file(SELECTION_INSTANTIATION_SOURCE);
        let values = parse_source_file("const object = { a: 'a', b: 'b' };");
        let mut fixture = selection_instantiation_fixture(&template, &values);
        let sources = fixture.parameters;
        let store = fixture.context.store_mut_for_test();
        let plan = plan_nongeneric_keyof_type(store, sources[0]).unwrap();
        let index = resolve_nongeneric_keyof_type(store, &plan).unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let keys = ["a", "b"].map(|name| store.regular_string_literal_type(name.into()).unwrap());
        let targets = [fixture.fresh, keys[1]];
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![index, number])
            .unwrap();
        assert_eq!(
            validate_instantiable_member_type(store, union, &sources, None),
            Ok(())
        );
        let expected = store
            .literal_union_type(&[keys[0], keys[1], number], None)
            .unwrap();
        let mapper = store
            .new_type_mapper(sources.to_vec(), targets.to_vec())
            .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        assert_eq!(
            instantiate_type_with_session(store, union, mapper, None, &mut session),
            Ok(expected)
        );
        let before = deferred_intersection_store_state(store);
        assert_eq!(
            instantiate_type_with_vector_and_session(
                store,
                union,
                &sources,
                &targets,
                None,
                &mut session,
            ),
            Ok(expected)
        );
        assert_eq!(
            cached_instantiation_with_vector(store, union, &sources, &targets, None, None),
            Ok(Some(expected))
        );
        assert_eq!(
            instantiated_member_type_matches(store, union, expected, mapper, None),
            Ok(true)
        );
        assert_eq!(deferred_intersection_store_state(store), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The symbolic and instantiated records are checked together.
    fn selection_mapped_alias_instantiation_preserves_the_symbolic_signature() {
        let template = parse_source_file(SELECTION_INSTANTIATION_SOURCE);
        let values = parse_source_file("const object = { a: 'a', b: 'b' };");
        let mut fixture = selection_instantiation_fixture(&template, &values);
        let sources = fixture.parameters;
        let store = fixture.context.store_mut_for_test();
        let b = store.regular_string_literal_type("b".into()).unwrap();
        let targets = [fixture.fresh, b];
        let substitution = store
            .new_type_mapper(sources.to_vec(), targets.to_vec())
            .unwrap();
        let projection = supported_mapped_alias_projection(store, fixture.returned, None)
            .unwrap()
            .unwrap();
        assert_eq!(projection.arguments, sources);
        assert_eq!(projection.identity_arguments, sources);
        let TypeData::Mapped(symbolic) = store.type_payload(fixture.returned).unwrap().data()
        else {
            panic!("the signature must keep its symbolic selection alias");
        };
        let symbolic = symbolic.clone();
        let evidence = store.source_callable_type_query(fixture.signature).unwrap();
        let annotation = evidence.callable().return_type.type_node().unwrap();
        assert_eq!(evidence.annotation_type(annotation), Some(fixture.returned));
        assert_eq!(
            validate_instantiable_member_type(store, fixture.returned, &sources, None),
            Ok(())
        );
        assert_eq!(
            cached_instantiation_with_vector(
                store,
                fixture.returned,
                &sources,
                &targets,
                None,
                None
            ),
            Ok(None)
        );
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let result = instantiate_type_with_vector_and_session(
            store,
            fixture.returned,
            &sources,
            &targets,
            None,
            &mut session,
        )
        .unwrap();
        let TypeData::Mapped(mapped) = store.type_payload(result).unwrap().data() else {
            panic!("selection substitution must keep a mapped alias");
        };
        assert_eq!(mapped.object.target, symbolic.object.target);
        assert_eq!(mapped.modifiers_type, Some(fixture.fresh));
        assert_eq!(mapped.constraint_type, Some(b));
        assert_eq!(mapped.object.structured, StructuredTypeData::default());
        let TypeData::IndexedAccess(indexed) = store
            .type_payload(mapped.template_type.unwrap())
            .unwrap()
            .data()
        else {
            panic!("selection values must keep their deferred indexed template");
        };
        assert_eq!(indexed.object_type, fixture.fresh);
        assert_eq!(Some(indexed.index_type), mapped.type_parameter);
        assert!(!sources.contains(&indexed.index_type));
        let identity = store
            .type_alias(store.type_payload(result).unwrap().alias().unwrap())
            .unwrap();
        assert_eq!(identity.symbol(), Some(fixture.alias));
        assert_eq!(identity.type_arguments(), Some(targets.as_slice()));
        let alias_links = store.type_alias_links(fixture.alias).unwrap().clone();
        assert_eq!(
            alias_links
                .instantiations
                .as_ref()
                .unwrap()
                .get(&type_alias_instantiation_cache_key(&targets, None)),
            Some(&result)
        );
        let before = deferred_intersection_store_state(store);
        for _ in 0..2 {
            assert_eq!(
                instantiate_type_with_session(
                    store,
                    fixture.returned,
                    substitution,
                    None,
                    &mut session
                ),
                Ok(result)
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    fixture.returned,
                    &sources,
                    &targets,
                    None,
                    None,
                ),
                Ok(Some(result))
            );
            assert_eq!(
                instantiated_member_type_matches(
                    store,
                    fixture.returned,
                    result,
                    substitution,
                    None
                ),
                Ok(true)
            );
            assert_eq!(store.type_alias_links(fixture.alias), Some(&alias_links));
            assert_eq!(deferred_intersection_store_state(store), before);
        }
        assert_eq!(
            store.type_payload(fixture.returned).unwrap().data(),
            &TypeData::Mapped(symbolic)
        );
        assert_eq!(
            store
                .signature(fixture.signature)
                .unwrap()
                .type_parameters(),
            &sources
        );
        assert_eq!(
            store
                .signature(fixture.signature)
                .unwrap()
                .resolved_return_type(),
            Some(fixture.returned)
        );
        let evidence = store.source_callable_type_query(fixture.signature).unwrap();
        assert!(evidence.is_exact(store));
        assert_eq!(evidence.annotation_type(annotation), Some(fixture.returned));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Both mapper representations share each nested limit case.
    fn generic_keyof_and_selection_alias_keep_the_callers_nested_limit_budget() {
        let template = parse_source_file(SELECTION_INSTANTIATION_SOURCE);
        let values = parse_source_file("const object = { a: 'a', b: 'b' };");
        let mut fixture = selection_instantiation_fixture(&template, &values);
        let sources = fixture.parameters;
        let store = fixture.context.store_mut_for_test();
        let b = store.regular_string_literal_type("b".into()).unwrap();
        let targets = [fixture.fresh, b];
        let mapper = store
            .new_type_mapper(sources.to_vec(), targets.to_vec())
            .unwrap();
        let plan = plan_nongeneric_keyof_type(store, sources[0]).unwrap();
        let index = resolve_nongeneric_keyof_type(store, &plan).unwrap();
        let error_type = store.intrinsic_bootstrap().unwrap().error_type;
        let alias_links = store.type_alias_links(fixture.alias).unwrap().clone();
        let before = deferred_intersection_store_state(store);
        for source in [index, fixture.returned] {
            for stored in [false, true] {
                for depth_limit in [false, true] {
                    for recovering in [false, true] {
                        let limits = if depth_limit {
                            InstantiationLimits {
                                max_depth: 4,
                                max_count: 50,
                            }
                        } else {
                            InstantiationLimits {
                                max_depth: 50,
                                max_count: 8,
                            }
                        };
                        let mut session = if recovering {
                            InstantiationSession::new_recovering(store, limits, error_type).unwrap()
                        } else {
                            InstantiationSession::new(limits)
                        };
                        session.depth = 3;
                        session.count = 7;
                        session.total_count = 11;
                        let mapping = if stored {
                            InstantiationMapping::Stored(mapper)
                        } else {
                            InstantiationMapping::Vector {
                                sources: &sources,
                                targets: &targets,
                            }
                        };
                        let retained = InstantiationCacheKey::Type {
                            type_: sources[1],
                            alias: InstantiationAliasCacheKey::None,
                        };
                        session.active_mappers.push(ActiveMapperFrame {
                            mapping: mapping.identity(),
                            cache: HashMap::from([(retained.clone(), b)]),
                        });
                        let mark = session.limit_event_mark();
                        let result = instantiate_type_with_alias(
                            store,
                            source,
                            mapping,
                            None,
                            None,
                            &mut session,
                        );
                        if recovering {
                            assert_eq!(result, Ok(error_type));
                        } else if depth_limit {
                            assert_eq!(
                                result,
                                Err(InstantiationError::DepthLimit { depth: 4, limit: 4 })
                            );
                        } else {
                            assert_eq!(
                                result,
                                Err(InstantiationError::CountLimit { count: 8, limit: 8 })
                            );
                        }
                        assert!(session.limit_event_occurred_since(mark));
                        assert_eq!(
                            (session.depth, session.query_count(), session.total_count()),
                            (3, 8, 12)
                        );
                        assert_eq!(session.active_mappers.len(), 1);
                        assert_eq!(session.active_mappers[0].cache.get(&retained), Some(&b));
                        let root_key = InstantiationCacheKey::Type {
                            type_: source,
                            alias: InstantiationAliasCacheKey::None,
                        };
                        assert_eq!(session.active_mappers[0].cache.get(&root_key), None);
                        assert_eq!(store.type_alias_links(fixture.alias), Some(&alias_links));
                        assert_eq!(deferred_intersection_store_state(store), before);
                    }
                }
            }
        }
        assert_eq!(
            cached_instantiation_with_vector(store, index, &sources, &targets, None, None),
            Ok(None)
        );
        assert_eq!(
            cached_instantiation_with_vector(
                store,
                fixture.returned,
                &sources,
                &targets,
                None,
                None
            ),
            Ok(None)
        );
    }

    #[test]
    fn generic_keyof_and_selection_alias_do_not_treat_an_ordinary_error_argument_as_a_limit() {
        let template = parse_source_file(SELECTION_INSTANTIATION_SOURCE);
        let values = parse_source_file("const object = { a: 'a', b: 'b' };");
        let mut fixture = selection_instantiation_fixture(&template, &values);
        let sources = fixture.parameters;
        let store = fixture.context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let error_type = bootstrap.error_type;
        let property_keys = bootstrap.string_number_symbol_type;
        let b = store.regular_string_literal_type("b".into()).unwrap();
        let targets = [error_type, b];
        let plan = plan_nongeneric_keyof_type(store, sources[0]).unwrap();
        let index = resolve_nongeneric_keyof_type(store, &plan).unwrap();
        let mut ordinary = InstantiationSession::new(InstantiationLimits::default());
        let mut recovering =
            InstantiationSession::new_recovering(store, InstantiationLimits::default(), error_type)
                .unwrap();
        recovering.limit_event_generation = 9;
        let mark = recovering.limit_event_mark();
        for source in [index, fixture.returned] {
            let result = instantiate_type_with_vector_and_session(
                store,
                source,
                &sources,
                &targets,
                None,
                &mut ordinary,
            )
            .unwrap();
            assert_ne!(result, error_type);
            if source == index {
                assert_eq!(result, property_keys);
            }
            let before = deferred_intersection_store_state(store);
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    source,
                    &sources,
                    &targets,
                    None,
                    &mut recovering,
                ),
                Ok(result)
            );
            assert_eq!(
                cached_instantiation_with_vector(store, source, &sources, &targets, None, None),
                Ok(Some(result))
            );
            assert_eq!(deferred_intersection_store_state(store), before);
            assert_eq!(recovering.limit_event_mark(), mark);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Repeated recovery and healthy retry share a caller frame.
    fn selection_mapped_alias_wrapped_recovery_stays_out_of_alias_and_scratch_caches() {
        let template = parse_source_file(concat!(
            "type Selection<S, K extends keyof S> = { [P in K]: S[P] }; ",
            "declare function select<O, K extends string>(object: O, key: K): ",
            "Selection<any, `pre-${K}`>;",
        ));
        let values = parse_source_file("const object = { a: 'a', b: 'b' };");
        for stored in [false, true] {
            let mut fixture = selection_instantiation_fixture(&template, &values);
            let sources = fixture.parameters;
            let store = fixture.context.store_mut_for_test();
            let any = store.intrinsic_bootstrap().unwrap().any_type;
            let error_type = store.intrinsic_bootstrap().unwrap().error_type;
            let b = store.regular_string_literal_type("b".into()).unwrap();
            let targets = [fixture.fresh, b];
            let mapper = store
                .new_type_mapper(sources.to_vec(), targets.to_vec())
                .unwrap();
            let projection = supported_mapped_alias_projection(store, fixture.returned, None)
                .unwrap()
                .unwrap();
            assert_eq!(projection.arguments[0], any);
            let key_template = projection.arguments[1];
            let TypeData::TemplateLiteral(key) = store.type_payload(key_template).unwrap().data()
            else {
                panic!("the mapped argument must retain its source template");
            };
            assert_eq!(key.texts, ["pre-", ""]);
            assert_eq!(key.types, [sources[1]]);
            let texts = key.texts.clone();
            let mapping = if stored {
                InstantiationMapping::Stored(mapper)
            } else {
                InstantiationMapping::Vector {
                    sources: &sources,
                    targets: &targets,
                }
            };
            let retained = InstantiationCacheKey::Type {
                type_: sources[0],
                alias: InstantiationAliasCacheKey::None,
            };
            let retained_cache = HashMap::from([(retained, fixture.fresh)]);
            let mut session = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_depth: 5,
                    max_count: 50,
                },
                error_type,
            )
            .unwrap();
            session.depth = 3;
            session.count = 7;
            session.total_count = 11;
            session.active_mappers.push(ActiveMapperFrame {
                mapping: mapping.identity(),
                cache: retained_cache.clone(),
            });
            let alias_links = store.type_alias_links(fixture.alias).unwrap().clone();
            let initial = deferred_intersection_store_state(store);
            let mut recovered_template = None;
            let mut recovered_state = None;
            for attempt in 0..2 {
                let mark = session.limit_event_mark();
                assert_eq!(
                    instantiate_type_with_alias(
                        store,
                        fixture.returned,
                        mapping,
                        None,
                        None,
                        &mut session,
                    ),
                    Ok(error_type)
                );
                assert!(session.limit_event_occurred_since(mark));
                assert_eq!(
                    (session.depth, session.query_count(), session.total_count()),
                    (3, 9 + 2 * attempt, 13 + 2 * attempt)
                );
                assert_eq!(session.active_mappers.len(), 1);
                assert_eq!(session.active_mappers[0].cache, retained_cache);
                let recovered = store
                    .cached_resolved_template_literal_type(&texts, &[error_type])
                    .unwrap()
                    .unwrap();
                assert_ne!(recovered, error_type);
                let TypeData::TemplateLiteral(recovered_key) =
                    store.type_payload(recovered).unwrap().data()
                else {
                    panic!("the inner recovery must retain its template wrapper");
                };
                assert_eq!(recovered_key.types, [error_type]);
                assert_eq!(store.type_alias_links(fixture.alias), Some(&alias_links));
                assert_eq!(
                    alias_links
                        .instantiations
                        .as_ref()
                        .unwrap()
                        .get(&type_alias_instantiation_cache_key(&[any, recovered], None)),
                    None
                );
                let state = deferred_intersection_store_state(store);
                assert_eq!(state.0[0], initial.0[0] + 1);
                assert_eq!(state.0[1..], initial.0[1..]);
                assert_eq!(state.1, initial.1);
                if let Some(previous) = recovered_template {
                    assert_eq!(recovered, previous);
                    assert_eq!(Some(state), recovered_state);
                }
                recovered_template = Some(recovered);
                recovered_state = Some(state);
            }
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    fixture.returned,
                    &sources,
                    &targets,
                    None,
                    None,
                ),
                Ok(None)
            );

            session.limits.max_depth = 50;
            let mark = session.limit_event_mark();
            let result = instantiate_type_with_alias(
                store,
                fixture.returned,
                mapping,
                None,
                None,
                &mut session,
            )
            .unwrap();
            assert_ne!(result, error_type);
            let expected_key = store.regular_string_literal_type("pre-b".into()).unwrap();
            let healthy = supported_mapped_alias_projection(store, result, None)
                .unwrap()
                .unwrap();
            assert_eq!(healthy.arguments, [any, expected_key]);
            assert_eq!(healthy.identity_arguments, healthy.arguments);
            assert_eq!(session.limit_event_mark(), mark);
            assert_eq!(session.depth, 3);
            assert_eq!(session.active_mappers.len(), 1);
            let healthy_state = deferred_intersection_store_state(store);
            let counters = (session.depth, session.query_count(), session.total_count());
            assert_eq!(
                instantiate_type_with_alias(
                    store,
                    fixture.returned,
                    mapping,
                    None,
                    None,
                    &mut session,
                ),
                Ok(result)
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    fixture.returned,
                    &sources,
                    &targets,
                    None,
                    None,
                ),
                Ok(Some(result))
            );
            assert_eq!(
                (session.depth, session.query_count(), session.total_count()),
                counters
            );
            assert_eq!(session.limit_event_mark(), mark);
            assert_eq!(deferred_intersection_store_state(store), healthy_state);
            assert!(
                store
                    .source_callable_type_query(fixture.signature)
                    .unwrap()
                    .is_exact(store)
            );
        }
    }

    fn assert_invalid_instantiation_cache_without_writes(
        store: &mut CanonicalTypeMapperStore,
        source: TypeId,
        sources: &[TypeId],
        targets: &[TypeId],
        alias: SemanticSymbolId,
    ) {
        let before = deferred_intersection_store_state(store);
        let links = store.type_alias_links(alias).unwrap().clone();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        for _ in 0..2 {
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    source,
                    sources,
                    targets,
                    None,
                    &mut session,
                ),
                Err(InstantiationError::InvalidType(source))
            );
            assert_eq!(
                cached_instantiation_with_vector(store, source, sources, targets, None, None),
                Err(InstantiationError::InvalidType(source))
            );
            assert_eq!(store.type_alias_links(alias), Some(&links));
            assert_eq!(deferred_intersection_store_state(store), before);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each changed cache is restored before the next control.
    fn generic_keyof_and_selection_alias_reject_changed_source_and_result_caches() {
        let template = parse_source_file(SELECTION_INSTANTIATION_SOURCE);
        let values = parse_source_file("const object = { a: 'a', b: 'b' };");
        let mut fixture = selection_instantiation_fixture(&template, &values);
        let sources = fixture.parameters;
        let store = fixture.context.store_mut_for_test();
        let b = store.regular_string_literal_type("b".into()).unwrap();
        let targets = [fixture.fresh, b];
        let plan = plan_nongeneric_keyof_type(store, sources[0]).unwrap();
        let index = resolve_nongeneric_keyof_type(store, &plan).unwrap();
        let owner = cached_ordinary_type_parameter_owner(store, sources[0]).unwrap();
        assert!(store.set_type_symbol(index, Some(owner)));
        assert_invalid_instantiation_cache_without_writes(
            store,
            index,
            &sources,
            &targets,
            fixture.alias,
        );
        assert!(store.set_type_symbol(index, None));
        assert_eq!(
            validate_generic_keyof_index_type(store, index),
            Ok(sources[0])
        );

        let object_owner = store.type_payload(fixture.fresh).unwrap().symbol();
        assert!(store.set_type_symbol(fixture.fresh, Some(owner)));
        assert_invalid_instantiation_cache_without_writes(
            store,
            fixture.fresh,
            &sources,
            &targets,
            fixture.alias,
        );
        assert!(store.set_type_symbol(fixture.fresh, object_owner));
        assert_eq!(
            is_concrete_source_object_literal(store, fixture.fresh, None),
            Ok(true)
        );

        let projection = supported_mapped_alias_projection(store, fixture.returned, None)
            .unwrap()
            .unwrap();
        let TypeData::Mapped(mapped) = store.type_payload(fixture.returned).unwrap().data() else {
            panic!("the source return must remain mapped");
        };
        let target = mapped.object.target;
        let substitution = mapped.object.mapper;
        let wrong_mapper = store
            .new_type_mapper(sources.to_vec(), targets.to_vec())
            .unwrap();
        assert!(store.set_object_target_and_mapper(fixture.returned, target, Some(wrong_mapper)));
        assert_invalid_instantiation_cache_without_writes(
            store,
            fixture.returned,
            &sources,
            &targets,
            fixture.alias,
        );
        assert!(store.set_object_target_and_mapper(fixture.returned, target, substitution));

        let identity = store
            .type_payload(fixture.returned)
            .unwrap()
            .alias()
            .unwrap();
        assert!(store.set_type_alias_arguments(identity, Some(targets.to_vec())));
        assert_invalid_instantiation_cache_without_writes(
            store,
            fixture.returned,
            &sources,
            &targets,
            fixture.alias,
        );
        assert!(store.set_type_alias_arguments(identity, Some(sources.to_vec())));
        assert_eq!(
            supported_mapped_alias_projection(store, fixture.returned, None),
            Ok(Some(projection.clone()))
        );

        let TypeData::Mapped(declared) =
            store.type_payload(projection.declared_type).unwrap().data()
        else {
            panic!("the selection declaration must keep its mapped template");
        };
        let declared = declared.clone();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        assert!(store.set_mapped_type_resolution(
            projection.declared_type,
            declared.declaration,
            declared.type_parameter,
            declared.constraint_type,
            declared.name_type,
            Some(number),
            declared.modifiers_type,
            declared.resolved_apparent_type,
            declared.contains_error,
        ));
        assert_invalid_instantiation_cache_without_writes(
            store,
            fixture.returned,
            &sources,
            &targets,
            fixture.alias,
        );
        assert!(store.set_mapped_type_resolution(
            projection.declared_type,
            declared.declaration,
            declared.type_parameter,
            declared.constraint_type,
            declared.name_type,
            declared.template_type,
            declared.modifiers_type,
            declared.resolved_apparent_type,
            declared.contains_error,
        ));

        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let result = instantiate_type_with_vector_and_session(
            store,
            fixture.returned,
            &sources,
            &targets,
            None,
            &mut session,
        )
        .unwrap();
        let original = store.type_alias_links(fixture.alias).unwrap().clone();
        let mut changed = original.clone();
        assert_eq!(
            changed
                .instantiations
                .as_mut()
                .unwrap()
                .insert(type_alias_instantiation_cache_key(&targets, None), number),
            Some(result)
        );
        assert!(store.set_type_alias_links(fixture.alias, changed));
        assert_invalid_instantiation_cache_without_writes(
            store,
            fixture.returned,
            &sources,
            &targets,
            fixture.alias,
        );
        assert!(store.set_type_alias_links(fixture.alias, original));
        assert_eq!(
            cached_instantiation_with_vector(
                store,
                fixture.returned,
                &sources,
                &targets,
                None,
                None,
            ),
            Ok(Some(result))
        );
        assert!(
            store
                .source_callable_type_query(fixture.signature)
                .unwrap()
                .is_exact(store)
        );
    }

    const NON_NULLABLE_CONDITIONAL_SOURCE: &str = concat!(
        "type Select<Value> = Value extends string ? number : boolean;\n",
        "type Forward<Other> = Select<Other>;\n",
    );

    mod source_conditional_signature_demand_tests {
        use super::*;
        use crate::semantic::{RelationUnavailable, SourceCheckError, TypeNodeLinks};
        use ts_binder::CanonicalNameResolverOptions;

        const FILE: FileId = FileId::new(8_587);

        struct Prepared<'a> {
            context: CanonicalCheckerContext<'a>,
            globals: CanonicalGlobalTypes,
            method: SemanticSymbolId,
            receiver: TypeId,
            template: TypeId,
            conditional: NodeRef,
        }

        #[allow(clippy::too_many_lines)] // Build the real declaration and receiver before measuring demand.
        fn prepare(parsed: &ParseResult) -> Prepared<'_> {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    FILE,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/conditional-signature.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, FILE)
                .unwrap();
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                vec![(FILE, &parsed.arena)],
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            let bound = context.file(FILE).unwrap().1.clone();
            let node = |kind| {
                parsed
                    .arena
                    .iter()
                    .find_map(|(id, record)| {
                        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), FILE, id))
                    })
                    .unwrap()
            };
            let method = bound.symbol(node(SyntaxKind::MethodSignature)).unwrap();
            let annotation = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                        return None;
                    };
                    (name.text == "receiver").then_some(NodeRef::new(
                        parsed.arena.id(),
                        FILE,
                        variable.type_?,
                    ))
                })
                .unwrap();
            let conditional = node(SyntaxKind::ConditionalType);
            let globals = context.global_types().clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let mut query = CanonicalTypeQuery::new_with_global_types_and_session(
                context.store_mut_for_test(),
                &host,
                &globals,
                crate::semantic::type_nodes::CanonicalTypeQueryOptions::default(),
                &mut session,
                &mut diagnostics,
            )
            .unwrap();
            query.get_type_of_interface_method(method).unwrap();
            let receiver = query.get_type_from_type_node(annotation).unwrap();
            let template = context
                .store()
                .type_node_links(conditional)
                .unwrap()
                .resolved_type
                .unwrap();
            assert!(conditional_signature_projection(context.store(), template).is_ok());
            assert!(diagnostics.is_empty());
            Prepared {
                context,
                globals,
                method,
                receiver,
                template,
                conditional,
            }
        }

        fn demand(
            fixture: &mut Prepared<'_>,
            parsed: &ParseResult,
            session: &mut InstantiationSession,
        ) -> Result<TypeId, SourceCheckError> {
            let bound = fixture.context.file(FILE).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let result = CanonicalTypeQuery::new_with_global_types_and_session(
                fixture.context.store_mut_for_test(),
                &host,
                &fixture.globals,
                crate::semantic::type_nodes::CanonicalTypeQueryOptions::default(),
                session,
                &mut diagnostics,
            )?
            .get_type_of_instantiated_interface_method(fixture.receiver, fixture.method);
            assert!(diagnostics.is_empty());
            result
        }

        fn demand_proxy(
            fixture: &mut Prepared<'_>,
            parsed: &ParseResult,
            property: SemanticSymbolId,
            session: &mut InstantiationSession,
        ) -> Result<TypeId, SourceCheckError> {
            let bound = fixture.context.file(FILE).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let result = CanonicalTypeQuery::new_with_global_types_and_session(
                fixture.context.store_mut_for_test(),
                &host,
                &fixture.globals,
                crate::semantic::type_nodes::CanonicalTypeQueryOptions::default(),
                session,
                &mut diagnostics,
            )?
            .get_type_of_instantiated_interface_property(fixture.receiver, property);
            assert!(diagnostics.is_empty());
            if let Ok(callable) = result {
                let signature = signature(fixture.context.store(), callable);
                let expected = returned(fixture.context.store(), callable);
                let state = format!("{:?}", fixture.context.store());
                let work = budget(session);
                assert_eq!(
                    CanonicalTypeQuery::new_with_global_types_and_session(
                        fixture.context.store_mut_for_test(),
                        &host,
                        &fixture.globals,
                        crate::semantic::type_nodes::CanonicalTypeQueryOptions::default(),
                        session,
                        &mut diagnostics,
                    )?
                    .get_return_type_of_signature(signature),
                    Ok(expected)
                );
                assert!(diagnostics.is_empty());
                assert_eq!(budget(session), work);
                assert_eq!(format!("{:?}", fixture.context.store()), state);
            }
            result
        }

        fn signature(store: &CanonicalTypeMapperStore, callable: TypeId) -> SignatureId {
            let signatures = store
                .type_payload(callable)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .signatures
                .as_deref()
                .unwrap();
            assert_eq!(signatures.len(), 1);
            signatures[0]
        }

        fn returned(store: &CanonicalTypeMapperStore, callable: TypeId) -> TypeId {
            store
                .signature(signature(store, callable))
                .unwrap()
                .resolved_return_type()
                .unwrap()
        }

        fn budget(session: &InstantiationSession) -> (usize, usize, u64, usize, usize) {
            (
                session.query_count(),
                session.total_count(),
                session.limit_event_count(),
                session.depth,
                session.active_mappers.len(),
            )
        }

        #[test]
        #[allow(clippy::too_many_lines)] // Compare fail-fast and recovery with the same spent caller budget.
        fn source_conditional_signature_demand_keeps_spent_limits_and_recovery() {
            let parsed = parse_source_file(concat!(
                "interface Array<T> {} interface ReadonlyArray<T> {} ",
                "interface Choice<T> { choose(): T extends any ? string : number; } ",
                "declare const receiver: Choice<any>;",
            ));
            for recovering in [false, true] {
                let mut fixture = prepare(&parsed);
                let bootstrap = fixture.context.store().intrinsic_bootstrap().unwrap();
                let (any, error_type, string) = (
                    bootstrap.any_type,
                    bootstrap.error_type,
                    bootstrap.string_type,
                );
                let parameter =
                    conditional_signature_projection(fixture.context.store(), fixture.template)
                        .unwrap()
                        .0
                        .parameters()[0];
                let limits = InstantiationLimits {
                    max_count: 1,
                    ..InstantiationLimits::default()
                };
                let mut session = if recovering {
                    InstantiationSession::new_recovering(
                        fixture.context.store(),
                        limits,
                        error_type,
                    )
                    .unwrap()
                } else {
                    InstantiationSession::new(limits)
                };
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        fixture.context.store_mut_for_test(),
                        parameter,
                        &[parameter],
                        &[any],
                        Some(CanonicalArrayTargets::from_global_types(&fixture.globals)),
                        &mut session,
                    ),
                    Ok(any)
                );
                assert_eq!(budget(&session), (1, 1, 0, 0, 0));
                let TypeData::Conditional(data) = fixture
                    .context
                    .store()
                    .type_payload(fixture.template)
                    .unwrap()
                    .data()
                else {
                    unreachable!()
                };
                let root = data.root;
                let cache = fixture
                    .context
                    .store()
                    .conditional_root(root)
                    .unwrap()
                    .instantiations()
                    .clone();
                let result = demand(&mut fixture, &parsed, &mut session);
                assert_eq!(budget(&session), (1, 1, 1, 0, 0));
                assert_eq!(
                    fixture
                        .context
                        .store()
                        .conditional_root(root)
                        .unwrap()
                        .instantiations(),
                    &cache
                );
                let callable = if recovering {
                    let callable = result.unwrap();
                    assert_eq!(returned(fixture.context.store(), callable), error_type);
                    assert!(
                        fixture
                            .context
                            .store()
                            .published_interface_method_recovery(callable)
                            .is_some()
                    );
                    callable
                } else {
                    assert_eq!(
                        result,
                        Err(SourceCheckError::RelationUnavailable(
                            RelationUnavailable::UnionValidationCapacity(fixture.template)
                        ))
                    );
                    assert_eq!(
                        fixture
                            .context
                            .store()
                            .published_interface_method_origin_len(),
                        0
                    );
                    assert_eq!(
                        fixture
                            .context
                            .store()
                            .published_interface_method_recovery_len(),
                        0
                    );
                    let mut fresh = InstantiationSession::new(InstantiationLimits::default());
                    let callable = demand(&mut fixture, &parsed, &mut fresh).unwrap();
                    assert_eq!(returned(fixture.context.store(), callable), string);
                    assert!(fresh.total_count() > 0);
                    assert_eq!(
                        (
                            fresh.depth,
                            fresh.active_mappers.len(),
                            fresh.limit_event_count()
                        ),
                        (0, 0, 0)
                    );
                    callable
                };
                let before = format!("{:?}", fixture.context.store());
                let mut warm = InstantiationSession::new(InstantiationLimits {
                    max_count: 0,
                    ..InstantiationLimits::default()
                });
                for _ in 0..2 {
                    assert_eq!(demand(&mut fixture, &parsed, &mut warm), Ok(callable));
                    assert_eq!(budget(&warm), (0, 0, 0, 0, 0));
                    assert_eq!(format!("{:?}", fixture.context.store()), before);
                }
            }
        }

        #[test]
        #[allow(clippy::too_many_lines)] // The real proxy keeps its mapper, failed demand, recovery, and warm value.
        fn source_conditional_signature_demand_keeps_resolved_proxy_limits_and_identity() {
            let parsed = parse_source_file(concat!(
                "interface Array<T> {} interface ReadonlyArray<T> {} ",
                "interface Choice<T> { choose(): T extends any ? string : number; } ",
                "declare const receiver: Choice<any>;",
            ));
            for recovering in [false, true] {
                let mut fixture = prepare(&parsed);
                fixture.context.check_source_file(FILE).unwrap();
                assert!(fixture.context.diagnostics().is_empty());
                let targets = CanonicalArrayTargets::from_global_types(&fixture.globals);
                let members = crate::semantic::instantiated_members::resolve_members_with_array_targets_and_session(
                    fixture.context.store_mut_for_test(),
                    fixture.receiver,
                    Some(targets),
                    &mut InstantiationSession::new(InstantiationLimits::default()),
                )
                .unwrap();
                let [property] = members.properties() else {
                    panic!("the real receiver must have one method proxy")
                };
                let property = *property;
                let proxy = fixture.context.store().symbol(property).unwrap();
                assert!(
                    proxy
                        .flags()
                        .contains(SymbolFlags::TRANSIENT | SymbolFlags::METHOD)
                );
                assert!(proxy.check_flags().contains(CheckFlags::INSTANTIATED));
                let links = fixture
                    .context
                    .store()
                    .value_symbol_links(property)
                    .unwrap()
                    .clone();
                assert_eq!(links.target, Some(fixture.method));
                assert!(links.mapper.is_some());
                assert!(links.resolved_type.is_none());
                let bootstrap = fixture.context.store().intrinsic_bootstrap().unwrap();
                let (any, error_type, string, number) = (
                    bootstrap.any_type,
                    bootstrap.error_type,
                    bootstrap.string_type,
                    bootstrap.number_type,
                );
                let projection =
                    conditional_signature_projection(fixture.context.store(), fixture.template)
                        .unwrap()
                        .0;
                let TypeData::Conditional(data) = fixture
                    .context
                    .store()
                    .type_payload(fixture.template)
                    .unwrap()
                    .data()
                else {
                    unreachable!()
                };
                let root = data.root;
                let parameter = projection.parameters()[0];
                let root_cache = fixture
                    .context
                    .store()
                    .conditional_root(root)
                    .unwrap()
                    .instantiations()
                    .clone();
                let limits = InstantiationLimits {
                    max_count: 1,
                    ..InstantiationLimits::default()
                };
                let mut session = if recovering {
                    InstantiationSession::new_recovering(
                        fixture.context.store(),
                        limits,
                        error_type,
                    )
                    .unwrap()
                } else {
                    InstantiationSession::new(limits)
                };
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        fixture.context.store_mut_for_test(),
                        parameter,
                        &[parameter],
                        &[any],
                        Some(targets),
                        &mut session,
                    ),
                    Ok(any)
                );
                assert_eq!(budget(&session), (1, 1, 0, 0, 0));
                let result = demand_proxy(&mut fixture, &parsed, property, &mut session);
                assert_eq!(budget(&session), (1, 1, 1, 0, 0));
                assert_eq!(
                    fixture
                        .context
                        .store()
                        .conditional_root(root)
                        .unwrap()
                        .instantiations(),
                    &root_cache
                );
                let callable = if recovering {
                    let callable = result.unwrap();
                    assert_eq!(returned(fixture.context.store(), callable), error_type);
                    assert!(
                        fixture
                            .context
                            .store()
                            .instantiated_property_recovery(property)
                            .is_some()
                    );
                    callable
                } else {
                    assert_eq!(
                        result,
                        Err(SourceCheckError::RelationUnavailable(
                            RelationUnavailable::UnionValidationCapacity(fixture.template)
                        ))
                    );
                    assert_eq!(
                        fixture.context.store().value_symbol_links(property),
                        Some(&links)
                    );
                    assert!(
                        fixture
                            .context
                            .store()
                            .instantiated_property_recovery(property)
                            .is_none()
                    );
                    let mut fresh = InstantiationSession::new(InstantiationLimits::default());
                    let callable =
                        demand_proxy(&mut fixture, &parsed, property, &mut fresh).unwrap();
                    assert_eq!(returned(fixture.context.store(), callable), string);
                    assert!(fresh.total_count() > 0);
                    assert_eq!(
                        (
                            fresh.depth,
                            fresh.active_mappers.len(),
                            fresh.limit_event_count()
                        ),
                        (0, 0, 0)
                    );
                    callable
                };
                assert_eq!(
                    fixture.context.store().value_symbol_links(property),
                    Some(&crate::semantic::ValueSymbolLinks {
                        resolved_type: Some(callable),
                        ..links
                    })
                );
                let copied = signature(fixture.context.store(), callable);
                let returned = returned(fixture.context.store(), callable);
                assert!(
                    fixture
                        .context
                        .store_mut_for_test()
                        .set_signature_resolved_return_type(copied, Some(number))
                );
                let damaged = format!("{:?}", fixture.context.store());
                assert!(crate::semantic::instantiated_members::instantiated_interface_method_signature_return(
                    fixture.context.store(),
                    copied,
                    Some(targets),
                )
                .is_err());
                let mut warm = InstantiationSession::new(InstantiationLimits {
                    max_count: 0,
                    ..InstantiationLimits::default()
                });
                assert_eq!(
                    demand_proxy(&mut fixture, &parsed, property, &mut warm),
                    Err(SourceCheckError::RelationUnavailable(
                        RelationUnavailable::InvalidStructuredMembers(fixture.receiver)
                    ))
                );
                assert_eq!(budget(&warm), (0, 0, 0, 0, 0));
                assert_eq!(format!("{:?}", fixture.context.store()), damaged);
                assert!(
                    fixture
                        .context
                        .store_mut_for_test()
                        .set_signature_resolved_return_type(copied, Some(returned))
                );
                let restored = format!("{:?}", fixture.context.store());
                for _ in 0..2 {
                    assert_eq!(
                        demand_proxy(&mut fixture, &parsed, property, &mut warm),
                        Ok(callable)
                    );
                    assert_eq!(budget(&warm), (0, 0, 0, 0, 0));
                    assert_eq!(format!("{:?}", fixture.context.store()), restored);
                }
            }
        }

        #[test]
        #[allow(clippy::too_many_lines)] // Damage one cache or owner, replay twice, and restore the original.
        fn source_conditional_signature_demand_rejects_and_restores_warm_damage() {
            let parsed = parse_source_file(concat!(
                "interface Array<T> {} interface ReadonlyArray<T> {} ",
                "interface Choice<T> { choose<S>(value: S): T extends any ? Choice<any> : Choice<S>; } ",
                "interface Other<T> {} ",
                "declare const receiver: Choice<any>;",
            ));
            for mutation in 0..4 {
                let mut fixture = prepare(&parsed);
                let mut session = InstantiationSession::new(InstantiationLimits::default());
                let callable = demand(&mut fixture, &parsed, &mut session).unwrap();
                assert_eq!(
                    returned(fixture.context.store(), callable),
                    fixture.receiver
                );
                let copied = signature(fixture.context.store(), callable);
                let signature_record = fixture.context.store().signature(copied).unwrap();
                let original = signature_record.target();
                let mapper = signature_record.mapper();
                let links = fixture
                    .context
                    .store()
                    .type_node_links(fixture.conditional)
                    .unwrap()
                    .clone();
                let number = fixture
                    .context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .number_type;
                let parameters =
                    conditional_signature_projection(fixture.context.store(), fixture.template)
                        .unwrap()
                        .0
                        .parameters()
                        .to_vec();
                let (owner, _) = fixture
                    .context
                    .store()
                    .authenticated_interface_method_owner(fixture.method)
                    .unwrap();
                let declarations = fixture
                    .context
                    .store()
                    .symbol(owner)
                    .unwrap()
                    .declarations()
                    .unwrap()
                    .to_vec();
                let other = parsed
                    .arena
                    .iter()
                    .find_map(|(id, record)| {
                        let NodeData::InterfaceDeclaration(interface) = &record.data else {
                            return None;
                        };
                        let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data
                        else {
                            return None;
                        };
                        (name.text == "Other").then_some(NodeRef::new(parsed.arena.id(), FILE, id))
                    })
                    .unwrap();
                let store = fixture.context.store_mut_for_test();
                match mutation {
                    0 => assert!(store.set_type_node_links(
                        fixture.conditional,
                        TypeNodeLinks {
                            outer_type_parameters: Some(Vec::new()),
                            ..links.clone()
                        }
                    )),
                    1 => {
                        let wrong = store
                            .new_type_mapper(parameters.clone(), vec![number; parameters.len()])
                            .unwrap();
                        assert!(store.set_signature_target_and_mapper(
                            copied,
                            original,
                            Some(wrong)
                        ));
                    }
                    2 => assert!(store.set_signature_resolved_return_type(copied, Some(number))),
                    _ => assert!(store.set_symbol_declarations(owner, Some(vec![other]), None)),
                }
                let before = format!("{:?}", fixture.context.store());
                let work = budget(&session);
                for _ in 0..2 {
                    assert_eq!(
                        demand(&mut fixture, &parsed, &mut session),
                        Err(SourceCheckError::RelationUnavailable(
                            RelationUnavailable::InvalidStructuredMembers(fixture.receiver)
                        ))
                    );
                    assert_eq!(format!("{:?}", fixture.context.store()), before);
                    assert_eq!(budget(&session), work);
                }
                let store = fixture.context.store_mut_for_test();
                assert!(store.set_type_node_links(fixture.conditional, links));
                assert!(store.set_signature_target_and_mapper(copied, original, mapper));
                assert!(store.set_signature_resolved_return_type(copied, Some(fixture.receiver)));
                assert!(store.set_symbol_declarations(owner, Some(declarations), None));
                let restored = format!("{:?}", fixture.context.store());
                assert_eq!(demand(&mut fixture, &parsed, &mut session), Ok(callable));
                assert_eq!(format!("{:?}", fixture.context.store()), restored);
                assert_eq!(budget(&session), work);
            }
        }

        #[test]
        #[allow(clippy::too_many_lines)] // Check the remapped root and both untouched branch nodes together.
        fn source_conditional_signature_demand_keeps_generic_input_deferred() {
            let parsed = parse_source_file(concat!(
                "interface Array<T> {} interface ReadonlyArray<T> {} ",
                "interface Choice<T> { choose<S>(value: S): T extends any ? Choice<any> : Choice<S>; } ",
                "declare const receiver: Choice<any>; ",
                "declare function hold<U>(value: Choice<U>): void;",
            ));
            let mut fixture = prepare(&parsed);
            let bound = fixture.context.file(FILE).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let annotation = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::FunctionDeclaration(function) = &record.data else {
                        return None;
                    };
                    let NodeData::ParameterDeclaration(parameter) =
                        &parsed.arena.get(function.parameters.nodes[0])?.data
                    else {
                        return None;
                    };
                    Some(NodeRef::new(parsed.arena.id(), FILE, parameter.type_?))
                })
                .unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            fixture.receiver = CanonicalTypeQuery::new_with_global_types(
                fixture.context.store_mut_for_test(),
                &host,
                &fixture.globals,
                crate::semantic::type_nodes::CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(annotation)
            .unwrap();
            let TypeData::TypeReference(receiver) = fixture
                .context
                .store()
                .type_payload(fixture.receiver)
                .unwrap()
                .data()
            else {
                unreachable!()
            };
            let parameter = receiver.resolved_type_arguments.as_deref().unwrap()[0];
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let callable = demand(&mut fixture, &parsed, &mut session).unwrap();
            let result = returned(fixture.context.store(), callable);
            let TypeData::Conditional(data) =
                fixture.context.store().type_payload(result).unwrap().data()
            else {
                panic!("a generic method result must stay deferred")
            };
            assert_eq!(data.check_type, parameter);
            assert!(data.resolved_true_type.is_none());
            assert!(data.resolved_false_type.is_none());
            let NodeData::ConditionalTypeNode(source) =
                &parsed.arena.get(fixture.conditional.node).unwrap().data
            else {
                unreachable!()
            };
            for branch in [source.true_type, source.false_type] {
                assert!(
                    fixture
                        .context
                        .store()
                        .type_node_links(NodeRef::new(parsed.arena.id(), FILE, branch))
                        .and_then(|links| links.resolved_type)
                        .is_none()
                );
            }
            let before = format!("{:?}", fixture.context.store());
            let work = budget(&session);
            assert_eq!(demand(&mut fixture, &parsed, &mut session), Ok(callable));
            assert_eq!(format!("{:?}", fixture.context.store()), before);
            assert_eq!(budget(&session), work);
            assert!(diagnostics.is_empty());
        }
    }

    struct NonNullableConditionalFixture<'arena> {
        context: CanonicalCheckerContext<'arena>,
        source: TypeId,
        parameter: TypeId,
        argument: TypeId,
        argument_parameter: TypeId,
        alias: SemanticSymbolId,
    }

    fn non_nullable_conditional_fixture<'arena>(
        library: &'arena ParseResult,
        source: &'arena ParseResult,
        strict_null_checks: bool,
    ) -> NonNullableConditionalFixture<'arena> {
        let library_file = FileId::new(8_554);
        let source_file = FileId::new(8_555);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path, default_library) in [
            (library, library_file, "\"/lib.non-nullable.d.ts\"", true),
            (source, source_file, "\"/conditional-argument.ts\"", false),
        ] {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        default_library,
                        default_library,
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
            vec![(library_file, &library.arena), (source_file, &source.arena)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let [alias, forward] =
            [(library_file, "NonNullable"), (source_file, "Forward")].map(|(file, name)| {
                let bound = context.file(file).unwrap().1;
                let locals = bound.locals(bound.source_file()).unwrap();
                context
                    .store()
                    .symbol_table(locals)
                    .unwrap()
                    .get_source(name)
                    .unwrap()
            });
        let source = context.get_declared_type_of_symbol(alias).unwrap();
        let argument = context.get_declared_type_of_symbol(forward).unwrap();
        let [parameter, argument_parameter] = [alias, forward].map(|symbol| {
            let parameters = context
                .store()
                .type_alias_links(symbol)
                .unwrap()
                .type_parameters
                .as_deref()
                .unwrap();
            assert_eq!(parameters.len(), 1);
            parameters[0]
        });
        assert!(conditional_alias_projection(context.store(), argument).is_ok());
        let TypeData::Conditional(data) = context.store().type_payload(argument).unwrap().data()
        else {
            panic!("the source query must retain its generic conditional")
        };
        assert_eq!(data.check_type, argument_parameter);
        assert!(data.mapper.is_some());
        NonNullableConditionalFixture {
            context,
            source,
            parameter,
            argument,
            argument_parameter,
            alias,
        }
    }

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn source_alias_instantiation_fixture(
        source: &str,
        names: &[&str],
    ) -> (CanonicalTypeMapperStore, Vec<TypeId>) {
        use crate::semantic::{
            CanonicalCheckerDiagnostics,
            production::GlobalMergeCompletion,
            type_nodes::{CanonicalTypeQuery, CanonicalTypeQueryOptions},
        };
        use ts_binder::CanonicalNameResolverOptions;

        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(8_561);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/inline-object-mapping.ts\""),
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
        let globals = store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap()
            .globals;
        let locals = bound.locals(bound.source_file()).unwrap();
        let table = store.symbol_table(locals).unwrap();
        let declarations = table.iter().map(|(_, symbol)| symbol).collect::<Vec<_>>();
        let requested = names
            .iter()
            .map(|name| table.get_source(name).unwrap())
            .collect::<Vec<_>>();
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
        let types = requested
            .into_iter()
            .map(|symbol| query.get_declared_type_of_symbol(symbol).unwrap())
            .collect::<Vec<_>>();
        assert!(diagnostics.is_empty());
        (store, types)
    }

    fn inline_object_instantiation_fixture() -> (
        CanonicalTypeMapperStore,
        InlinePropertyObjectProjection,
        Vec<TypeId>,
    ) {
        let (store, aliases) = source_alias_instantiation_fixture(
            concat!(
                "type Left<T> = { left: T };\n",
                "type Inline<T, U> = { first: T; second: U } & Left<T>;\n",
                "type Other<T, U> = { first: T; second: U };\n",
            ),
            &["Inline", "Other"],
        );
        let parts = store
            .validate_deferred_intersection_type(aliases[0])
            .unwrap();
        let inline = inline_property_object_projection(&store, parts.types[0])
            .unwrap()
            .unwrap();
        let other_parameters = property_object_alias_projection(&store, aliases[1])
            .unwrap()
            .unwrap()
            .parameters;
        (store, inline, other_parameters)
    }

    fn ordinary_intersection_instantiation_fixture()
    -> (CanonicalTypeMapperStore, TypeId, Vec<TypeId>, Vec<TypeId>) {
        let (store, inline, other_parameters) = inline_object_instantiation_fixture();
        let source = store
            .type_alias_links(inline.parameter_owner)
            .unwrap()
            .declared_type
            .unwrap();
        (store, source, inline.parameters, other_parameters)
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Compare real depth/count events, then reject changes to the retained proof.
    fn ordinary_intersection_receipts_keep_exact_constituent_and_alias_slot_events() {
        for (limits, child_events, alias_events) in [
            (
                InstantiationLimits {
                    max_depth: 2,
                    max_count: 100,
                },
                2,
                0,
            ),
            (
                InstantiationLimits {
                    max_depth: 100,
                    max_count: 4,
                },
                1,
                1,
            ),
        ] {
            let (mut store, source, parameters, _) = ordinary_intersection_instantiation_fixture();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let arguments = [bootstrap.string_type, bootstrap.number_type];
            let error = bootstrap.error_type;
            let mut session = InstantiationSession::new_recovering(&store, limits, error).unwrap();
            let (result, receipt) =
                instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                    &mut store,
                    source,
                    &parameters,
                    &arguments,
                    None,
                    None,
                    None,
                    &mut session,
                )
                .unwrap();
            let receipt = receipt.expect("the child limit has exact recovery evidence");
            assert_eq!(receipt.result(), result);
            assert_eq!(session.count, if alias_events == 0 { 5 } else { 4 });
            assert_eq!(session.limit_event_count(), child_events + 2 * alias_events);
            assert_eq!(session.depth, 0);
            assert!(session.active_mappers.is_empty());
            assert_eq!(
                receipt
                    .constituents
                    .iter()
                    .map(|slot| slot.events.after.0 - slot.events.before.0)
                    .collect::<Vec<_>>(),
                [0, child_events],
            );
            assert_eq!(
                receipt
                    .alias_arguments
                    .iter()
                    .map(|slot| slot.events.after.0 - slot.events.before.0)
                    .collect::<Vec<_>>(),
                [alias_events, alias_events],
            );
            assert!(receipt.alias_arguments.iter().all(|slot| !slot.inherited));
            let result_projection = store.validate_deferred_intersection_type(result).unwrap();
            assert_eq!(
                result_projection.alias_arguments,
                if alias_events == 0 {
                    arguments
                } else {
                    [error, error]
                },
            );
            let inline = inline_property_object_projection(&store, result_projection.types[0])
                .unwrap()
                .unwrap();
            assert_eq!(inline.arguments, arguments);
            assert!(store.type_payload(inline.type_).unwrap().alias().is_none());
            let left = property_object_alias_projection(&store, result_projection.types[1])
                .unwrap()
                .unwrap();
            assert_eq!(
                left.arguments,
                [if alias_events == 0 {
                    error
                } else {
                    arguments[0]
                }],
            );
            assert_eq!(left.identity_arguments, [error]);
            let child = store.property_object_alias_recovery(left.type_).unwrap();
            assert_eq!(child.physical_slot_recovered(0), alias_events == 0);
            assert!(child.identity_slot_recovered(0));
            assert_eq!(
                cached_instantiation_with_vector(
                    &store,
                    source,
                    &parameters,
                    &arguments,
                    None,
                    None,
                ),
                Ok(None),
            );

            let mut normal_session = InstantiationSession::new(InstantiationLimits::default());
            let normal = instantiate_type_with_vector_and_session(
                &mut store,
                source,
                &parameters,
                &arguments,
                None,
                &mut normal_session,
            )
            .unwrap();
            assert_ne!(normal, result);
            assert_eq!(normal_session.count, 5);
            let warm = deferred_intersection_store_state(&store);
            for _ in 0..2 {
                assert_eq!(
                    receipt.matches_mapping_request(
                        &store,
                        source,
                        &parameters,
                        &arguments,
                        None,
                        None,
                    ),
                    Ok(true),
                );
                assert_eq!(
                    cached_instantiation_with_vector(
                        &store,
                        source,
                        &parameters,
                        &arguments,
                        None,
                        None,
                    ),
                    Ok(Some(normal)),
                );
                assert_eq!(deferred_intersection_store_state(&store), warm);
            }
            assert_eq!(
                receipt.matches_mapping_request(
                    &store,
                    source,
                    &parameters,
                    &[arguments[1], arguments[0]],
                    None,
                    None,
                ),
                Ok(false),
            );
            for mutation in 0..6 {
                let mut changed = receipt.clone();
                match mutation {
                    0 => changed.source_key.types.swap(0, 1),
                    1 => changed.result_key.alias_arguments[0] = parameters[0],
                    2 => changed.constituents.swap(0, 1),
                    3 => {
                        changed.constituents[1].events.after =
                            changed.constituents[1].events.before;
                    }
                    4 => changed.alias_arguments[0].source = parameters[1],
                    5 => changed.error_type = arguments[0],
                    _ => unreachable!(),
                }
                assert!(
                    changed
                        .matches_mapping_request(
                            &store,
                            source,
                            &parameters,
                            &arguments,
                            None,
                            None,
                        )
                        .is_err(),
                    "changed receipt field {mutation} must fail",
                );
                assert_eq!(deferred_intersection_store_state(&store), warm);
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // A nested inline limit and inherited inline slots use the same physical cache.
    fn ordinary_intersection_receipts_validate_inline_slot_recovery_and_inheritance() {
        let (mut store, source, parameters, other_parameters) =
            ordinary_intersection_instantiation_fixture();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let error = bootstrap.error_type;
        let intermediate =
            instantiate_type_with_vector(&mut store, source, &parameters, &other_parameters)
                .unwrap();
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 2,
                max_count: 100,
            },
            error,
        )
        .unwrap();
        let (result, receipt) =
            instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                &mut store,
                intermediate,
                &other_parameters,
                &arguments,
                None,
                None,
                None,
                &mut session,
            )
            .unwrap();
        let receipt = receipt.unwrap();
        assert_eq!(session.count, 5);
        assert_eq!(session.limit_event_count(), 4);
        assert_eq!(
            receipt
                .constituents
                .iter()
                .map(|slot| slot.events.after.0 - slot.events.before.0)
                .collect::<Vec<_>>(),
            [2, 2],
        );
        let parts = store.validate_deferred_intersection_type(result).unwrap();
        let inline = inline_property_object_projection(&store, parts.types[0])
            .unwrap()
            .unwrap();
        let recovery = store.inline_property_object_recovery(inline.type_).unwrap();
        assert_eq!(inline.arguments, [error, error]);
        assert!(recovery.physical_slot_recovered(0));
        assert!(recovery.physical_slot_recovered(1));
        assert_eq!(parts.alias_arguments, arguments);
        assert_eq!(
            receipt.matches_mapping_request(
                &store,
                intermediate,
                &other_parameters,
                &arguments,
                None,
                None,
            ),
            Ok(true),
        );

        let intermediate_parts = store
            .validate_deferred_intersection_type(intermediate)
            .unwrap();
        let mut partial_session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 100,
                max_count: 2,
            },
            error,
        )
        .unwrap();
        let partial_inline = instantiate_type_with_vector_and_session(
            &mut store,
            intermediate_parts.types[0],
            &other_parameters,
            &[other_parameters[0], arguments[1]],
            None,
            &mut partial_session,
        )
        .unwrap();
        assert_eq!(partial_session.limit_event_count(), 1);
        let inherited_source = instantiate_type_with_vector(
            &mut store,
            source,
            &parameters,
            &[other_parameters[0], error],
        )
        .unwrap();
        assert_eq!(
            store
                .validate_deferred_intersection_type(inherited_source)
                .unwrap()
                .types[0],
            partial_inline,
        );
        let mut next_session = InstantiationSession::new(InstantiationLimits::default());
        let (inherited_result, inherited_receipt) =
            instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                &mut store,
                inherited_source,
                &other_parameters[..1],
                &arguments[..1],
                None,
                None,
                None,
                &mut next_session,
            )
            .unwrap();
        let inherited_receipt = inherited_receipt.unwrap();
        let inherited_parts = store
            .validate_deferred_intersection_type(inherited_result)
            .unwrap();
        let inherited_inline = inline_property_object_projection(&store, inherited_parts.types[0])
            .unwrap()
            .unwrap();
        assert_eq!(inherited_inline.arguments, [arguments[0], error]);
        assert!(
            store
                .inline_property_object_recovery(inherited_inline.type_)
                .unwrap()
                .physical_slot_recovered(1),
        );
        assert_eq!(next_session.limit_event_count(), 0);
        assert!(inherited_receipt.inherited.is_none());
        assert!(
            inherited_receipt
                .alias_arguments
                .iter()
                .all(|slot| !slot.inherited)
        );
        let warm = deferred_intersection_store_state(&store);
        assert_eq!(
            inherited_receipt.matches_mapping_request(
                &store,
                inherited_source,
                &other_parameters[..1],
                &arguments[..1],
                None,
                None,
            ),
            Ok(true),
        );
        assert_eq!(deferred_intersection_store_state(&store), warm);
    }

    #[test]
    fn ordinary_intersection_receipts_retain_exact_outer_inherited_slots() {
        let (mut store, source, parameters, other_parameters) =
            ordinary_intersection_instantiation_fixture();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [other_parameters[0], bootstrap.number_type];
        let string = bootstrap.string_type;
        let error = bootstrap.error_type;
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 100,
                max_count: 4,
            },
            error,
        )
        .unwrap();
        let (intermediate, receipt) =
            instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                &mut store,
                source,
                &parameters,
                &arguments,
                None,
                None,
                None,
                &mut session,
            )
            .unwrap();
        let receipt = receipt.unwrap();
        assert_eq!(session.limit_event_count(), 3);
        assert!(
            receipt
                .alias_arguments
                .iter()
                .all(|slot| slot.events.occurred())
        );
        assert_eq!(
            store
                .validate_deferred_intersection_type(intermediate)
                .unwrap()
                .alias_arguments,
            [error, error],
        );
        let mut next_session = InstantiationSession::new(InstantiationLimits::default());
        let (result, next) = instantiate_ordinary_intersection_with_vector_and_alias_and_session(
            &mut store,
            intermediate,
            &other_parameters[..1],
            &[string],
            None,
            None,
            Some(&receipt),
            &mut next_session,
        )
        .unwrap();
        let next = next.unwrap();
        assert_eq!(next_session.limit_event_count(), 0);
        assert_eq!(next.inherited.as_deref(), Some(&receipt));
        assert!(
            next.alias_arguments
                .iter()
                .all(|slot| { slot.inherited && !slot.events.occurred() && slot.result == error })
        );
        let parts = store.validate_deferred_intersection_type(result).unwrap();
        assert_eq!(parts.alias_arguments, [error, error]);
        assert_eq!(
            inline_property_object_projection(&store, parts.types[0])
                .unwrap()
                .unwrap()
                .arguments,
            [string, arguments[1]],
        );
        let warm = deferred_intersection_store_state(&store);
        assert_eq!(
            next.matches_mapping_request(
                &store,
                intermediate,
                &other_parameters[..1],
                &[string],
                None,
                None,
            ),
            Ok(true),
        );
        for mutation in 0..3 {
            let mut changed = next.clone();
            match mutation {
                0 => changed.inherited = None,
                1 => changed.alias_arguments[0].inherited = false,
                2 => changed
                    .inherited
                    .as_mut()
                    .unwrap()
                    .result_key
                    .types
                    .swap(0, 1),
                _ => unreachable!(),
            }
            assert!(
                changed
                    .matches_mapping_request(
                        &store,
                        intermediate,
                        &other_parameters[..1],
                        &[string],
                        None,
                        None,
                    )
                    .is_err(),
            );
            assert_eq!(deferred_intersection_store_state(&store), warm);
        }
    }

    #[test]
    fn ordinary_intersection_receipts_do_not_map_borrowed_override_arguments() {
        let (mut store, types) = source_alias_instantiation_fixture(
            concat!(
                "type Left<T> = { left: T };\n",
                "type Inline<T, U> = { first: T; second: U } & Left<T>;\n",
                "type Other<T, U> = { first: T; second: U };\n",
            ),
            &["Inline", "Other"],
        );
        let source = types[0];
        let parts = store.validate_deferred_intersection_type(source).unwrap();
        let parameters = inline_property_object_projection(&store, parts.types[0])
            .unwrap()
            .unwrap()
            .parameters;
        let other = property_object_alias_projection(&store, types[1])
            .unwrap()
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let error = bootstrap.error_type;
        let alias = Some((other.identity_symbol, other.parameters.as_slice()));
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 100,
                max_count: 4,
            },
            error,
        )
        .unwrap();
        let (result, receipt) =
            instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                &mut store,
                source,
                &parameters,
                &arguments,
                None,
                alias,
                None,
                &mut session,
            )
            .unwrap();
        let receipt = receipt.unwrap();
        assert_eq!(session.count, 4);
        assert_eq!(session.limit_event_count(), 1);
        assert!(receipt.alias_arguments.is_empty());
        let parts = store.validate_deferred_intersection_type(result).unwrap();
        assert_eq!(parts.alias_symbol, Some(other.identity_symbol));
        assert_eq!(parts.alias_arguments, other.parameters);
        let warm = deferred_intersection_store_state(&store);
        assert_eq!(
            receipt.matches_mapping_request(&store, source, &parameters, &arguments, alias, None,),
            Ok(true),
        );
        assert_eq!(
            receipt.matches_mapping_request(
                &store,
                source,
                &parameters,
                &arguments,
                Some((other.identity_symbol, &arguments)),
                None,
            ),
            Ok(false),
        );
        assert_eq!(deferred_intersection_store_state(&store), warm);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Guards and scratch hits must precede extra checks of an inherited receipt.
    fn ordinary_intersection_receipts_preserve_guard_and_scratch_cache_order() {
        let (mut store, source, parameters, other_parameters) =
            ordinary_intersection_instantiation_fixture();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [other_parameters[0], bootstrap.number_type];
        let targets = [bootstrap.string_type];
        let error = bootstrap.error_type;
        let mut preparation = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 100,
                max_count: 4,
            },
            error,
        )
        .unwrap();
        let (intermediate, receipt) =
            instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                &mut store,
                source,
                &parameters,
                &arguments,
                None,
                None,
                None,
                &mut preparation,
            )
            .unwrap();
        let receipt = receipt.unwrap();
        let mut normal = InstantiationSession::new(InstantiationLimits::default());
        let (result, _) = instantiate_ordinary_intersection_with_vector_and_alias_and_session(
            &mut store,
            intermediate,
            &other_parameters[..1],
            &targets,
            None,
            None,
            Some(&receipt),
            &mut normal,
        )
        .unwrap();
        let key = instantiation_cache_key_for_input(&store, intermediate, None).unwrap();
        assert_eq!(
            store.intersection_types.remove(&receipt.source_key),
            Some(source)
        );
        assert_eq!(
            could_contain_installed_type_variables(&store, intermediate, None),
            Ok(true),
        );
        let before = deferred_intersection_store_state(&store);
        let mut scratch = InstantiationSession::new(InstantiationLimits {
            max_depth: 10,
            max_count: 5,
        });
        scratch.depth = 3;
        scratch.count = 4;
        scratch.total_count = 9;
        scratch.active_mappers.push(ActiveMapperFrame {
            mapping: InstantiationMapping::Vector {
                sources: &other_parameters[..1],
                targets: &targets,
            }
            .identity(),
            cache: HashMap::from([(key.clone(), result)]),
        });
        assert_eq!(
            instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                &mut store,
                intermediate,
                &other_parameters[..1],
                &targets,
                None,
                None,
                Some(&receipt),
                &mut scratch,
            ),
            Ok((result, None)),
        );
        assert_eq!(
            (scratch.depth, scratch.count, scratch.total_count),
            (3, 4, 9)
        );
        assert_eq!(scratch.limit_event_count(), 0);
        assert_eq!(deferred_intersection_store_state(&store), before);
        for limits in [
            InstantiationLimits {
                max_depth: 0,
                max_count: 100,
            },
            InstantiationLimits {
                max_depth: 100,
                max_count: 0,
            },
        ] {
            let mut failing = InstantiationSession::new(limits);
            let expected = if limits.max_depth == 0 {
                InstantiationError::DepthLimit { depth: 0, limit: 0 }
            } else {
                InstantiationError::CountLimit { count: 0, limit: 0 }
            };
            assert_eq!(
                instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                    &mut store,
                    intermediate,
                    &other_parameters[..1],
                    &targets,
                    None,
                    None,
                    Some(&receipt),
                    &mut failing,
                ),
                Err(expected),
            );
            let mut recovering =
                InstantiationSession::new_recovering(&store, limits, error).unwrap();
            recovering.active_mappers.push(ActiveMapperFrame {
                mapping: InstantiationMapping::Vector {
                    sources: &other_parameters[..1],
                    targets: &targets,
                }
                .identity(),
                cache: HashMap::from([(key.clone(), result)]),
            });
            assert_eq!(
                instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                    &mut store,
                    intermediate,
                    &other_parameters[..1],
                    &targets,
                    None,
                    None,
                    Some(&receipt),
                    &mut recovering,
                ),
                Ok((error, None)),
            );
            assert_eq!(recovering.count, 0);
            assert_eq!(recovering.limit_event_count(), 1);
            assert_eq!(recovering.active_mappers[0].cache.get(&key), Some(&result));
            assert_eq!(deferred_intersection_store_state(&store), before);
        }
        let mut active = InstantiationSession::new(InstantiationLimits::default());
        assert!(
            instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                &mut store,
                intermediate,
                &other_parameters[..1],
                &targets,
                None,
                None,
                Some(&receipt),
                &mut active,
            )
            .is_err(),
        );
        assert_eq!(active.count, 1);
        assert_eq!(active.depth, 0);
        assert!(active.active_mappers.is_empty());
        assert_eq!(deferred_intersection_store_state(&store), before);
        assert_eq!(
            store
                .intersection_types
                .insert(receipt.source_key.clone(), source),
            None
        );
        assert_eq!(
            receipt.matches_mapping_request(&store, source, &parameters, &arguments, None, None,),
            Ok(true),
        );
    }

    #[test]
    fn ordinary_intersection_receipts_reject_recovered_reference_arguments_and_collapses() {
        let mut fixture = deferred_generic_intersection_fixture();
        let error = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let sources = [fixture.props, fixture.element];
        let targets = [fixture.attributes_reference, fixture.string];
        let mut session = InstantiationSession::new_recovering(
            &fixture.store,
            InstantiationLimits {
                max_depth: 2,
                max_count: 100,
            },
            error,
        )
        .unwrap();
        assert_eq!(
            instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                &mut fixture.store,
                fixture.intersection,
                &sources,
                &targets,
                None,
                None,
                None,
                &mut session,
            ),
            Err(InstantiationError::UnsupportedType(fixture.class_reference)),
        );
        assert_eq!(session.count, 2);
        assert_eq!(session.limit_event_count(), 1);
        assert_eq!(session.depth, 0);
        assert!(session.active_mappers.is_empty());

        let (mut store, source, parameters, _) = ordinary_intersection_instantiation_fixture();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 1,
                max_count: 100,
            },
            bootstrap.error_type,
        )
        .unwrap();
        let parts = store.validate_deferred_intersection_type(source).unwrap();
        assert_eq!(
            instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                &mut store,
                source,
                &parameters,
                &arguments,
                None,
                None,
                None,
                &mut session,
            ),
            Err(InstantiationError::UnsupportedType(parts.types[0])),
        );
        assert_eq!(session.count, 1);
        assert_eq!(session.limit_event_count(), 1);
        assert_eq!(session.depth, 0);
        assert!(session.active_mappers.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // A nested recovered reference is unsupported with or without another recovered object slot.
    fn ordinary_intersection_receipts_reject_nested_recovered_reference_arguments() {
        for (limits, count, events, has_object_recovery) in [
            (
                InstantiationLimits {
                    max_depth: 3,
                    max_count: 100,
                },
                4,
                1,
                false,
            ),
            (
                InstantiationLimits {
                    max_depth: 100,
                    max_count: 3,
                },
                3,
                2,
                true,
            ),
        ] {
            let (mut store, types) = source_alias_instantiation_fixture(
                concat!(
                    "interface Generic<T> {}\n",
                    "type Closed = { closed: string };\n",
                    "type Packet<T, V> = { value: T; other: V } & Closed;\n",
                    "type Stage<U, V> = Packet<Generic<U>, V>;\n",
                ),
                &["Stage"],
            );
            let source = types[0];
            let parts = store.validate_deferred_intersection_type(source).unwrap();
            let owner = parts.alias_symbol.unwrap();
            let links = store.type_alias_links(owner).cloned().unwrap();
            let parameters = links.type_parameters.clone().unwrap();
            let inline = inline_property_object_projection(&store, parts.types[0])
                .unwrap()
                .unwrap();
            assert!(inline.mapper.is_some());
            let generic = validate_direct_generic_reference(&store, inline.arguments[0]).unwrap();
            assert_eq!(generic.type_arguments, [parameters[0]]);
            assert_eq!(inline.arguments[1], parameters[1]);
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let arguments = [bootstrap.string_type, bootstrap.number_type];
            let error = bootstrap.error_type;
            let mut session = InstantiationSession::new_recovering(&store, limits, error).unwrap();
            assert_eq!(
                instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                    &mut store,
                    source,
                    &parameters,
                    &arguments,
                    None,
                    None,
                    None,
                    &mut session,
                ),
                Err(InstantiationError::UnsupportedType(inline.type_)),
            );
            assert_eq!(session.count, count);
            assert_eq!(session.limit_event_count(), events);
            assert_eq!(session.depth, 0);
            assert!(session.active_mappers.is_empty());
            assert_eq!(store.type_alias_links(owner), Some(&links));
            let recovered_reference = store
                .relation_object_instantiation(generic.target, type_list_key(&[error]))
                .unwrap();
            let recovered_arguments = [
                recovered_reference,
                if has_object_recovery {
                    error
                } else {
                    arguments[1]
                },
            ];
            let partial = store
                .relation_object_instantiation(
                    inline.target,
                    type_alias_instantiation_cache_key(&recovered_arguments, None),
                )
                .unwrap();
            assert_eq!(
                store.inline_property_object_recovery(partial).is_some(),
                has_object_recovery,
            );
            if let Some(recovery) = store.inline_property_object_recovery(partial) {
                assert!(!recovery.physical_slot_recovered(0));
                assert!(recovery.physical_slot_recovered(1));
            }
            let mut normal = InstantiationSession::new(InstantiationLimits::default());
            let (result, receipt) =
                instantiate_ordinary_intersection_with_vector_and_alias_and_session(
                    &mut store,
                    source,
                    &parameters,
                    &arguments,
                    None,
                    None,
                    None,
                    &mut normal,
                )
                .unwrap();
            assert!(receipt.is_none());
            assert_eq!(normal.limit_event_count(), 0);
            assert_eq!(
                cached_instantiation_with_vector(
                    &store,
                    source,
                    &parameters,
                    &arguments,
                    None,
                    None,
                ),
                Ok(Some(result)),
            );
            assert_eq!(store.type_alias_links(owner), Some(&links));
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One source target keeps physical identity across cold, warm, and composed maps.
    fn inline_objects_map_original_parameters_without_allocating_aliases_or_members() {
        let (mut store, source, outer_parameters) = inline_object_instantiation_fixture();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let target = source.target;
        assert_eq!(source.type_, target);
        assert!(source.mapper.is_none());
        assert!(store.type_payload(target).unwrap().alias().is_none());
        for (own, outer) in source.parameters.iter().zip(&outer_parameters) {
            assert_ne!(own, outer);
            assert_ne!(
                cached_ordinary_type_parameter_owner(&store, *own),
                cached_ordinary_type_parameter_owner(&store, *outer),
            );
        }
        assert_eq!(
            validate_instantiable_member_type(&store, target, &source.parameters, None),
            Ok(()),
        );
        let alias_count = store.type_alias_len();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut results = Vec::new();
        for arguments in [
            vec![string, number],
            vec![number, string],
            outer_parameters.clone(),
        ] {
            let cold = deferred_intersection_store_state(&store);
            assert_eq!(
                cached_instantiation_with_vector(
                    &store,
                    target,
                    &source.parameters,
                    &arguments,
                    None,
                    None,
                ),
                Ok(None),
            );
            assert_eq!(deferred_intersection_store_state(&store), cold);
            let instance = instantiate_type_with_vector_and_session(
                &mut store,
                target,
                &source.parameters,
                &arguments,
                None,
                &mut session,
            )
            .unwrap();
            let mapped = inline_property_object_projection(&store, instance)
                .unwrap()
                .unwrap();
            assert_eq!(mapped.target, target);
            assert_eq!(mapped.declaration, source.declaration);
            assert_eq!(mapped.source_symbol, source.source_symbol);
            assert_eq!(mapped.parameter_owner, source.parameter_owner);
            assert_eq!(mapped.parameters, source.parameters);
            assert_eq!(mapped.arguments, arguments);
            assert!(store.type_payload(instance).unwrap().alias().is_none());
            let physical_mapper = mapped.mapper.unwrap();
            assert_eq!(
                store.type_mapper_has_exact_endpoints(
                    physical_mapper,
                    &source.parameters,
                    &arguments,
                ),
                Some(true),
            );
            assert_eq!(
                store.relation_object_instantiation(
                    target,
                    type_alias_instantiation_cache_key(&arguments, None),
                ),
                Some(instance),
            );
            assert_eq!(store.type_alias_len(), alias_count);
            assert_eq!(
                instantiated_member_type_matches(&store, target, instance, physical_mapper, None),
                Ok(true),
            );
            assert!(store.inline_property_object_recovery(instance).is_none());
            assert!(store.property_object_alias_recovery(instance).is_none());
            let warm = deferred_intersection_store_state(&store);
            for _ in 0..2 {
                assert_eq!(
                    cached_instantiation_with_vector(
                        &store,
                        target,
                        &source.parameters,
                        &arguments,
                        None,
                        None,
                    ),
                    Ok(Some(instance)),
                );
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        &mut store,
                        target,
                        &source.parameters,
                        &arguments,
                        None,
                        &mut session,
                    ),
                    Ok(instance),
                );
            }
            assert_eq!(deferred_intersection_store_state(&store), warm);
            assert!(!results.contains(&instance));
            results.push(instance);
        }
        let warm = deferred_intersection_store_state(&store);
        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut store,
                results[2],
                &outer_parameters,
                &[string, number],
                None,
                &mut session,
            ),
            Ok(results[0]),
        );
        assert_eq!(
            cached_instantiation_with_vector(
                &store,
                results[2],
                &outer_parameters,
                &[string, number],
                None,
                None,
            ),
            Ok(Some(results[0])),
        );
        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut store,
                target,
                &source.parameters,
                &source.parameters,
                None,
                &mut session,
            ),
            Ok(target),
        );
        assert_eq!(deferred_intersection_store_state(&store), warm);
        assert_eq!(session.depth, 0);
        assert!(session.active_mappers.is_empty());
        assert_eq!(session.limit_event_count(), 0);
        for property in &source.properties {
            assert!(store.type_node_links(property.type_node).is_none());
            assert!(store.value_symbol_links(property.symbol).is_none());
        }
        for type_ in std::iter::once(target).chain(results) {
            let object = store.type_payload(type_).unwrap();
            assert!(
                !object
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            );
            assert_eq!(
                object.data().structured(),
                Some(&StructuredTypeData::default())
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Every altered cache must reject without changing the remaining graph.
    fn inline_object_mapping_rejects_changed_mappers_aliases_nodes_and_target_keys() {
        let (mut store, source, _) = inline_object_instantiation_fixture();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let reversed = [arguments[1], arguments[0]];
        let result =
            instantiate_type_with_vector(&mut store, source.target, &source.parameters, &arguments)
                .unwrap();
        let other =
            instantiate_type_with_vector(&mut store, source.target, &source.parameters, &reversed)
                .unwrap();
        let mapper = inline_property_object_projection(&store, result)
            .unwrap()
            .unwrap()
            .mapper;
        let other_mapper = inline_property_object_projection(&store, other)
            .unwrap()
            .unwrap()
            .mapper;
        let reject = |store: &mut CanonicalTypeMapperStore| {
            let before = deferred_intersection_store_state(store);
            assert!(
                cached_instantiation_with_vector(
                    store,
                    source.target,
                    &source.parameters,
                    &arguments,
                    None,
                    None,
                )
                .is_err()
            );
            assert!(
                instantiate_type_with_vector(store, source.target, &source.parameters, &arguments,)
                    .is_err()
            );
            assert_eq!(deferred_intersection_store_state(store), before);
        };
        assert!(store.set_object_target_and_mapper(result, Some(source.target), other_mapper));
        reject(&mut store);
        assert!(store.set_object_target_and_mapper(result, Some(source.target), mapper));

        let alias = store
            .type_alias_links(source.parameter_owner)
            .unwrap()
            .declared_type
            .unwrap();
        let alias = store.type_payload(alias).unwrap().alias().unwrap();
        assert!(store.set_type_alias(result, Some(alias)));
        reject(&mut store);
        assert!(store.set_type_alias(result, None));

        let original_links = store.type_node_links(source.declaration).unwrap().clone();
        let mut changed_links = original_links.clone();
        changed_links.resolved_type = Some(result);
        assert!(store.set_type_node_links(source.declaration, changed_links));
        reject(&mut store);
        assert!(store.set_type_node_links(source.declaration, original_links));

        let TypeData::Object(target) = store.type_payload(source.target).unwrap().data() else {
            panic!("the original inline literal must remain an object")
        };
        let original_cache = target.instantiations.clone();
        let TypeCacheState::Allocated(mut changed_cache) = original_cache.clone() else {
            panic!("both inline instances must use the original target cache")
        };
        let key = type_alias_instantiation_cache_key(&arguments, None);
        assert_eq!(changed_cache.insert(key, other), Some(result));
        assert!(
            store
                .set_object_instantiations(source.target, TypeCacheState::Allocated(changed_cache))
        );
        reject(&mut store);
        assert!(store.set_object_instantiations(source.target, original_cache));
        let before = deferred_intersection_store_state(&store);
        assert_eq!(
            cached_instantiation_with_vector(
                &store,
                source.target,
                &source.parameters,
                &arguments,
                None,
                None,
            ),
            Ok(Some(result)),
        );
        assert_eq!(
            instantiate_type_with_vector(&mut store, source.target, &source.parameters, &arguments),
            Ok(result),
        );
        assert_eq!(deferred_intersection_store_state(&store), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Real caller limits distinguish recovered physical slots from normal mapping.
    fn inline_object_recovery_keeps_the_caller_guard_and_exact_physical_slots() {
        let (mut store, source, outer_parameters) = inline_object_instantiation_fixture();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let error = bootstrap.error_type;
        let intermediate = instantiate_type_with_vector(
            &mut store,
            source.target,
            &source.parameters,
            &outer_parameters,
        )
        .unwrap();
        let before = deferred_intersection_store_state(&store);
        for limits in [
            InstantiationLimits {
                max_depth: 0,
                max_count: 100,
            },
            InstantiationLimits {
                max_depth: 100,
                max_count: 0,
            },
        ] {
            let mut session = InstantiationSession::new(limits);
            let expected = if limits.max_depth == 0 {
                InstantiationError::DepthLimit { depth: 0, limit: 0 }
            } else {
                InstantiationError::CountLimit { count: 0, limit: 0 }
            };
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    &mut store,
                    source.target,
                    &source.parameters,
                    &outer_parameters,
                    None,
                    &mut session,
                ),
                Err(expected),
            );
            assert_eq!(session.count, 0);
            assert!(session.active_mappers.is_empty());
            assert_eq!(deferred_intersection_store_state(&store), before);
        }
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 1,
                max_count: 100,
            },
            error,
        )
        .unwrap();
        let alias_count = store.type_alias_len();
        let signature_count = store.signature_len();
        let result = instantiate_type_with_vector_and_session(
            &mut store,
            intermediate,
            &outer_parameters,
            &arguments,
            None,
            &mut session,
        )
        .unwrap();
        let mapped = inline_property_object_projection(&store, result)
            .unwrap()
            .unwrap();
        assert_eq!(mapped.target, source.target);
        assert_eq!(mapped.parameters, source.parameters);
        assert_eq!(mapped.arguments, [error, error]);
        assert!(store.type_payload(result).unwrap().alias().is_none());
        assert_eq!(store.type_alias_len(), alias_count);
        assert_eq!(store.signature_len(), signature_count);
        assert_eq!(session.count, 1);
        assert_eq!(session.limit_event_count(), 2);
        assert_eq!(session.depth, 0);
        assert!(session.active_mappers.is_empty());
        let retained = store
            .inline_property_object_recovery(result)
            .unwrap()
            .clone();
        assert_eq!(retained.result(), result);
        assert_eq!(retained.error_type(), error);
        assert!(retained.physical_slot_recovered(0));
        assert!(retained.physical_slot_recovered(1));
        assert!(!retained.physical_slot_recovered(2));
        assert!(retained.matches_current_result(&store));
        assert!(store.property_object_alias_recovery(result).is_none());
        let warm = deferred_intersection_store_state(&store);
        assert_eq!(
            cached_instantiation_with_vector(
                &store,
                intermediate,
                &outer_parameters,
                &arguments,
                None,
                None,
            ),
            Ok(None),
            "a recovered physical key must not claim the normal arguments",
        );
        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut store,
                intermediate,
                &outer_parameters,
                &arguments,
                None,
                &mut session,
            ),
            Ok(result),
        );
        assert_eq!(session.count, 2);
        assert_eq!(session.limit_event_count(), 4);
        assert_eq!(deferred_intersection_store_state(&store), warm);
        for mutation in 0..5 {
            let mut changed = retained.clone();
            match mutation {
                0 => {
                    assert_eq!(changed.physical_recovery.pop(), Some(true));
                }
                1 => changed.physical_recovery.fill(false),
                2 => changed.arguments[0] = arguments[0],
                3 => changed.parameters.swap(0, 1),
                4 => changed.result = source.target,
                _ => unreachable!(),
            }
            assert!(!changed.matches_current_result(&store));
            assert_eq!(deferred_intersection_store_state(&store), warm);
        }
        let mut partial_session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 100,
                max_count: 2,
            },
            error,
        )
        .unwrap();
        let partial = instantiate_type_with_vector_and_session(
            &mut store,
            intermediate,
            &outer_parameters,
            &[source.parameters[0], arguments[1]],
            None,
            &mut partial_session,
        )
        .unwrap();
        let partial_projection = inline_property_object_projection(&store, partial)
            .unwrap()
            .unwrap();
        assert_eq!(partial_projection.arguments, [source.parameters[0], error]);
        assert_eq!(partial_session.limit_event_count(), 1);
        let partial_recovery = store.inline_property_object_recovery(partial).unwrap();
        assert!(!partial_recovery.physical_slot_recovered(0));
        assert!(partial_recovery.physical_slot_recovered(1));
        let mut next_session = InstantiationSession::new(InstantiationLimits::default());
        let inherited = instantiate_type_with_vector_and_session(
            &mut store,
            partial,
            &source.parameters[..1],
            &arguments[..1],
            None,
            &mut next_session,
        )
        .unwrap();
        let inherited_projection = inline_property_object_projection(&store, inherited)
            .unwrap()
            .unwrap();
        assert_eq!(inherited_projection.target, source.target);
        assert_eq!(inherited_projection.arguments, [arguments[0], error]);
        let inherited_recovery = store.inline_property_object_recovery(inherited).unwrap();
        assert!(!inherited_recovery.physical_slot_recovered(0));
        assert!(inherited_recovery.physical_slot_recovered(1));
        assert!(inherited_recovery.matches_current_result(&store));
        assert_eq!(next_session.limit_event_count(), 0);
        assert_eq!(next_session.depth, 0);
        assert_eq!(store.type_alias_len(), alias_count);
        assert_eq!(store.signature_len(), signature_count);
        let inherited_counts = deferred_intersection_store_state(&store);
        assert_eq!(
            cached_instantiation_with_vector(
                &store,
                partial,
                &source.parameters[..1],
                &arguments[..1],
                None,
                None,
            ),
            Ok(Some(inherited)),
        );
        assert_eq!(deferred_intersection_store_state(&store), inherited_counts);
        for property in source.properties {
            assert!(store.type_node_links(property.type_node).is_none());
            assert!(store.value_symbol_links(property.symbol).is_none());
        }
    }

    #[test]
    fn closed_declared_objects_and_callables_keep_identity_in_all_mapper_readers() {
        let (mut store, types) = source_alias_instantiation_fixture(
            concat!(
                "type Noop = () => void;\n",
                "type Subscription = { unsubscribe: Noop };\n",
                "type Scope<T> = { value: T };\n",
            ),
            &["Subscription", "Noop", "Scope"],
        );
        let scope = property_object_alias_projection(&store, types[2])
            .unwrap()
            .unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let mapper = store
            .new_type_mapper(scope.parameters.clone(), vec![string])
            .unwrap();
        let before = deferred_intersection_store_state(&store);
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 0,
            max_count: 0,
        });
        for type_ in &types[..2] {
            assert_eq!(
                could_contain_installed_type_variables(&store, *type_, None),
                Ok(false)
            );
            assert_eq!(
                validate_instantiable_member_type(&store, *type_, &scope.parameters, None),
                Ok(())
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    &store,
                    *type_,
                    &scope.parameters,
                    &[string],
                    None,
                    None
                ),
                Ok(Some(*type_)),
            );
            assert_eq!(
                instantiated_member_type_matches(&store, *type_, *type_, mapper, None),
                Ok(true),
            );
            assert_eq!(
                instantiated_member_type_matches(&store, *type_, string, mapper, None),
                Ok(false),
            );
            assert_eq!(
                instantiate_type_with_session(&mut store, *type_, mapper, None, &mut session),
                Ok(*type_),
            );
        }
        assert_eq!(session.count, 0);
        assert_eq!(session.limit_event_count(), 0);
        assert_eq!(deferred_intersection_store_state(&store), before);
    }

    fn mapped_frame_fixture() -> (CanonicalTypeMapperStore, TypeId, TypeId, TypeId, TypeId) {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            })
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (object, number, sentinel) = (
            bootstrap.empty_type_literal_type,
            bootstrap.number_type,
            bootstrap.undefined_or_missing_type,
        );
        let parameter = store.alloc_type_parameter(None).unwrap();
        let template = store
            .alloc_indexed_access_type(object, parameter, AccessFlags::NONE)
            .unwrap();
        (store, template, parameter, number, sentinel)
    }

    fn canonical_array_target(store: &mut CanonicalTypeMapperStore, name: &str) -> TypeId {
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::INTERFACE,
                EscapedName::source(name),
            ))
            .unwrap();
        let parameter_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_PARAMETER,
                EscapedName::source("T"),
            ))
            .unwrap();
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
        target
    }

    fn canonical_array_targets(store: &mut CanonicalTypeMapperStore) -> CanonicalArrayTargets {
        CanonicalArrayTargets::for_test(
            canonical_array_target(store, "Array"),
            canonical_array_target(store, "ReadonlyArray"),
        )
    }

    #[test]
    fn maps_type_parameters_and_preserves_dependency_closed_leaves() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();

        assert_eq!(instantiate_type(&mut store, parameter, mapper), Ok(number));
        assert_eq!(instantiate_type(&mut store, string, mapper), Ok(string));
    }

    #[test]
    fn authenticated_unique_symbol_members_preserve_identity_and_reject_poisoned_owners() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let owner = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
                EscapedName::source("key"),
            ))
            .unwrap();
        let unique = store.alloc_unique_es_symbol_type(owner).unwrap();
        assert!(store.set_value_symbol_links(
            owner,
            ValueSymbolLinks {
                resolved_type: Some(unique),
                ..ValueSymbolLinks::default()
            },
        ));

        assert_eq!(
            validate_instantiable_member_type(&store, unique, &[parameter], None),
            Ok(()),
        );
        assert_eq!(
            instantiable_member_type_contains_variables(&store, unique, &[parameter], None),
            Ok(false),
        );
        assert_eq!(instantiate_type(&mut store, unique, mapper), Ok(unique));
        let before = (store.type_len(), store.mapper_len());
        assert_eq!(
            instantiated_member_type_matches(&store, unique, unique, mapper, None),
            Ok(true),
        );
        assert_eq!(
            instantiated_member_type_matches(&store, unique, number, mapper, None),
            Ok(false),
        );
        assert_eq!((store.type_len(), store.mapper_len()), before);

        assert!(store.set_value_symbol_links(owner, ValueSymbolLinks::default()));
        assert_eq!(
            validate_instantiable_member_type(&store, unique, &[parameter], None),
            Err(InstantiationError::UnsupportedType(unique)),
        );
        assert_eq!(
            instantiated_member_type_matches(&store, unique, unique, mapper, None),
            Err(InstantiationError::UnsupportedType(unique)),
        );
    }

    #[test]
    fn global_concat_array_unions_instantiate_tuple_arguments_and_replay_warm() {
        let mut store = initialized_store();
        let array_targets = canonical_array_targets(&mut store);
        let concat_target = canonical_array_target(&mut store, "ConcatArray");
        let concat_symbol = store.type_payload(concat_target).unwrap().symbol().unwrap();
        assert!(store.set_declared_type_links(
            concat_symbol,
            DeclaredTypeLinks {
                declared_type: Some(concat_target),
                ..DeclaredTypeLinks::default()
            },
        ));
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            store.insert_symbol(globals, EscapedName::source("ConcatArray"), concat_symbol),
            Some(None),
        );

        let parameter = store.alloc_type_parameter(None).unwrap();
        let concat_parameter = create_direct_generic_reference(
            &mut store,
            concat_target,
            &[parameter],
            ObjectFlags::NONE,
        )
        .unwrap();
        let source_union = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, concat_parameter])
            .unwrap();
        let source = store
            .create_canonical_array_type_with_targets(array_targets, source_union, false)
            .unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let required = store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let tuple = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number, number],
                &[required, required],
                false,
            ))
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, tuple).unwrap();

        assert_eq!(
            validate_instantiable_member_type(&store, source, &[parameter], Some(array_targets)),
            Ok(()),
        );
        assert_eq!(
            instantiated_member_type_matches(
                &store,
                source_union,
                tuple,
                mapper,
                Some(array_targets)
            ),
            Ok(false),
            "warm validation cannot invent an uncached ConcatArray instantiation",
        );

        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let instantiated = instantiate_type_with_session(
            &mut store,
            source,
            mapper,
            Some(array_targets),
            &mut session,
        )
        .unwrap();
        let actual = store
            .canonical_array_reference_with_targets(array_targets, instantiated)
            .unwrap()
            .unwrap()
            .element_type;
        let concat_tuple = store
            .relation_object_instantiation(concat_target, type_list_key(&[tuple]))
            .unwrap();
        let TypeData::Union(union) = store.type_payload(actual).unwrap().data() else {
            panic!("the specialized overload must retain its anonymous union")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&tuple));
        assert!(union.union.types.contains(&concat_tuple));

        let warm = (store.type_len(), store.mapper_len());
        assert_eq!(
            instantiated_member_type_matches(
                &store,
                source,
                instantiated,
                mapper,
                Some(array_targets),
            ),
            Ok(true),
        );
        assert_eq!((store.type_len(), store.mapper_len()), warm);
    }

    #[test]
    fn unregistered_generic_union_references_remain_unsupported() {
        let mut store = initialized_store();
        let target = canonical_array_target(&mut store, "Pair");
        let owner = store.type_payload(target).unwrap().symbol().unwrap();
        assert!(store.set_declared_type_links(
            owner,
            DeclaredTypeLinks {
                declared_type: Some(target),
                ..DeclaredTypeLinks::default()
            },
        ));
        let parameter = store.alloc_type_parameter(None).unwrap();
        let reference =
            create_direct_generic_reference(&mut store, target, &[parameter], ObjectFlags::NONE)
                .unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, reference])
            .unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let before = (store.type_len(), store.mapper_len());

        assert_eq!(
            validate_instantiable_member_type(&store, source, &[parameter], None),
            Err(InstantiationError::UnsupportedUnionConstituent(reference)),
        );
        assert_eq!(
            instantiate_type(&mut store, source, mapper),
            Err(InstantiationError::UnsupportedUnionConstituent(reference)),
        );
        assert_eq!((store.type_len(), store.mapper_len()), before);
    }

    #[test]
    fn deferred_generic_intersections_substitute_constituents_and_alias_arguments_lazily() {
        let mut fixture = deferred_generic_intersection_fixture();
        let source = fixture.intersection;
        let sources = [fixture.props, fixture.element];
        let targets = [fixture.attributes_reference, fixture.string];

        let instantiated =
            instantiate_type_with_vector(&mut fixture.store, source, &sources, &targets).unwrap();

        let projection = fixture
            .store
            .validate_deferred_intersection_type(instantiated)
            .unwrap();
        assert_eq!(projection.alias_symbol, Some(fixture.alias));
        assert_eq!(projection.alias_arguments, targets);
        assert_eq!(projection.types[1], fixture.attributes_reference);
        assert_eq!(
            validate_direct_generic_reference(&fixture.store, projection.types[0])
                .unwrap()
                .type_arguments,
            [fixture.string],
        );
        let record = fixture.store.type_payload(instantiated).unwrap();
        assert!(
            !record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        assert!(record.data().structured().unwrap().members.is_none());

        let warm = deferred_intersection_store_state(&fixture.store);
        assert_eq!(
            instantiate_type_with_vector(&mut fixture.store, source, &sources, &targets),
            Ok(instantiated),
        );
        assert_eq!(deferred_intersection_store_state(&fixture.store), warm);
    }

    #[test]
    fn unchanged_deferred_generic_intersections_reuse_their_original_identity() {
        let mut fixture = deferred_generic_intersection_fixture();
        let source = fixture.intersection;
        let arguments = [fixture.props, fixture.element];
        let before = deferred_intersection_store_state(&fixture.store);

        assert_eq!(
            instantiate_type_with_vector(&mut fixture.store, source, &arguments, &arguments),
            Ok(source),
        );
        assert_eq!(deferred_intersection_store_state(&fixture.store), before);
    }

    #[test]
    fn non_nullable_conditional_instantiation_preserves_cold_and_warm_identity() {
        let library = parse_source_file("type NonNullable<T> = T & {};");
        let source = parse_source_file(NON_NULLABLE_CONDITIONAL_SOURCE);
        for strict_null_checks in [false, true] {
            let mut fixture =
                non_nullable_conditional_fixture(&library, &source, strict_null_checks);
            let sources = [fixture.parameter];
            let targets = [fixture.argument];
            let store = fixture.context.store_mut_for_test();
            let empty = store.intrinsic_bootstrap().unwrap().empty_type_literal_type;
            let conditional = match store.type_payload(fixture.argument).unwrap().data() {
                TypeData::Conditional(data) => TypeData::Conditional(data.clone()),
                _ => panic!("expected the source-produced conditional argument"),
            };
            let conditional_alias = store.type_payload(fixture.argument).unwrap().alias();
            let production_lengths = store.conditional_production_lengths();
            let before = deferred_intersection_store_state(store);
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    fixture.source,
                    &sources,
                    &targets,
                    None,
                    None,
                ),
                Ok(None),
            );
            assert_eq!(deferred_intersection_store_state(store), before);

            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let result = instantiate_type_with_vector_and_session(
                store,
                fixture.source,
                &sources,
                &targets,
                None,
                &mut session,
            )
            .unwrap();
            assert_ne!(result, fixture.argument);
            assert_eq!(session.query_count(), 2);
            assert_eq!(session.total_count(), 2);
            assert_eq!(session.depth, 0);
            assert!(session.active_mappers.is_empty());
            let projection = store.validate_deferred_intersection_type(result).unwrap();
            assert_eq!(projection.types, [fixture.argument, empty]);
            assert_eq!(projection.alias_symbol, Some(fixture.alias));
            assert_eq!(projection.alias_arguments, targets);
            assert_eq!(store.type_len(), before.0[0] + 1);
            assert_eq!(store.type_alias_len(), before.0[1] + 1);
            assert_eq!(store.mapper_len(), before.0[2]);
            let TypeData::Intersection(data) = store.type_payload(result).unwrap().data() else {
                panic!("NonNullable must retain the conditional and empty object")
            };
            assert_eq!(data.intersection.structured, StructuredTypeData::default());
            assert!(data.intersection.property_cache.is_none());
            assert!(data.intersection.resolved_properties.is_none());

            let warm = deferred_intersection_store_state(store);
            let forward = store.intersection_types.clone();
            let reverse = store.intersection_keys_by_type.clone();
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    fixture.source,
                    &sources,
                    &targets,
                    None,
                    None,
                ),
                Ok(Some(result)),
            );
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    fixture.source,
                    &sources,
                    &targets,
                    None,
                    &mut session,
                ),
                Ok(result),
            );
            assert_eq!(session.query_count(), 4);
            assert_eq!(session.total_count(), 4);
            assert_eq!(deferred_intersection_store_state(store), warm);
            assert_eq!(store.intersection_types, forward);
            assert_eq!(store.intersection_keys_by_type, reverse);
            assert_eq!(store.conditional_production_lengths(), production_lengths);
            assert_eq!(
                store.type_payload(fixture.argument).unwrap().data(),
                &conditional
            );
            assert_eq!(
                store.type_payload(fixture.argument).unwrap().alias(),
                conditional_alias
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each damaged proof must reject the same retained result.
    fn non_nullable_conditional_cached_replay_rejects_damaged_proofs_and_keys() {
        let library = parse_source_file("type NonNullable<T> = T & {};");
        let source = parse_source_file(NON_NULLABLE_CONDITIONAL_SOURCE);
        let mut fixture = non_nullable_conditional_fixture(&library, &source, true);
        let sources = [fixture.parameter];
        let targets = [fixture.argument];
        let store = fixture.context.store_mut_for_test();
        let result =
            instantiate_type_with_vector(store, fixture.source, &sources, &targets).unwrap();
        let key = store
            .intersection_keys_by_type
            .get(&result)
            .unwrap()
            .clone();
        let identity = store.type_payload(result).unwrap().alias().unwrap();
        let TypeData::Conditional(conditional) =
            store.type_payload(fixture.argument).unwrap().data()
        else {
            panic!("the source query must retain a conditional")
        };
        let conditional = conditional.clone();
        let original_root_alias = store.conditional_root(conditional.root).unwrap().alias();
        assert!(original_root_alias.is_some());
        let assert_rejected = |store: &CanonicalTypeMapperStore| {
            let before = deferred_intersection_store_state(store);
            let production_lengths = store.conditional_production_lengths();
            let forward = store.intersection_types.clone();
            let reverse = store.intersection_keys_by_type.clone();
            assert!(
                cached_instantiation_with_vector(
                    store,
                    fixture.source,
                    &sources,
                    &targets,
                    None,
                    None,
                )
                .is_err()
            );
            assert!(store.validate_deferred_intersection_type(result).is_err());
            assert_eq!(deferred_intersection_store_state(store), before);
            assert_eq!(store.conditional_production_lengths(), production_lengths);
            assert_eq!(store.intersection_types, forward);
            assert_eq!(store.intersection_keys_by_type, reverse);
        };

        assert!(store.set_conditional_resolution(
            fixture.argument,
            conditional.resolved_true_type,
            conditional.resolved_false_type,
            conditional.resolved_inferred_true_type,
            conditional.resolved_default_constraint,
            conditional.resolved_constraint_of_distributive,
            None,
            conditional.combined_mapper,
        ));
        assert_rejected(store);
        assert!(store.set_conditional_resolution(
            fixture.argument,
            conditional.resolved_true_type,
            conditional.resolved_false_type,
            conditional.resolved_inferred_true_type,
            conditional.resolved_default_constraint,
            conditional.resolved_constraint_of_distributive,
            conditional.mapper,
            conditional.combined_mapper,
        ));

        assert!(store.set_conditional_root_alias(conditional.root, None));
        assert_rejected(store);
        assert!(store.set_conditional_root_alias(conditional.root, original_root_alias));
        assert!(store.set_type_alias_arguments(identity, Some(vec![fixture.parameter])));
        assert_rejected(store);
        assert!(store.set_type_alias_arguments(identity, Some(targets.to_vec())));

        assert_eq!(store.intersection_types.remove(&key), Some(result));
        assert_rejected(store);
        assert!(
            store
                .intersection_types
                .insert(key.clone(), result)
                .is_none()
        );
        assert_eq!(
            store.intersection_keys_by_type.remove(&result),
            Some(key.clone())
        );
        assert_rejected(store);
        assert!(
            store
                .intersection_keys_by_type
                .insert(result, key)
                .is_none()
        );

        let restored = deferred_intersection_store_state(store);
        assert_eq!(
            cached_instantiation_with_vector(store, fixture.source, &sources, &targets, None, None,),
            Ok(Some(result)),
        );
        assert_eq!(
            instantiate_type_with_vector(store, fixture.source, &sources, &targets),
            Ok(result),
        );
        assert_eq!(deferred_intersection_store_state(store), restored);
        assert_eq!(
            store.type_payload(fixture.argument).unwrap().data(),
            &TypeData::Conditional(conditional)
        );
    }

    #[test]
    fn non_nullable_conditional_rejects_unproved_and_foreign_arguments() {
        let library = parse_source_file("type NonNullable<T> = T & {};");
        let source = parse_source_file(NON_NULLABLE_CONDITIONAL_SOURCE);
        let mut fixture = non_nullable_conditional_fixture(&library, &source, true);
        let foreign = non_nullable_conditional_fixture(&library, &source, true);
        let sources = [fixture.parameter];
        let store = fixture.context.store_mut_for_test();
        let empty = store.intrinsic_bootstrap().unwrap().empty_type_literal_type;
        let record = store.type_payload(fixture.argument).unwrap();
        let alias = record.alias();
        let TypeData::Conditional(data) = record.data() else {
            panic!("the source query must retain a conditional")
        };
        let data = data.clone();
        let unproved = store
            .alloc_conditional_type(
                data.root,
                data.check_type,
                data.extends_type,
                data.mapper,
                data.combined_mapper,
            )
            .unwrap();
        assert!(store.set_type_alias(unproved, alias));
        assert!(store.conditional_type_production(unproved).is_none());
        for (argument, expected_count) in [(unproved, 2), (foreign.argument, 0)] {
            let before = deferred_intersection_store_state(store);
            let production_lengths = store.conditional_production_lengths();
            let forward = store.intersection_types.clone();
            let reverse = store.intersection_keys_by_type.clone();
            assert_eq!(
                store.canonical_deferred_intersection_type(&[argument, empty], None),
                Err(IntersectionTypeError::MalformedConstituent(argument)),
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    fixture.source,
                    &sources,
                    &[argument],
                    None,
                    None,
                ),
                Err(InstantiationError::InvalidType(argument)),
            );
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    fixture.source,
                    &sources,
                    &[argument],
                    None,
                    &mut session,
                ),
                Err(InstantiationError::InvalidType(argument)),
            );
            assert_eq!(session.query_count(), expected_count);
            assert_eq!(session.depth, 0);
            assert!(session.active_mappers.is_empty());
            assert_eq!(deferred_intersection_store_state(store), before);
            assert_eq!(store.conditional_production_lengths(), production_lengths);
            assert_eq!(store.intersection_types, forward);
            assert_eq!(store.intersection_keys_by_type, reverse);
        }
    }

    #[test]
    fn non_nullable_conditional_keeps_remapping_and_members_unsupported() {
        let library = parse_source_file("type NonNullable<T> = T & {};");
        let source = parse_source_file(NON_NULLABLE_CONDITIONAL_SOURCE);
        let mut fixture = non_nullable_conditional_fixture(&library, &source, true);
        let store = fixture.context.store_mut_for_test();
        let result = instantiate_type_with_vector(
            store,
            fixture.source,
            &[fixture.parameter],
            &[fixture.argument],
        )
        .unwrap();
        let projection = store.validate_deferred_intersection_type(result).unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let before = deferred_intersection_store_state(store);
        let forward = store.intersection_types.clone();
        let reverse = store.intersection_keys_by_type.clone();
        assert_eq!(
            cached_instantiation_with_vector(
                store,
                result,
                &[fixture.argument_parameter],
                &[string],
                None,
                None,
            ),
            Err(InstantiationError::UnsupportedType(fixture.argument)),
        );
        assert_eq!(
            instantiate_type_with_vector(store, result, &[fixture.argument_parameter], &[string]),
            Err(InstantiationError::UnsupportedType(fixture.argument)),
        );
        assert_eq!(
            store.canonical_intersection_type(&projection.types, Some(fixture.alias)),
            Err(IntersectionTypeError::UnsupportedConstituent(
                fixture.argument
            )),
        );
        assert_eq!(deferred_intersection_store_state(store), before);
        assert_eq!(store.intersection_types, forward);
        assert_eq!(store.intersection_keys_by_type, reverse);
        assert_eq!(
            store.validate_deferred_intersection_type(result),
            Ok(projection)
        );
    }

    const DEFERRED_CONDITIONAL_ARRAY_LIBRARY: &str = concat!(
        "type NonNullable<T> = T & {}; ",
        "interface Array<T> {} interface ReadonlyArray<T> {}",
    );
    const DEFERRED_CONDITIONAL_ARRAY_SOURCE: &str = concat!(
        "type Select<Check, Value> = Check extends string ? Value : boolean; ",
        "type Forward<Other> = Select<Other, Other[]>;",
    );

    #[test]
    #[allow(clippy::too_many_lines)] // Both mapper representations must preserve the nested source argument.
    fn deferred_conditional_remap_composes_nested_array_arguments() {
        for stored_mapper in [false, true] {
            let library = parse_source_file(DEFERRED_CONDITIONAL_ARRAY_LIBRARY);
            let source = parse_source_file(DEFERRED_CONDITIONAL_ARRAY_SOURCE);
            let mut fixture = non_nullable_conditional_fixture(&library, &source, true);
            let targets = CanonicalArrayTargets::from_global_types(fixture.context.global_types());
            let store = fixture.context.store_mut_for_test();
            let parameter = fixture.argument_parameter;
            let argument = fixture.parameter;
            let projection = conditional_remap_projection(store, fixture.argument).unwrap();
            assert_eq!(projection.arguments().len(), 2);
            assert_eq!(projection.arguments()[0], parameter);
            let original_array = projection.arguments()[1];
            assert_eq!(
                store
                    .canonical_array_reference_with_targets(targets, original_array)
                    .unwrap()
                    .unwrap()
                    .element_type,
                parameter
            );
            let mapper = store.new_simple_type_mapper(parameter, argument).unwrap();
            let before = conditional_remap_projection(store, fixture.argument).unwrap();
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    fixture.argument,
                    &[parameter],
                    &[argument],
                    Some(targets),
                    None,
                ),
                Ok(None)
            );
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let result = if stored_mapper {
                instantiate_type_with_session(
                    store,
                    fixture.argument,
                    mapper,
                    Some(targets),
                    &mut session,
                )
            } else {
                instantiate_type_with_vector_and_session(
                    store,
                    fixture.argument,
                    &[parameter],
                    &[argument],
                    Some(targets),
                    &mut session,
                )
            }
            .unwrap();
            let result_projection = conditional_remap_projection(store, result).unwrap();
            assert_eq!(result_projection.arguments()[0], argument);
            assert_ne!(result_projection.arguments()[1], original_array);
            let mapped_array = store
                .canonical_array_reference_with_targets(targets, result_projection.arguments()[1])
                .unwrap()
                .unwrap();
            assert_eq!(mapped_array.element_type, argument);
            assert_eq!(
                result_projection.alias(),
                Some(ConditionalAliasIdentity {
                    symbol: projection.alias().unwrap().symbol,
                    type_arguments: &[argument],
                })
            );
            let TypeData::Conditional(data) = store.type_payload(result).unwrap().data() else {
                unreachable!()
            };
            assert_eq!(data.check_type, argument);
            assert!(data.resolved_true_type.is_none());
            assert!(data.resolved_false_type.is_none());
            assert_eq!(
                conditional_remap_projection(store, fixture.argument).unwrap(),
                before
            );
            assert_eq!(session.depth, 0);
            assert!(session.active_mappers.is_empty());
            assert_eq!(session.limit_event_count(), 0);
            let warm = deferred_intersection_store_state(store);
            for _ in 0..2 {
                assert_eq!(
                    cached_instantiation_with_vector(
                        store,
                        fixture.argument,
                        &[parameter],
                        &[argument],
                        Some(targets),
                        None,
                    ),
                    Ok(Some(result))
                );
                assert_eq!(
                    instantiate_type_with_session(
                        store,
                        fixture.argument,
                        mapper,
                        Some(targets),
                        &mut session,
                    ),
                    Ok(result)
                );
                assert_eq!(deferred_intersection_store_state(store), warm);
            }

            // A generic argument inside Array<T> does not itself prove that a
            // conditional check remains deferred in Go.
            let conditional_counts = store.conditional_production_lengths();
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    fixture.argument,
                    &[parameter],
                    &[result_projection.arguments()[1]],
                    Some(targets),
                    &mut session,
                ),
                Err(InstantiationError::UnsupportedType(fixture.argument))
            );
            assert_eq!(store.conditional_production_lengths(), conditional_counts);
            assert_eq!(session.depth, 0);
            assert!(session.active_mappers.is_empty());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Nested limits, scratch replay, and a healthy retry share the same source shell.
    fn deferred_conditional_remap_limits_do_not_publish_normal_results() {
        for limits in [
            InstantiationLimits {
                max_depth: 2,
                max_count: 100,
            },
            InstantiationLimits {
                max_depth: 100,
                max_count: 2,
            },
        ] {
            let library = parse_source_file(DEFERRED_CONDITIONAL_ARRAY_LIBRARY);
            let source = parse_source_file(DEFERRED_CONDITIONAL_ARRAY_SOURCE);
            let mut fixture = non_nullable_conditional_fixture(&library, &source, true);
            let targets = CanonicalArrayTargets::from_global_types(fixture.context.global_types());
            let store = fixture.context.store_mut_for_test();
            let parameter = fixture.argument_parameter;
            let argument = fixture.parameter;
            let mapper = store.new_simple_type_mapper(parameter, argument).unwrap();
            let error_type = store.intrinsic_bootstrap().unwrap().error_type;
            let TypeData::Conditional(data) = store.type_payload(fixture.argument).unwrap().data()
            else {
                unreachable!()
            };
            let root = data.root;
            let root_cache = store
                .conditional_root(root)
                .unwrap()
                .instantiations()
                .clone();
            let production_lengths = store.conditional_production_lengths();
            let aliases = store.type_alias_len();
            let mut fail_fast = InstantiationSession::new(limits);
            assert_eq!(
                instantiate_type_with_session(
                    store,
                    fixture.argument,
                    mapper,
                    Some(targets),
                    &mut fail_fast,
                ),
                Err(if limits.max_depth == 2 {
                    InstantiationError::DepthLimit { depth: 2, limit: 2 }
                } else {
                    InstantiationError::CountLimit { count: 2, limit: 2 }
                })
            );
            assert_eq!(fail_fast.depth, 0);
            assert!(fail_fast.active_mappers.is_empty());
            assert_eq!(fail_fast.limit_event_count(), 1);

            let mut recovering =
                InstantiationSession::new_recovering(store, limits, error_type).unwrap();
            recovering.active_mappers.push(ActiveMapperFrame {
                mapping: InstantiationMappingIdentity::Stored(mapper),
                cache: HashMap::new(),
            });
            let scratch_key = instantiation_cache_key(store, fixture.argument, None).unwrap();
            for _ in 0..2 {
                let mark = recovering.limit_event_mark();
                assert_eq!(
                    instantiate_type_with_session(
                        store,
                        fixture.argument,
                        mapper,
                        Some(targets),
                        &mut recovering,
                    ),
                    Ok(error_type)
                );
                assert!(recovering.limit_event_occurred_since(mark));
                assert_eq!(recovering.depth, 0);
                assert_eq!(recovering.active_mappers.len(), 1);
                assert!(
                    !recovering.active_mappers[0]
                        .cache
                        .contains_key(&scratch_key)
                );
                assert_eq!(
                    store.conditional_root(root).unwrap().instantiations(),
                    &root_cache
                );
                assert_eq!(store.conditional_production_lengths(), production_lengths);
                assert_eq!(store.type_alias_len(), aliases);
                assert_eq!(
                    cached_instantiation_with_vector(
                        store,
                        fixture.argument,
                        &[parameter],
                        &[argument],
                        Some(targets),
                        None,
                    ),
                    Ok(None)
                );
            }
            recovering.active_mappers.pop().unwrap();
            let mut healthy = InstantiationSession::new(InstantiationLimits::default());
            let result = instantiate_type_with_session(
                store,
                fixture.argument,
                mapper,
                Some(targets),
                &mut healthy,
            )
            .unwrap();
            assert_ne!(result, error_type);
            assert_eq!(healthy.depth, 0);
            assert!(healthy.active_mappers.is_empty());
            assert_eq!(healthy.limit_event_count(), 0);
            let warm = deferred_intersection_store_state(store);
            assert_eq!(
                instantiate_type_with_session(
                    store,
                    fixture.argument,
                    mapper,
                    Some(targets),
                    &mut healthy,
                ),
                Ok(result)
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    fixture.argument,
                    &[parameter],
                    &[argument],
                    Some(targets),
                    None,
                ),
                Ok(Some(result))
            );
            assert_eq!(deferred_intersection_store_state(store), warm);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One retained frame must reject each damaged destination and then replay it.
    fn deferred_conditional_remap_scratch_hits_validate_the_destination() {
        for corruption in 0..4 {
            let (mut store, types) = source_alias_instantiation_fixture(
                concat!(
                    "type Select<Value> = Value extends string ? number : boolean; ",
                    "type Forward<Other> = Select<Other>; type Next<After> = After;",
                ),
                &["Forward", "Next"],
            );
            let [source, argument] = types.as_slice() else {
                unreachable!()
            };
            let parameter = conditional_remap_projection(&store, *source)
                .unwrap()
                .arguments()[0];
            let mapper = store.new_simple_type_mapper(parameter, *argument).unwrap();
            let scratch_key = instantiation_cache_key(&store, *source, None).unwrap();
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            session.active_mappers.push(ActiveMapperFrame {
                mapping: InstantiationMappingIdentity::Stored(mapper),
                cache: HashMap::new(),
            });
            let result =
                instantiate_type_with_session(&mut store, *source, mapper, None, &mut session)
                    .unwrap();
            assert_eq!(
                session.active_mappers[0].cache.get(&scratch_key),
                Some(&result)
            );
            let TypeData::Conditional(data) = store.type_payload(result).unwrap().data() else {
                unreachable!()
            };
            let root = data.root;
            let original_cache = store
                .conditional_root(root)
                .unwrap()
                .instantiations()
                .clone();
            let TypeCacheState::Allocated(cache) = &original_cache else {
                unreachable!()
            };
            let keys = cache
                .iter()
                .filter_map(|(key, value)| (*value == result).then_some(*key))
                .collect::<Vec<_>>();
            let [key] = keys.as_slice() else {
                panic!("the deferred result must have one root cache key")
            };
            let alias = store.type_payload(result).unwrap().alias().unwrap();
            let original_alias_arguments = store
                .type_alias(alias)
                .unwrap()
                .type_arguments()
                .map(<[TypeId]>::to_vec);
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            match corruption {
                0 | 1 => {
                    let mut cache = cache.clone();
                    assert_eq!(cache.remove(key), Some(result));
                    if corruption == 1 {
                        cache.insert(*key, *source);
                    }
                    assert!(store.set_conditional_root_instantiations(
                        root,
                        TypeCacheState::Allocated(cache)
                    ));
                }
                2 => assert!(store.set_type_alias_arguments(alias, Some(vec![number]))),
                3 => {
                    session.active_mappers[0]
                        .cache
                        .insert(scratch_key.clone(), *source);
                }
                _ => unreachable!(),
            }
            let before = deferred_intersection_store_state(&store);
            let budget = (
                session.depth,
                session.count,
                session.total_count,
                session.limit_event_mark(),
            );
            let poisoned_cache = store
                .conditional_root(root)
                .unwrap()
                .instantiations()
                .clone();
            for _ in 0..2 {
                assert_eq!(
                    instantiate_type_with_session(&mut store, *source, mapper, None, &mut session,),
                    Err(InstantiationError::InvalidType(*source)),
                    "corruption {corruption}"
                );
                assert_eq!(deferred_intersection_store_state(&store), before);
                assert_eq!(
                    (
                        session.depth,
                        session.count,
                        session.total_count,
                        session.limit_event_mark()
                    ),
                    budget
                );
                assert_eq!(session.active_mappers.len(), 1);
                assert_eq!(
                    store.conditional_root(root).unwrap().instantiations(),
                    &poisoned_cache
                );
            }
            assert!(store.set_conditional_root_instantiations(root, original_cache));
            assert!(store.set_type_alias_arguments(alias, original_alias_arguments));
            session.active_mappers[0].cache.insert(scratch_key, result);
            assert_eq!(
                instantiate_type_with_session(&mut store, *source, mapper, None, &mut session,),
                Ok(result)
            );
            assert_eq!(
                (
                    session.depth,
                    session.count,
                    session.total_count,
                    session.limit_event_mark()
                ),
                budget
            );
            assert_eq!(deferred_intersection_store_state(&store), before);
            session.active_mappers.pop().unwrap();
            assert!(session.active_mappers.is_empty());
        }
    }

    #[test]
    fn deferred_conditional_remap_does_not_recover_for_an_earlier_event_or_error_argument() {
        let (mut store, types) = source_alias_instantiation_fixture(
            concat!(
                "type Select<Check, Value> = Check extends string ? Value : boolean; ",
                "type Next<Other> = Other;",
            ),
            &["Select", "Next"],
        );
        let [source, argument] = types.as_slice() else {
            unreachable!()
        };
        let projection = conditional_remap_projection(&store, *source).unwrap();
        let error_type = store.intrinsic_bootstrap().unwrap().error_type;
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits::default(),
            error_type,
        )
        .unwrap();
        session.limit_event_generation = 7;
        let mark = session.limit_event_mark();
        let result = instantiate_type_with_vector_and_session(
            &mut store,
            *source,
            projection.parameters(),
            &[*argument, error_type],
            None,
            &mut session,
        )
        .unwrap();
        assert_ne!(result, error_type);
        assert_eq!(session.limit_event_mark(), mark);
        let mapped = conditional_remap_projection(&store, result).unwrap();
        assert_eq!(mapped.arguments(), &[*argument, error_type]);
        assert_eq!(session.depth, 0);
        assert!(session.active_mappers.is_empty());
        let warm = deferred_intersection_store_state(&store);
        assert_eq!(
            cached_instantiation_with_vector(
                &store,
                *source,
                projection.parameters(),
                &[*argument, error_type],
                None,
                None,
            ),
            Ok(Some(result))
        );
        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut store,
                *source,
                projection.parameters(),
                &[*argument, error_type],
                None,
                &mut session,
            ),
            Ok(result)
        );
        assert_eq!(session.limit_event_mark(), mark);
        assert_eq!(deferred_intersection_store_state(&store), warm);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Real calls cover cold failure, recovery, and a spent warm budget.
    fn non_nullable_conditional_instantiation_uses_caller_budget_and_recovery() {
        let library = parse_source_file("type NonNullable<T> = T & {};");
        let source = parse_source_file(NON_NULLABLE_CONDITIONAL_SOURCE);
        let mut fixture = non_nullable_conditional_fixture(&library, &source, true);
        let sources = [fixture.parameter];
        let targets = [fixture.argument];
        let store = fixture.context.store_mut_for_test();
        let error_type = store.intrinsic_bootstrap().unwrap().error_type;
        let limits = InstantiationLimits {
            max_depth: 100,
            max_count: 1,
        };
        let before = deferred_intersection_store_state(store);
        let mut fail_fast = InstantiationSession::new(limits);
        assert_eq!(
            instantiate_type_with_vector_and_session(
                store,
                fixture.source,
                &sources,
                &targets,
                None,
                &mut fail_fast,
            ),
            Err(InstantiationError::CountLimit { count: 1, limit: 1 }),
        );
        assert_eq!(fail_fast.query_count(), 1);
        assert_eq!(fail_fast.total_count(), 1);
        assert_eq!(fail_fast.depth, 0);
        assert_eq!(fail_fast.limit_event_count(), 1);
        assert!(fail_fast.active_mappers.is_empty());
        assert_eq!(deferred_intersection_store_state(store), before);

        let mut recovering =
            InstantiationSession::new_recovering(store, limits, error_type).unwrap();
        assert_eq!(
            instantiate_type_with_vector_and_session(
                store,
                fixture.source,
                &sources,
                &targets,
                None,
                &mut recovering,
            ),
            Ok(error_type),
        );
        assert_eq!(recovering.query_count(), 1);
        assert_eq!(recovering.total_count(), 1);
        assert_eq!(recovering.limit_event_count(), 2);
        assert_eq!(recovering.depth, 0);
        assert!(recovering.active_mappers.is_empty());
        assert_eq!(deferred_intersection_store_state(store), before);

        let mut success = InstantiationSession::new(InstantiationLimits {
            max_depth: 100,
            max_count: 3,
        });
        let result = instantiate_type_with_vector_and_session(
            store,
            fixture.source,
            &sources,
            &targets,
            None,
            &mut success,
        )
        .unwrap();
        assert_eq!(success.query_count(), 2);
        assert_eq!(success.total_count(), 2);
        assert_eq!(success.limit_event_count(), 0);
        let warm = deferred_intersection_store_state(store);
        let forward = store.intersection_types.clone();
        let reverse = store.intersection_keys_by_type.clone();
        for recover in [false, true] {
            let mut session = if recover {
                InstantiationSession::new_recovering(store, limits, error_type).unwrap()
            } else {
                InstantiationSession::new(limits)
            };
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    fixture.parameter,
                    &sources,
                    &targets,
                    None,
                    &mut session,
                ),
                Ok(fixture.argument),
            );
            assert_eq!(session.query_count(), 1);
            let actual = instantiate_type_with_vector_and_session(
                store,
                fixture.source,
                &sources,
                &targets,
                None,
                &mut session,
            );
            if recover {
                assert_eq!(actual, Ok(error_type));
            } else {
                assert_eq!(
                    actual,
                    Err(InstantiationError::CountLimit { count: 1, limit: 1 })
                );
            }
            assert_eq!(session.query_count(), 1);
            assert_eq!(session.total_count(), 1);
            assert_eq!(session.limit_event_count(), 1);
            assert_eq!(session.depth, 0);
            assert!(session.active_mappers.is_empty());
        }
        let mut zero_budget = InstantiationSession::new(InstantiationLimits {
            max_depth: 100,
            max_count: 0,
        });
        assert_eq!(
            instantiate_type_with_vector_and_session(
                store,
                fixture.source,
                &sources,
                &targets,
                None,
                &mut zero_budget,
            ),
            Err(InstantiationError::CountLimit { count: 0, limit: 0 }),
        );
        assert_eq!(zero_budget.query_count(), 0);
        assert_eq!(zero_budget.total_count(), 0);
        assert_eq!(
            cached_instantiation_with_vector(store, fixture.source, &sources, &targets, None, None,),
            Ok(Some(result)),
        );
        assert_eq!(deferred_intersection_store_state(store), warm);
        assert_eq!(store.intersection_types, forward);
        assert_eq!(store.intersection_keys_by_type, reverse);
    }

    #[test]
    fn deferred_intersection_alias_overrides_keep_distinct_cold_and_warm_owners() {
        let mut fixture = deferred_generic_intersection_fixture();
        let source = fixture.intersection;
        let sources = [fixture.props, fixture.element];
        let targets = [fixture.attributes_reference, fixture.string];
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let aliases = [
            None,
            Some((fixture.outer_aliases[0], &[][..])),
            Some((fixture.outer_aliases[1], &[][..])),
        ];
        let mut results = Vec::new();
        for alias in aliases {
            let before = deferred_intersection_store_state(&fixture.store);
            assert_eq!(
                cached_instantiation_with_vector(
                    &fixture.store,
                    source,
                    &sources,
                    &targets,
                    None,
                    alias,
                ),
                Ok(None)
            );
            assert_eq!(deferred_intersection_store_state(&fixture.store), before);
            let aliases_before = fixture.store.type_alias_len();
            let result = instantiate_type_with_vector_and_alias_and_session(
                &mut fixture.store,
                source,
                &sources,
                &targets,
                None,
                alias,
                &mut session,
            )
            .unwrap();
            assert_eq!(
                fixture.store.type_alias_len(),
                aliases_before + 1,
                "only the canonical result allocates an alias record"
            );
            let projection = fixture
                .store
                .validate_deferred_intersection_type(result)
                .unwrap();
            assert_eq!(
                projection.alias_symbol,
                Some(alias.map_or(fixture.alias, |(owner, _)| owner))
            );
            assert_eq!(
                projection.alias_arguments,
                alias.map_or_else(|| targets.to_vec(), |(_, arguments)| arguments.to_vec())
            );
            assert_eq!(projection.types[1], fixture.attributes_reference);
            let before = deferred_intersection_store_state(&fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    cached_instantiation_with_vector(
                        &fixture.store,
                        source,
                        &sources,
                        &targets,
                        None,
                        alias,
                    ),
                    Ok(Some(result))
                );
                assert_eq!(
                    instantiate_type_with_vector_and_alias_and_session(
                        &mut fixture.store,
                        source,
                        &sources,
                        &targets,
                        None,
                        alias,
                        &mut session,
                    ),
                    Ok(result)
                );
            }
            assert_eq!(deferred_intersection_store_state(&fixture.store), before);
            assert!(!results.contains(&result));
            results.push(result);
        }
        assert_eq!(session.depth, 0);
        assert!(session.active_mappers.is_empty());
    }

    #[test]
    fn deferred_intersection_alias_override_keeps_go_identity_mapper_rule() {
        let mut fixture = deferred_generic_intersection_fixture();
        let source = fixture.intersection;
        let arguments = [fixture.props, fixture.element];
        let alias = Some((fixture.outer_aliases[0], &[][..]));
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        assert_eq!(
            cached_instantiation_with_vector(
                &fixture.store,
                source,
                &arguments,
                &arguments,
                None,
                alias,
            ),
            Ok(None)
        );
        let renamed = instantiate_type_with_vector_and_alias_and_session(
            &mut fixture.store,
            source,
            &arguments,
            &arguments,
            None,
            alias,
            &mut session,
        )
        .unwrap();
        assert_ne!(renamed, source);
        let original = fixture
            .store
            .validate_deferred_intersection_type(source)
            .unwrap();
        let projection = fixture
            .store
            .validate_deferred_intersection_type(renamed)
            .unwrap();
        assert_eq!(projection.types, original.types);
        assert_eq!(projection.alias_symbol, Some(fixture.outer_aliases[0]));
        assert!(projection.alias_arguments.is_empty());
        assert_eq!(
            cached_instantiation_with_vector(
                &fixture.store,
                source,
                &arguments,
                &arguments,
                None,
                alias,
            ),
            Ok(Some(renamed))
        );

        // Pinned Go tests the override symbol before reading its argument slice.
        let different_arguments = [fixture.string, fixture.attributes_reference];
        let same_owner = Some((fixture.alias, different_arguments.as_slice()));
        let before = deferred_intersection_store_state(&fixture.store);
        assert_eq!(
            instantiate_type_with_vector_and_alias_and_session(
                &mut fixture.store,
                source,
                &arguments,
                &arguments,
                None,
                same_owner,
                &mut session,
            ),
            Ok(source)
        );
        assert_eq!(
            cached_instantiation_with_vector(
                &fixture.store,
                source,
                &arguments,
                &arguments,
                None,
                same_owner,
            ),
            Ok(Some(source))
        );
        assert_eq!(deferred_intersection_store_state(&fixture.store), before);
    }

    #[test]
    fn deferred_intersection_alias_override_does_not_remap_borrowed_arguments() {
        let mut fixture = deferred_generic_intersection_fixture();
        let source = fixture.intersection;
        let arguments = fixture.outer_parameters;
        let sources = [fixture.props, fixture.element, arguments[0], arguments[1]];
        let targets = [
            fixture.attributes_reference,
            fixture.string,
            fixture.string,
            fixture.attributes_reference,
        ];
        let alias = Some((fixture.argument_alias, arguments.as_slice()));
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 10,
            max_count: 4,
        });
        let mark = session.limit_event_mark();
        let aliases_before = fixture.store.type_alias_len();
        let mappers_before = fixture.store.mapper_len();
        let result = instantiate_type_with_vector_and_alias_and_session(
            &mut fixture.store,
            source,
            &sources,
            &targets,
            None,
            alias,
            &mut session,
        )
        .unwrap();
        assert_eq!(fixture.store.type_alias_len(), aliases_before + 1);
        assert_eq!(fixture.store.mapper_len(), mappers_before);
        assert_eq!(
            session.query_count(),
            4,
            "the root, reference, T, and E are the only charged substitutions"
        );
        assert!(!session.limit_event_occurred_since(mark));
        let projection = fixture
            .store
            .validate_deferred_intersection_type(result)
            .unwrap();
        assert_eq!(projection.alias_symbol, Some(fixture.argument_alias));
        assert_eq!(projection.alias_arguments, arguments);
        assert_eq!(projection.types[1], fixture.attributes_reference);
        assert_eq!(
            validate_direct_generic_reference(&fixture.store, projection.types[0])
                .unwrap()
                .type_arguments,
            [fixture.string]
        );
        let before = deferred_intersection_store_state(&fixture.store);
        assert_eq!(
            cached_instantiation_with_vector(
                &fixture.store,
                source,
                &sources,
                &targets,
                None,
                alias,
            ),
            Ok(Some(result))
        );
        assert_eq!(deferred_intersection_store_state(&fixture.store), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each mutation checks the same expected intersection identity.
    fn cached_deferred_intersection_alias_overrides_reject_interner_and_alias_damage() {
        let mut fixture = deferred_generic_intersection_fixture();
        let source = fixture.intersection;
        let sources = [fixture.props, fixture.element];
        let targets = [fixture.attributes_reference, fixture.string];
        let arguments = fixture.outer_parameters;
        let alias = Some((fixture.argument_alias, arguments.as_slice()));
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let result = instantiate_type_with_vector_and_alias_and_session(
            &mut fixture.store,
            source,
            &sources,
            &targets,
            None,
            alias,
            &mut session,
        )
        .unwrap();
        let other = instantiate_type_with_vector_and_alias_and_session(
            &mut fixture.store,
            source,
            &sources,
            &targets,
            None,
            Some((fixture.outer_aliases[0], &[])),
            &mut session,
        )
        .unwrap();
        let key = fixture
            .store
            .intersection_keys_by_type
            .get(&result)
            .unwrap()
            .clone();
        let other_key = fixture
            .store
            .intersection_keys_by_type
            .get(&other)
            .unwrap()
            .clone();
        let identity = fixture.store.type_payload(result).unwrap().alias().unwrap();
        let other_identity = fixture.store.type_payload(other).unwrap().alias().unwrap();
        let flags = fixture.store.type_payload(result).unwrap().object_flags();
        let assert_rejected = |store: &CanonicalTypeMapperStore| {
            let before = deferred_intersection_store_state(store);
            let forward = store.intersection_types.clone();
            let reverse = store.intersection_keys_by_type.clone();
            assert!(
                cached_instantiation_with_vector(store, source, &sources, &targets, None, alias,)
                    .is_err()
            );
            assert_eq!(deferred_intersection_store_state(store), before);
            assert_eq!(store.intersection_types, forward);
            assert_eq!(store.intersection_keys_by_type, reverse);
        };

        assert_eq!(fixture.store.intersection_types.remove(&key), Some(result));
        assert_rejected(&fixture.store);
        assert!(
            fixture
                .store
                .intersection_types
                .insert(key.clone(), result)
                .is_none()
        );
        assert_eq!(
            fixture.store.intersection_keys_by_type.remove(&result),
            Some(key.clone())
        );
        assert_rejected(&fixture.store);
        assert!(
            fixture
                .store
                .intersection_keys_by_type
                .insert(result, key.clone())
                .is_none()
        );

        assert_eq!(
            fixture.store.intersection_types.insert(key.clone(), other),
            Some(result)
        );
        assert_rejected(&fixture.store);
        assert_eq!(
            fixture.store.intersection_types.insert(key.clone(), result),
            Some(other)
        );
        assert_eq!(
            fixture
                .store
                .intersection_keys_by_type
                .insert(result, other_key.clone()),
            Some(key.clone())
        );
        assert_rejected(&fixture.store);
        assert_eq!(
            fixture
                .store
                .intersection_keys_by_type
                .insert(result, key.clone()),
            Some(other_key)
        );

        assert!(
            fixture
                .store
                .set_type_alias_arguments(identity, Some(vec![arguments[1], arguments[0]]))
        );
        assert_rejected(&fixture.store);
        assert!(
            fixture
                .store
                .set_type_alias_arguments(identity, Some(arguments.to_vec()))
        );
        assert!(fixture.store.set_type_alias(result, Some(other_identity)));
        assert_rejected(&fixture.store);
        assert!(fixture.store.set_type_alias(result, Some(identity)));

        assert!(
            fixture
                .store
                .set_type_object_flags(result, flags | ObjectFlags::MEMBERS_RESOLVED)
        );
        assert_rejected(&fixture.store);
        assert!(fixture.store.set_type_object_flags(result, flags));
        assert!(fixture.store.set_union_or_intersection_caches(
            result,
            None,
            None,
            Some(Vec::new())
        ));
        assert_rejected(&fixture.store);
        assert!(
            fixture
                .store
                .set_union_or_intersection_caches(result, None, None, None)
        );
        assert_eq!(
            cached_instantiation_with_vector(
                &fixture.store,
                source,
                &sources,
                &targets,
                None,
                alias,
            ),
            Ok(Some(result))
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check flattening, collapse, and the surviving reference cache together.
    fn cached_deferred_intersections_flatten_and_validate_collapsed_references() {
        let mut fixture = deferred_generic_intersection_fixture();
        let source = fixture.intersection;
        let sources = [fixture.props, fixture.element];
        let targets = [fixture.attributes_reference, fixture.string];
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let inner = instantiate_type_with_vector_and_alias_and_session(
            &mut fixture.store,
            source,
            &sources,
            &targets,
            None,
            Some((fixture.outer_aliases[1], &[])),
            &mut session,
        )
        .unwrap();
        let inner_projection = fixture
            .store
            .validate_deferred_intersection_type(inner)
            .unwrap();
        let class = inner_projection.types[0];
        let alias = Some((fixture.outer_aliases[0], &[][..]));
        let nested_targets = [inner, fixture.string];
        let flattened = instantiate_type_with_vector_and_alias_and_session(
            &mut fixture.store,
            source,
            &sources,
            &nested_targets,
            None,
            alias,
            &mut session,
        )
        .unwrap();
        let projection = fixture
            .store
            .validate_deferred_intersection_type(flattened)
            .unwrap();
        assert_eq!(projection.types, inner_projection.types);
        assert_eq!(projection.alias_symbol, Some(fixture.outer_aliases[0]));
        assert_eq!(
            cached_instantiation_with_vector(
                &fixture.store,
                source,
                &sources,
                &nested_targets,
                None,
                alias,
            ),
            Ok(Some(flattened))
        );

        let collapsed_targets = [class, fixture.string];
        let before = deferred_intersection_store_state(&fixture.store);
        assert_eq!(
            cached_instantiation_with_vector(
                &fixture.store,
                source,
                &sources,
                &collapsed_targets,
                None,
                alias,
            ),
            Ok(Some(class))
        );
        assert_eq!(
            instantiate_type_with_vector_and_alias_and_session(
                &mut fixture.store,
                source,
                &sources,
                &collapsed_targets,
                None,
                alias,
                &mut session,
            ),
            Ok(class)
        );
        assert!(fixture.store.type_payload(class).unwrap().alias().is_none());
        assert_eq!(deferred_intersection_store_state(&fixture.store), before);

        let flags = fixture.store.type_payload(class).unwrap().object_flags();
        assert!(fixture.store.set_structured_type_members(
            class,
            None,
            Some(vec![fixture.alias]),
            None,
            None,
            None,
        ));
        let damaged = deferred_intersection_store_state(&fixture.store);
        assert!(
            cached_instantiation_with_vector(
                &fixture.store,
                source,
                &sources,
                &collapsed_targets,
                None,
                alias,
            )
            .is_err()
        );
        assert_eq!(deferred_intersection_store_state(&fixture.store), damaged);
        assert!(
            fixture
                .store
                .set_structured_type_members(class, None, None, None, None, None)
        );
        assert!(fixture.store.set_type_object_flags(class, flags));
        assert_eq!(
            cached_instantiation_with_vector(
                &fixture.store,
                source,
                &sources,
                &collapsed_targets,
                None,
                alias,
            ),
            Ok(Some(class))
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Validate resolved intersections and their surviving reference cache together.
    fn cached_deferred_intersections_preserve_resolved_members_and_reject_warm_damage() {
        let parsed = parse_source_file(concat!(
            "interface ClassAttributes<T> { ref: T }\n",
            "interface HTMLAttributes<T> { value: T }\n",
            "type Left = ClassAttributes<string>;\n",
            "type Right = HTMLAttributes<string>;\n",
        ));
        let template = parse_source_file(concat!(
            "type DetailedHTMLProps<E, T> = ClassAttributes<T> & E;\n",
            "type Probe = unknown;\n",
        ));
        let mut fixture = nonempty_deferred_generic_intersection_fixture(&parsed, &template);
        let source = fixture.intersection;
        let sources = fixture.sources;
        let targets = fixture.targets;
        let owner = fixture.owner;
        let alias = Some((owner, &[][..]));
        let store = fixture.context.store_mut_for_test();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let result = instantiate_type_with_vector_and_alias_and_session(
            store,
            source,
            &sources,
            &targets,
            None,
            alias,
            &mut session,
        )
        .unwrap();
        let constituents = store
            .validate_deferred_intersection_type(result)
            .unwrap()
            .types;
        assert_eq!(constituents.len(), 2);
        for (reference, name) in constituents.iter().zip(["ref", "value"]) {
            let property = store
                .resolve_generic_interface_property(*reference, name, None)
                .unwrap()
                .unwrap();
            assert_eq!(property.type_id(), targets[1]);
        }
        assert_eq!(
            store.canonical_intersection_type(&constituents, Some(owner)),
            Ok(result)
        );
        let resolved = store.validate_intersection_type(result).unwrap();
        assert_eq!(resolved.properties.len(), 2);
        assert!(store.validate_deferred_intersection_type(result).is_err());
        let class = constituents[0];
        let collapsed_targets = [class, targets[1]];
        let before = deferred_intersection_store_state(store);
        for (arguments, expected) in [(&targets, result), (&collapsed_targets, class)] {
            assert_eq!(
                cached_instantiation_with_vector(store, source, &sources, arguments, None, alias,),
                Ok(Some(expected))
            );
        }
        assert_eq!(deferred_intersection_store_state(store), before);

        assert!(store.set_union_or_intersection_caches(result, Some(resolved.members), None, None));
        let damaged = deferred_intersection_store_state(store);
        assert!(
            cached_instantiation_with_vector(store, source, &sources, &targets, None, alias,)
                .is_err()
        );
        assert_eq!(deferred_intersection_store_state(store), damaged);
        assert!(store.set_union_or_intersection_caches(
            result,
            Some(resolved.members),
            None,
            Some(resolved.properties),
        ));

        let original = store
            .type_payload(class)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .clone();
        assert!(original.signatures.is_none());
        assert_eq!(original.call_signature_count, 0);
        assert!(store.set_structured_type_members(
            class,
            None,
            Some(vec![fixture.source_alias]),
            None,
            None,
            None,
        ));
        let damaged = deferred_intersection_store_state(store);
        for arguments in [&targets, &collapsed_targets] {
            assert!(
                cached_instantiation_with_vector(store, source, &sources, arguments, None, alias,)
                    .is_err()
            );
        }
        assert_eq!(deferred_intersection_store_state(store), damaged);
        assert!(store.set_structured_type_members(
            class,
            original.members,
            original.properties,
            None,
            None,
            original.index_infos,
        ));
        for (arguments, expected) in [(&targets, result), (&collapsed_targets, class)] {
            assert_eq!(
                cached_instantiation_with_vector(store, source, &sources, arguments, None, alias,),
                Ok(Some(expected))
            );
        }
    }

    #[test]
    fn empty_generic_deferred_intersection_materialization_is_unsupported_without_writes() {
        let mut fixture = deferred_generic_intersection_fixture();
        let owner = fixture.outer_aliases[0];
        let result = instantiate_type_with_vector_and_alias_and_session(
            &mut fixture.store,
            fixture.intersection,
            &[fixture.props, fixture.element],
            &[fixture.attributes_reference, fixture.string],
            None,
            Some((owner, &[])),
            &mut InstantiationSession::new(InstantiationLimits::default()),
        )
        .unwrap();
        let constituents = fixture
            .store
            .validate_deferred_intersection_type(result)
            .unwrap()
            .types;
        for reference in &constituents {
            let target = validate_direct_generic_reference(&fixture.store, *reference)
                .unwrap()
                .target;
            assert!(fixture.store.publish_interface_no_base_resolution(target));
            assert!(
                fixture
                    .store
                    .set_interface_declared_members(target, true, None, None, None, None)
            );
            let members = fixture
                .store
                .resolve_generic_interface_members(*reference, None)
                .unwrap();
            assert!(members.properties().is_empty());
            assert!(members.mapper().is_none());
        }
        let before = deferred_intersection_store_state(&fixture.store);
        let forward = fixture.store.intersection_types.clone();
        let reverse = fixture.store.intersection_keys_by_type.clone();
        let record_state = |store: &CanonicalTypeMapperStore| {
            let record = store.type_payload(result).unwrap();
            let TypeData::Intersection(data) = record.data() else {
                panic!("unsupported materialization must retain its intersection record")
            };
            (
                record.flags(),
                record.object_flags(),
                record.symbol(),
                record.alias(),
                data.clone(),
            )
        };
        let record = record_state(&fixture.store);
        for _ in 0..2 {
            assert_eq!(
                fixture
                    .store
                    .canonical_intersection_type(&constituents, Some(owner)),
                Err(IntersectionTypeError::UnsupportedConstituent(
                    constituents[0]
                ))
            );
            assert_eq!(deferred_intersection_store_state(&fixture.store), before);
            assert_eq!(fixture.store.intersection_types, forward);
            assert_eq!(fixture.store.intersection_keys_by_type, reverse);
            assert_eq!(record_state(&fixture.store), record);
        }
    }

    #[test]
    fn canonical_empty_type_literal_identity_rejects_incomplete_object_or_symbol_state() {
        for poison_symbol in [false, true] {
            let mut store = initialized_store();
            let (empty_object, string) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.empty_type_literal_type, bootstrap.string_type)
            };
            assert_eq!(
                could_contain_installed_type_variables(&store, empty_object, None),
                Ok(false),
            );
            if poison_symbol {
                assert!(store.set_type_symbol(empty_object, None));
            } else {
                assert!(store.set_resolved_base_constraint(empty_object, Some(string)));
            }
            assert_eq!(
                could_contain_installed_type_variables(&store, empty_object, None),
                Err(InstantiationError::UnsupportedType(empty_object)),
            );
        }
    }

    #[test]
    fn forged_deferred_generic_intersections_fail_before_semantic_writes() {
        for forge_alias in [false, true] {
            let mut fixture = deferred_generic_intersection_fixture();
            let source = fixture.intersection;
            let sources = [fixture.props, fixture.element];
            let targets = [fixture.attributes_reference, fixture.string];
            if forge_alias {
                let identity = fixture.store.type_payload(source).unwrap().alias().unwrap();
                assert!(fixture.store.set_type_alias_arguments(
                    identity,
                    Some(vec![fixture.element, fixture.props]),
                ));
            } else {
                assert!(fixture.store.set_type_reference_resolution(
                    fixture.class_reference,
                    None,
                    Some(vec![fixture.string]),
                ));
            }
            let before = deferred_intersection_store_state(&fixture.store);

            assert_eq!(
                instantiate_type_with_vector(&mut fixture.store, source, &sources, &targets),
                Err(InstantiationError::InvalidType(source)),
            );
            assert_eq!(deferred_intersection_store_state(&fixture.store), before);
        }
    }

    #[test]
    fn instantiates_template_literals_to_canonical_string_identities() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let value = store
            .get_template_literal_type(&["value".to_owned()], &[])
            .unwrap();
        let expected = store
            .get_template_literal_type(&["before-value-after".to_owned()], &[])
            .unwrap();
        let template = store
            .get_template_literal_type(&["before-".to_owned(), "-after".to_owned()], &[parameter])
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, value).unwrap();

        assert_eq!(instantiate_type(&mut store, template, mapper), Ok(expected));
        assert_eq!(
            instantiate_type_with_vector(&mut store, template, &[parameter], &[value]),
            Ok(expected)
        );
    }

    #[test]
    fn instantiates_template_literals_distributively_over_mapped_unions() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let first = store
            .get_template_literal_type(&["first".to_owned()], &[])
            .unwrap();
        let second = store
            .get_template_literal_type(&["second".to_owned()], &[])
            .unwrap();
        let replacement = canonical_anonymous_union(&mut store, &[first, second]).unwrap();
        let template = store
            .get_template_literal_type(&["id-".to_owned(), String::new()], &[parameter])
            .unwrap();
        let mapper = store
            .new_simple_type_mapper(parameter, replacement)
            .unwrap();

        let result = instantiate_type(&mut store, template, mapper).unwrap();
        let TypeData::Union(union) = store.type_payload(result).unwrap().data() else {
            panic!("a union replacement must distribute through the template")
        };
        let values = union
            .union
            .types
            .iter()
            .map(|type_| match store.type_payload(*type_).unwrap().data() {
                TypeData::Literal(literal) => match &literal.value {
                    LiteralValue::String(value) => value.as_str(),
                    _ => panic!("distributed templates must produce string literals"),
                },
                _ => panic!("distributed templates must produce string literals"),
            })
            .collect::<Vec<_>>();
        assert_eq!(values, ["id-first", "id-second"]);
    }

    #[test]
    fn instantiates_template_literals_with_utf16_surrogate_boundaries() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let high = encode_js_string(&JsString::from_units(vec![0xd83d]));
        let low = encode_js_string(&JsString::from_units(vec![0xde00]));
        let replacement = store.get_template_literal_type(&[low], &[]).unwrap();
        let expected = store
            .get_template_literal_type(&["\u{1f600}".to_owned()], &[])
            .unwrap();
        let template = store
            .get_template_literal_type(&[high, String::new()], &[parameter])
            .unwrap();
        let mapper = store
            .new_simple_type_mapper(parameter, replacement)
            .unwrap();

        let result = instantiate_type(&mut store, template, mapper).unwrap();
        assert_eq!(result, expected);
        let TypeData::Literal(literal) = store.type_payload(result).unwrap().data() else {
            panic!("the instantiated surrogate pair must become a string literal")
        };
        let LiteralValue::String(value) = &literal.value else {
            panic!("the instantiated surrogate pair must become a string literal")
        };
        assert_eq!(decode_js_string(value).as_units(), &[0xd83d, 0xde00]);
    }

    #[test]
    fn instantiates_intrinsic_string_mappings_and_nested_templates() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Uppercase"),
            ))
            .unwrap();
        let value = store
            .get_template_literal_type(&["\u{00df}foo".to_owned()], &[])
            .unwrap();
        let expected = store
            .get_template_literal_type(&["SSFOO".to_owned()], &[])
            .unwrap();
        let mapping = store.get_string_mapping_type(symbol, parameter).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, value).unwrap();

        assert_eq!(instantiate_type(&mut store, mapping, mapper), Ok(expected));

        let nested = store
            .get_template_literal_type(&["value:".to_owned(), String::new()], &[mapping])
            .unwrap();
        let nested_expected = store
            .get_template_literal_type(&["value:SSFOO".to_owned()], &[])
            .unwrap();
        assert_eq!(
            instantiate_type(&mut store, nested, mapper),
            Ok(nested_expected)
        );
    }

    #[test]
    fn unchanged_template_and_string_mapping_instantiations_preserve_identity() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let unrelated = store.alloc_type_parameter(None).unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Lowercase"),
            ))
            .unwrap();
        let template = store
            .get_template_literal_type(&["prefix".to_owned(), String::new()], &[parameter])
            .unwrap();
        let mapping = store.get_string_mapping_type(symbol, parameter).unwrap();
        let mapper = store.new_simple_type_mapper(unrelated, string).unwrap();
        let before = store.type_len();

        assert_eq!(instantiate_type(&mut store, template, mapper), Ok(template));
        assert_eq!(instantiate_type(&mut store, mapping, mapper), Ok(mapping));
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn concrete_named_unions_preserve_identity_without_consuming_instantiation_limits() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Named"),
            ))
            .unwrap();
        let union = store
            .literal_union_type_with_alias_and_array_targets(
                &[string, number],
                Some((symbol, &[])),
                None,
            )
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 0,
            max_count: 0,
        });

        assert_eq!(
            validate_instantiable_member_type(&store, union, &[parameter], None),
            Ok(())
        );
        assert_eq!(
            instantiate_type_with_session(&mut store, union, mapper, None, &mut session),
            Ok(union)
        );
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 0);
        assert_eq!(
            instantiated_member_type_matches(&store, union, union, mapper, None),
            Ok(true)
        );
    }

    #[test]
    fn template_and_mapping_member_types_validate_and_replay_without_allocating() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let replacement = store
            .get_template_literal_type(&["value".to_owned()], &[])
            .unwrap();
        let unexpected = store
            .get_template_literal_type(&["different".to_owned()], &[])
            .unwrap();
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Uppercase"),
            ))
            .unwrap();
        let template = store
            .get_template_literal_type(&["prefix-".to_owned(), String::new()], &[parameter])
            .unwrap();
        let mapping = store.get_string_mapping_type(symbol, parameter).unwrap();
        let mapper = store
            .new_simple_type_mapper(parameter, replacement)
            .unwrap();

        for source in [template, mapping] {
            assert_eq!(
                validate_instantiable_member_type(&store, source, &[parameter], None),
                Ok(())
            );
            assert_eq!(
                instantiable_member_type_contains_variables(&store, source, &[parameter], None),
                Ok(true)
            );
            let result = instantiate_type(&mut store, source, mapper).unwrap();
            let count = store.type_len();
            assert_eq!(
                instantiated_member_type_matches(&store, source, result, mapper, None),
                Ok(true)
            );
            assert_eq!(
                instantiated_member_type_matches(&store, source, unexpected, mapper, None),
                Ok(false)
            );
            assert_eq!(store.type_len(), count);
        }
    }

    #[test]
    fn template_union_member_types_replay_their_cached_distributed_identity() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let replacement = store
            .get_template_literal_type(&["value".to_owned()], &[])
            .unwrap();
        let first = store
            .get_template_literal_type(&["a-".to_owned(), String::new()], &[parameter])
            .unwrap();
        let second = store
            .get_template_literal_type(&["b-".to_owned(), String::new()], &[parameter])
            .unwrap();
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![first, second])
            .unwrap();
        let mapper = store
            .new_simple_type_mapper(parameter, replacement)
            .unwrap();

        assert_eq!(
            validate_instantiable_member_type(&store, union, &[parameter], None),
            Ok(())
        );
        let result = instantiate_type(&mut store, union, mapper).unwrap();
        let count = store.type_len();
        assert_eq!(
            instantiated_member_type_matches(&store, union, result, mapper, None),
            Ok(true)
        );
        assert_eq!(store.type_len(), count);
    }

    #[test]
    fn dependent_generic_defaults_substitute_templates_and_intrinsic_mappings() {
        let mut store = initialized_store();
        let first = store.alloc_type_parameter(None).unwrap();
        let second = store.alloc_type_parameter(None).unwrap();
        let provided = store
            .get_template_literal_type(&["value".to_owned()], &[])
            .unwrap();
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Uppercase"),
            ))
            .unwrap();
        let second_default = store.get_string_mapping_type(symbol, first).unwrap();
        let outer_default = store
            .get_template_literal_type(
                &[String::new(), "-".to_owned(), String::new()],
                &[first, second],
            )
            .unwrap();

        let resolved_second =
            instantiate_type_with_vector(&mut store, second_default, &[first], &[provided])
                .unwrap();
        let resolved_outer = instantiate_type_with_vector(
            &mut store,
            outer_default,
            &[first, second],
            &[provided, resolved_second],
        )
        .unwrap();

        let Some(TypeData::Literal(result)) =
            store.type_payload(resolved_outer).map(TypeRecord::data)
        else {
            panic!("dependent defaults must resolve to a canonical string literal")
        };
        assert_eq!(result.value, LiteralValue::String("value-VALUE".to_owned()));
    }

    #[test]
    fn broad_string_removes_instantiated_template_union_constituents() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let template = store
            .get_template_literal_type(&["prefix-".to_owned(), String::new()], &[parameter])
            .unwrap();
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![string, template])
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();

        assert_eq!(
            validate_instantiable_member_type(&store, union, &[parameter], None),
            Ok(())
        );
        assert_eq!(instantiate_type(&mut store, union, mapper), Ok(string));
        let count = store.type_len();
        assert_eq!(
            instantiated_member_type_matches(&store, union, string, mapper, None),
            Ok(true)
        );
        assert_eq!(store.type_len(), count);
    }

    #[test]
    fn template_instantiation_reports_cross_product_overflow_without_allocating() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let values = (0..10)
            .map(|index| {
                store
                    .get_template_literal_type(&[index.to_string()], &[])
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let replacement = canonical_anonymous_union(&mut store, &values).unwrap();
        let template = store
            .get_template_literal_type(&vec![String::new(); 6], &[parameter; 5])
            .unwrap();
        let mapper = store
            .new_simple_type_mapper(parameter, replacement)
            .unwrap();
        let before = store.type_len();

        assert_eq!(
            instantiate_type(&mut store, template, mapper),
            Err(InstantiationError::Template(
                TemplateTypeError::CrossProductTooLarge {
                    size: MAX_TEMPLATE_UNION_SIZE,
                    limit: MAX_TEMPLATE_UNION_SIZE,
                }
            ))
        );
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn instantiates_unions_containing_generic_template_literals() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let value = store
            .get_template_literal_type(&["value".to_owned()], &[])
            .unwrap();
        let first = store
            .get_template_literal_type(&["a-".to_owned(), String::new()], &[parameter])
            .unwrap();
        let second = store
            .get_template_literal_type(&["b-".to_owned(), String::new()], &[parameter])
            .unwrap();
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![first, second])
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, value).unwrap();

        let result = instantiate_type(&mut store, union, mapper).unwrap();
        let TypeData::Union(union) = store.type_payload(result).unwrap().data() else {
            panic!("different instantiated templates must remain a union")
        };
        let values = union
            .union
            .types
            .iter()
            .map(|type_| match store.type_payload(*type_).unwrap().data() {
                TypeData::Literal(literal) => match &literal.value {
                    LiteralValue::String(value) => value.as_str(),
                    _ => panic!("instantiated templates must produce string literals"),
                },
                _ => panic!("instantiated templates must produce string literals"),
            })
            .collect::<Vec<_>>();
        assert_eq!(values, ["a-value", "b-value"]);
    }

    #[test]
    fn instantiates_anonymous_union_with_literal_reduction() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, string])
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();

        let result = instantiate_type(&mut store, source, mapper).unwrap();
        let TypeData::Union(data) = store.type_payload(result).unwrap().data() else {
            panic!("two primitive constituents must remain a union");
        };
        assert_eq!(data.union.types, [string, number]);
    }

    #[test]
    fn deferred_indexed_access_substitution_retains_array_targets_for_cache_checks() {
        let mut store = initialized_store();
        let targets = canonical_array_targets(&mut store);
        let (number, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let source_parameter = store.alloc_type_parameter(None).unwrap();
        let indexed = get_instantiated_indexed_access_type(
            &mut store,
            source_parameter,
            number,
            AccessFlags::NONE,
        )
        .unwrap();
        for readonly in [false, true] {
            let array = store
                .create_canonical_array_type_with_targets(targets, string, readonly)
                .unwrap();
            let mapper = store
                .new_simple_type_mapper(source_parameter, array)
                .unwrap();
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            assert_eq!(
                instantiate_type_with_session(
                    &mut store,
                    indexed,
                    mapper,
                    Some(targets),
                    &mut session
                ),
                Ok(string)
            );
            let warm = deferred_intersection_store_state(&store);
            assert_eq!(
                instantiated_member_type_matches(&store, indexed, string, mapper, Some(targets)),
                Ok(true)
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    &store,
                    indexed,
                    &[source_parameter],
                    &[array],
                    Some(targets),
                    None,
                ),
                Ok(Some(string))
            );
            assert_eq!(deferred_intersection_store_state(&store), warm);
        }
    }

    #[test]
    fn composite_mapper_recursively_instantiates_a_changed_intermediate() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let outer = store.alloc_type_parameter(None).unwrap();
        let inner = store.alloc_type_parameter(None).unwrap();
        let intermediate = store
            .alloc_union_type(ObjectFlags::NONE, vec![inner, string])
            .unwrap();
        let first = store.new_simple_type_mapper(outer, intermediate).unwrap();
        let second = store.new_simple_type_mapper(inner, number).unwrap();
        let merged = store.merge_type_mappers(Some(first), second).unwrap();
        let composite = store.combine_type_mappers(Some(first), second).unwrap();

        assert_eq!(
            instantiate_type(&mut store, outer, merged),
            Ok(intermediate)
        );
        let instantiated = instantiate_type(&mut store, outer, composite).unwrap();
        let TypeData::Union(data) = store.type_payload(instantiated).unwrap().data() else {
            panic!("the recursively instantiated intermediate must remain a union");
        };
        assert_eq!(data.union.types, [string, number]);
        assert_eq!(
            instantiated_member_type_matches(&store, outer, intermediate, merged, None),
            Ok(true)
        );
        assert_eq!(
            instantiated_member_type_matches(&store, outer, instantiated, composite, None),
            Ok(true)
        );
        assert_eq!(
            instantiated_member_type_matches(&store, outer, intermediate, composite, None),
            Ok(false)
        );
    }

    #[test]
    fn composite_mapper_maps_unchanged_inputs_and_nested_composites_exactly() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let outer = store.alloc_type_parameter(None).unwrap();
        let untouched = store.alloc_type_parameter(None).unwrap();
        let inner = store.alloc_type_parameter(None).unwrap();
        let leaf = store.alloc_type_parameter(None).unwrap();
        let intermediate = store
            .alloc_union_type(ObjectFlags::NONE, vec![inner, string])
            .unwrap();

        let first = store.new_simple_type_mapper(outer, intermediate).unwrap();
        let unchanged_second = store.new_simple_type_mapper(untouched, number).unwrap();
        let unchanged = store
            .combine_type_mappers(Some(first), unchanged_second)
            .unwrap();
        assert_eq!(
            instantiate_type(&mut store, untouched, unchanged),
            Ok(number)
        );

        let inner_to_leaf = store.new_simple_type_mapper(inner, leaf).unwrap();
        let leaf_to_number = store.new_simple_type_mapper(leaf, number).unwrap();
        let nested_second = store
            .combine_type_mappers(Some(inner_to_leaf), leaf_to_number)
            .unwrap();
        let nested = store
            .combine_type_mappers(Some(first), nested_second)
            .unwrap();
        let instantiated = instantiate_type(&mut store, outer, nested).unwrap();
        let TypeData::Union(data) = store.type_payload(instantiated).unwrap().data() else {
            panic!("nested composites must recursively instantiate the union")
        };
        assert_eq!(data.union.types, [string, number]);
        assert_eq!(
            instantiated_member_type_matches(&store, untouched, number, unchanged, None),
            Ok(true)
        );
        assert_eq!(
            instantiated_member_type_matches(&store, outer, instantiated, nested, None),
            Ok(true)
        );
    }

    #[test]
    fn active_mapper_cache_precedes_instantiation_counter_increment() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, parameter, string])
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 10,
            max_count: 3,
        });

        let result =
            instantiate_type_with_session(&mut store, source, mapper, None, &mut session).unwrap();

        assert_eq!(session.query_count(), 2, "the repeated leaf must hit cache");
        let TypeData::Union(data) = store.type_payload(result).unwrap().data() else {
            panic!("the remaining string and number constituents must form a union");
        };
        assert_eq!(data.union.types, [string, number]);
    }

    #[test]
    fn mapped_template_frames_share_the_vector_cache_with_distinct_optional_keys() {
        let (mut store, template, parameter, number, sentinel) = mapped_frame_fixture();
        let sources = [parameter];
        let targets = [number];
        let optional = store
            .literal_union_type_with_alias_and_array_targets(&[number, sentinel], None, None)
            .unwrap();
        assert_ne!(optional, number);
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        session.active_mappers.push(ActiveMapperFrame {
            mapping: InstantiationMapping::Vector {
                sources: &sources,
                targets: &targets,
            }
            .identity(),
            cache: HashMap::new(),
        });
        let result = with_mapped_template_frame(
            &mut store,
            MappedTemplateFrame::Optional { template, sentinel },
            &sources,
            &targets,
            &mut session,
            std::convert::identity,
            |store, session| {
                let indexed = with_mapped_template_frame(
                    store,
                    MappedTemplateFrame::Indexed(template),
                    &sources,
                    &targets,
                    session,
                    std::convert::identity,
                    |store, session| {
                        instantiate_type_with_vector_and_session(
                            store, parameter, &sources, &targets, None, session,
                        )
                    },
                )?;
                assert_eq!(indexed, number);
                store
                    .literal_union_type_with_alias_and_array_targets(
                        &[indexed, sentinel],
                        None,
                        None,
                    )
                    .map_err(InstantiationError::from)
            },
        );
        assert_eq!(result, Ok(optional));
        assert_eq!(session.query_count(), 3);
        assert_eq!(session.total_count(), 3);
        assert_eq!(session.depth, 0);
        assert_eq!(session.active_mappers.len(), 1);
        assert_eq!(session.active_mappers[0].cache.len(), 3);

        for (frame, expected) in [
            (
                MappedTemplateFrame::Optional { template, sentinel },
                optional,
            ),
            (MappedTemplateFrame::Indexed(template), number),
        ] {
            assert_eq!(
                with_mapped_template_frame(
                    &mut store,
                    frame,
                    &sources,
                    &targets,
                    &mut session,
                    std::convert::identity,
                    |_, _| -> Result<TypeId, InstantiationError> {
                        panic!("the existing frame must return its cached result")
                    },
                ),
                Ok(expected),
            );
        }
        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut store,
                parameter,
                &sources,
                &targets,
                None,
                &mut session,
            ),
            Ok(number),
        );
        assert_eq!(session.query_count(), 3);
        assert_eq!(session.total_count(), 3);
        assert_eq!(session.depth, 0);
    }

    #[test]
    fn mapped_template_frame_limits_precede_cache_hits_and_keep_recovery_uncached() {
        let (mut store, template, parameter, number, sentinel) = mapped_frame_fixture();
        let error_type = store.intrinsic_bootstrap().unwrap().error_type;
        let sources = [parameter];
        let targets = [number];
        for frame in [
            MappedTemplateFrame::Optional { template, sentinel },
            MappedTemplateFrame::Indexed(template),
        ] {
            let key = match frame {
                MappedTemplateFrame::Optional { template, sentinel } => {
                    InstantiationCacheKey::MappedOptional { template, sentinel }
                }
                MappedTemplateFrame::Indexed(template) => {
                    instantiation_cache_key(&store, template, None).unwrap()
                }
            };
            for recovering in [false, true] {
                for (limits, error) in [
                    (
                        InstantiationLimits {
                            max_depth: 0,
                            max_count: 10,
                        },
                        InstantiationError::DepthLimit { depth: 0, limit: 0 },
                    ),
                    (
                        InstantiationLimits {
                            max_depth: 10,
                            max_count: 0,
                        },
                        InstantiationError::CountLimit { count: 0, limit: 0 },
                    ),
                ] {
                    let mut session = if recovering {
                        InstantiationSession::new_recovering(&store, limits, error_type).unwrap()
                    } else {
                        InstantiationSession::new(limits)
                    };
                    session.active_mappers.push(ActiveMapperFrame {
                        mapping: InstantiationMapping::Vector {
                            sources: &sources,
                            targets: &targets,
                        }
                        .identity(),
                        cache: HashMap::from([(key.clone(), number)]),
                    });
                    let mark = session.limit_event_mark();
                    let result = with_mapped_template_frame(
                        &mut store,
                        frame,
                        &sources,
                        &targets,
                        &mut session,
                        std::convert::identity,
                        |_, _| panic!("a guarded frame must not execute work"),
                    );
                    assert_eq!(
                        result,
                        if recovering {
                            Ok(error_type)
                        } else {
                            Err(error)
                        }
                    );
                    assert!(session.limit_event_occurred_since(mark));
                    assert_eq!(session.query_count(), 0);
                    assert_eq!(session.total_count(), 0);
                    assert_eq!(session.depth, 0);
                    assert_eq!(session.active_mappers.len(), 1);
                    assert_eq!(session.active_mappers[0].cache.get(&key), Some(&number));
                }
            }
        }
    }

    #[test]
    fn mapped_template_frames_validate_inputs_without_work() {
        let (mut store, template, parameter, number, _) = mapped_frame_fixture();
        let foreign_store = initialized_store();
        let foreign = foreign_store.intrinsic_bootstrap().unwrap().number_type;
        let sources = [parameter];
        let targets = [number];
        let foreign_endpoints = [foreign];
        let frame = MappedTemplateFrame::Indexed(template);
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let before = (store.type_len(), store.mapper_len());
        let mark = session.limit_event_mark();
        for (frame, sources, targets, invalid) in [
            (frame, sources.as_slice(), &[][..], template),
            (
                frame,
                foreign_endpoints.as_slice(),
                targets.as_slice(),
                foreign,
            ),
            (
                frame,
                sources.as_slice(),
                foreign_endpoints.as_slice(),
                foreign,
            ),
            (
                MappedTemplateFrame::Indexed(foreign),
                sources.as_slice(),
                targets.as_slice(),
                foreign,
            ),
            (
                MappedTemplateFrame::Indexed(number),
                sources.as_slice(),
                targets.as_slice(),
                number,
            ),
            (
                MappedTemplateFrame::Optional {
                    template,
                    sentinel: number,
                },
                sources.as_slice(),
                targets.as_slice(),
                number,
            ),
            (
                MappedTemplateFrame::Optional {
                    template,
                    sentinel: foreign,
                },
                sources.as_slice(),
                targets.as_slice(),
                foreign,
            ),
        ] {
            assert_eq!(
                with_mapped_template_frame(
                    &mut store,
                    frame,
                    sources,
                    targets,
                    &mut session,
                    std::convert::identity,
                    |_, _| panic!("invalid frame inputs must not execute work"),
                ),
                Err(InstantiationError::InvalidType(invalid)),
            );
        }
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 0);
        assert!(!session.limit_event_occurred_since(mark));
        assert_eq!(session.depth, 0);
        assert!(session.active_mappers.is_empty());
        assert_eq!((store.type_len(), store.mapper_len()), before);
    }

    #[test]
    fn mapped_template_frames_unwind_work_errors_without_caching() {
        #[derive(Debug, PartialEq)]
        enum WorkError {
            Instantiation(InstantiationError),
            Work,
        }

        let (mut store, template, parameter, number, sentinel) = mapped_frame_fixture();
        let sources = [parameter];
        let targets = [number];
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let before = (store.type_len(), store.mapper_len());
        for retained_frame in [false, true] {
            if retained_frame {
                session.active_mappers.push(ActiveMapperFrame {
                    mapping: InstantiationMapping::Vector {
                        sources: &sources,
                        targets: &targets,
                    }
                    .identity(),
                    cache: HashMap::new(),
                });
            }
            assert_eq!(
                with_mapped_template_frame(
                    &mut store,
                    MappedTemplateFrame::Optional { template, sentinel },
                    &sources,
                    &targets,
                    &mut session,
                    WorkError::Instantiation,
                    |_, _| Err(WorkError::Work),
                ),
                Err(WorkError::Work),
            );
            assert_eq!(session.depth, 0);
            assert_eq!(session.active_mappers.len(), usize::from(retained_frame));
            assert!(
                session
                    .active_mappers
                    .iter()
                    .all(|frame| frame.cache.is_empty())
            );
        }
        assert_eq!(session.query_count(), 2);
        assert_eq!(session.total_count(), 2);
        assert_eq!((store.type_len(), store.mapper_len()), before);
    }

    #[test]
    fn limit_guard_precedes_an_active_mapper_cache_hit() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let key = InstantiationCacheKey::Type {
            type_: parameter,
            alias: InstantiationAliasCacheKey::None,
        };
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 10,
            max_count: 5,
        });
        session.count = 4;
        session.total_count = 9;
        session.active_mappers.push(ActiveMapperFrame {
            mapping: InstantiationMappingIdentity::Stored(mapper),
            cache: HashMap::from([(key.clone(), number)]),
        });

        let before_hit = session.limit_event_mark();
        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Ok(number),
        );
        assert_eq!(session.query_count(), 4);
        assert_eq!(session.total_count(), 9);
        assert!(!session.limit_event_occurred_since(before_hit));

        session.count = 5;
        let before_first_limit = session.limit_event_mark();
        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Err(InstantiationError::CountLimit { count: 5, limit: 5 }),
        );
        assert!(session.limit_event_occurred_since(before_first_limit));
        assert_eq!(session.query_count(), 5);
        assert_eq!(session.total_count(), 9);
        assert_eq!(session.active_mappers[0].cache.get(&key), Some(&number));

        let before_second_limit = session.limit_event_mark();
        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Err(InstantiationError::CountLimit { count: 5, limit: 5 }),
        );
        assert!(
            session.limit_event_occurred_since(before_second_limit),
            "each limit event must advance the session's monotonic marker",
        );
        assert_eq!(session.query_count(), 5);
        assert_eq!(session.total_count(), 9);
    }

    #[test]
    fn recovering_guard_does_not_cache_the_directly_guarded_key() {
        let mut store = initialized_store();
        let (number, error_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.error_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 10,
                max_count: 0,
            },
            error_type,
        )
        .unwrap();
        session.active_mappers.push(ActiveMapperFrame {
            mapping: InstantiationMappingIdentity::Stored(mapper),
            cache: HashMap::new(),
        });

        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Ok(error_type),
        );
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 0);
        assert_eq!(session.active_mappers.len(), 1);
        assert!(
            session.active_mappers[0].cache.is_empty(),
            "a recovered guard returns before the directly guarded cache key is located",
        );
    }

    #[test]
    fn session_count_resets_only_at_the_explicit_query_boundary() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 10,
            max_count: 1,
        });

        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Ok(number)
        );
        assert_eq!(session.query_count(), 1);
        assert_eq!(session.total_count(), 1);
        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Err(InstantiationError::CountLimit { count: 1, limit: 1 })
        );

        session.reset_query();
        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Ok(number)
        );
        assert_eq!(session.query_count(), 1);
        assert_eq!(session.total_count(), 2);
    }

    #[test]
    fn query_reset_and_cache_clear_preserve_dynamic_mapper_frames() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let key = InstantiationCacheKey::Type {
            type_: parameter,
            alias: InstantiationAliasCacheKey::None,
        };
        let mut cache = HashMap::new();
        cache.insert(key.clone(), number);
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        session.depth = 3;
        session.count = 7;
        session.total_count = 11;
        session.limit_event_generation = 13;
        session.active_mappers.push(ActiveMapperFrame {
            mapping: InstantiationMappingIdentity::Stored(mapper),
            cache,
        });
        let limit_mark = session.limit_event_mark();

        session.reset_query();
        assert_eq!(session.depth, 3);
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 11);
        assert_eq!(session.limit_event_mark(), limit_mark);
        assert_eq!(session.active_mappers.len(), 1);
        assert_eq!(session.active_mappers[0].cache.get(&key), Some(&number));

        session.clear_active_mapper_caches();
        assert_eq!(session.depth, 3);
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 11);
        assert_eq!(session.limit_event_mark(), limit_mark);
        assert_eq!(session.active_mappers.len(), 1);
        assert!(session.active_mappers[0].cache.is_empty());
    }

    #[test]
    fn recovering_limits_retain_the_outer_array_wrapper() {
        let mut store = initialized_store();
        let (number, error_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.error_type)
        };
        let targets = canonical_array_targets(&mut store);
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = store
            .create_canonical_array_type_with_targets(targets, parameter, false)
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();

        for limits in [
            InstantiationLimits {
                max_depth: 1,
                max_count: 10,
            },
            InstantiationLimits {
                max_depth: 10,
                max_count: 1,
            },
        ] {
            let mut session =
                InstantiationSession::new_recovering(&store, limits, error_type).unwrap();
            let mark = session.limit_event_mark();
            let result = instantiate_type_with_session(
                &mut store,
                source,
                mapper,
                Some(targets),
                &mut session,
            )
            .unwrap();

            let recovered = store
                .canonical_array_reference_with_targets(targets, result)
                .unwrap()
                .expect("recovery at the recursive element must retain Array<_>");
            assert_eq!(recovered.element_type, error_type);
            assert!(!recovered.readonly);
            assert_eq!(session.query_count(), 1);
            assert_eq!(session.total_count(), 1);
            assert_eq!(session.depth, 0);
            assert!(session.active_mappers.is_empty());
            assert!(session.limit_event_occurred_since(mark));
        }
    }

    #[test]
    fn recovering_session_rejects_a_foreign_error_type() {
        let store = initialized_store();
        let foreign = initialized_store();
        let foreign_error = foreign.intrinsic_bootstrap().unwrap().error_type;

        assert_eq!(
            InstantiationSession::new_recovering(
                &store,
                InstantiationLimits::default(),
                foreign_error,
            )
            .unwrap_err(),
            InstantiationError::InvalidRecoveryType(foreign_error),
        );
    }

    #[test]
    fn recovering_session_revalidates_error_ownership_against_the_active_store() {
        let first = initialized_store();
        let first_error = first.intrinsic_bootstrap().unwrap().error_type;
        let mut session = InstantiationSession::new_recovering(
            &first,
            InstantiationLimits {
                max_depth: 10,
                max_count: 0,
            },
            first_error,
        )
        .unwrap();

        let mut second = initialized_store();
        let number = second.intrinsic_bootstrap().unwrap().number_type;
        let parameter = second.alloc_type_parameter(None).unwrap();
        let mapper = second.new_simple_type_mapper(parameter, number).unwrap();
        let mark = session.limit_event_mark();

        assert_eq!(
            instantiate_type_with_session(&mut second, parameter, mapper, None, &mut session),
            Err(InstantiationError::InvalidRecoveryType(first_error)),
        );
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 0);
        assert_eq!(session.depth, 0);
        assert!(session.active_mappers.is_empty());
        assert!(session.limit_event_occurred_since(mark));
    }

    #[test]
    fn alias_cache_keys_use_symbol_and_ordered_arguments_not_record_identity() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        let first_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("First"),
            ))
            .unwrap();
        let second_symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Second"),
            ))
            .unwrap();
        let first = store.alloc_type_alias(Some(first_symbol)).unwrap();
        let equivalent = store.alloc_type_alias(Some(first_symbol)).unwrap();
        let different_symbol = store.alloc_type_alias(Some(second_symbol)).unwrap();
        let reversed = store.alloc_type_alias(Some(first_symbol)).unwrap();
        let no_arguments = store.alloc_type_alias(Some(first_symbol)).unwrap();
        let empty_arguments = store.alloc_type_alias(Some(first_symbol)).unwrap();
        for alias in [first, equivalent, different_symbol] {
            assert!(store.set_type_alias_arguments(alias, Some(vec![parameter, number])));
        }
        assert!(store.set_type_alias_arguments(reversed, Some(vec![number, parameter])));
        assert!(store.set_type_alias_arguments(empty_arguments, Some(Vec::new())));

        assert_eq!(
            instantiation_cache_key(&store, number, Some(first)),
            instantiation_cache_key(&store, number, Some(equivalent)),
            "record identity is not part of the pinned alias key",
        );
        assert_ne!(
            instantiation_cache_key(&store, number, Some(first)),
            instantiation_cache_key(&store, number, Some(different_symbol)),
            "alias symbol identity is part of the pinned alias key",
        );
        assert_ne!(
            instantiation_cache_key(&store, number, Some(first)),
            instantiation_cache_key(&store, number, Some(reversed)),
            "type argument order is part of the pinned alias key",
        );
        assert_eq!(
            instantiation_cache_key(&store, number, Some(no_arguments)),
            instantiation_cache_key(&store, number, Some(empty_arguments)),
            "nil and empty argument slices have the same pinned length-and-elements key",
        );

        let old_key = instantiation_cache_key(&store, number, Some(equivalent)).unwrap();
        let cache = HashMap::from([(old_key, parameter)]);
        assert!(store.set_type_alias_arguments(equivalent, Some(vec![number, parameter])));
        let mutated_key = instantiation_cache_key(&store, number, Some(equivalent)).unwrap();
        assert_eq!(
            cache.get(&mutated_key),
            None,
            "a live alias mutation must miss"
        );
    }

    #[test]
    fn borrowed_alias_cache_keys_match_stored_owner_and_ordered_arguments() {
        let mut fixture = deferred_generic_intersection_fixture();
        let source = fixture.intersection;
        let arguments = fixture.outer_parameters;
        let identity = fixture
            .store
            .alloc_type_alias(Some(fixture.argument_alias))
            .unwrap();
        assert!(
            fixture
                .store
                .set_type_alias_arguments(identity, Some(arguments.to_vec()))
        );
        let before = deferred_intersection_store_state(&fixture.store);
        let key = instantiation_cache_key_for_input(
            &fixture.store,
            source,
            Some(InstantiationAliasInput::Borrowed(
                fixture.argument_alias,
                &arguments,
            )),
        )
        .unwrap();
        assert_eq!(
            instantiation_cache_key(&fixture.store, source, Some(identity)),
            Ok(key.clone())
        );
        assert_ne!(
            instantiation_cache_key_for_input(
                &fixture.store,
                source,
                Some(InstantiationAliasInput::Borrowed(
                    fixture.argument_alias,
                    &[arguments[1], arguments[0]]
                )),
            )
            .unwrap(),
            key
        );
        let first = instantiation_cache_key_for_input(
            &fixture.store,
            source,
            Some(InstantiationAliasInput::Borrowed(
                fixture.outer_aliases[0],
                &[],
            )),
        )
        .unwrap();
        let second = instantiation_cache_key_for_input(
            &fixture.store,
            source,
            Some(InstantiationAliasInput::Borrowed(
                fixture.outer_aliases[1],
                &[],
            )),
        )
        .unwrap();
        assert_ne!(first, second);
        assert_ne!(
            first,
            instantiation_cache_key(&fixture.store, source, None).unwrap()
        );
        assert_eq!(deferred_intersection_store_state(&fixture.store), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check cache hits, both guards, and recovery in one active frame.
    fn borrowed_alias_overrides_share_session_cache_and_preserve_limit_guards() {
        let mut fixture = deferred_generic_intersection_fixture();
        let source = fixture.intersection;
        let sources = [fixture.props, fixture.element];
        let targets = [fixture.attributes_reference, fixture.string];
        let alias = Some((fixture.outer_aliases[0], &[][..]));
        let mut preparation = InstantiationSession::new(InstantiationLimits::default());
        let result = instantiate_type_with_vector_and_alias_and_session(
            &mut fixture.store,
            source,
            &sources,
            &targets,
            None,
            alias,
            &mut preparation,
        )
        .unwrap();
        let key = instantiation_cache_key_for_input(
            &fixture.store,
            source,
            Some(InstantiationAliasInput::Borrowed(
                fixture.outer_aliases[0],
                &[],
            )),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 10,
            max_count: 5,
        });
        session.depth = 3;
        session.count = 4;
        session.total_count = 9;
        session.active_mappers.push(ActiveMapperFrame {
            mapping: InstantiationMapping::Vector {
                sources: &sources,
                targets: &targets,
            }
            .identity(),
            cache: HashMap::from([(key.clone(), result)]),
        });
        let before = deferred_intersection_store_state(&fixture.store);
        let mark = session.limit_event_mark();
        assert_eq!(
            instantiate_type_with_vector_and_alias_and_session(
                &mut fixture.store,
                source,
                &sources,
                &targets,
                None,
                alias,
                &mut session,
            ),
            Ok(result)
        );
        assert_eq!(
            (session.depth, session.query_count(), session.total_count()),
            (3, 4, 9)
        );
        assert_eq!(session.limit_event_mark(), mark);
        assert_eq!(deferred_intersection_store_state(&fixture.store), before);

        session.count = 5;
        assert_eq!(
            instantiate_type_with_vector_and_alias_and_session(
                &mut fixture.store,
                source,
                &sources,
                &targets,
                None,
                alias,
                &mut session,
            ),
            Err(InstantiationError::CountLimit { count: 5, limit: 5 })
        );
        assert!(session.limit_event_occurred_since(mark));
        assert_eq!(session.active_mappers[0].cache.get(&key), Some(&result));
        assert_eq!(
            (session.depth, session.query_count(), session.total_count()),
            (3, 5, 9)
        );

        session.count = 4;
        session.depth = 10;
        let mark = session.limit_event_mark();
        assert_eq!(
            instantiate_type_with_vector_and_alias_and_session(
                &mut fixture.store,
                source,
                &sources,
                &targets,
                None,
                alias,
                &mut session,
            ),
            Err(InstantiationError::DepthLimit {
                depth: 10,
                limit: 10
            })
        );
        assert!(session.limit_event_occurred_since(mark));
        assert_eq!(
            (session.depth, session.query_count(), session.total_count()),
            (10, 4, 9)
        );

        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        session.limit_policy = InstantiationLimitPolicy::Recover { error_type };
        let cache = session.active_mappers[0].cache.clone();
        for owner in fixture.outer_aliases {
            let mark = session.limit_event_mark();
            assert_eq!(
                instantiate_type_with_vector_and_alias_and_session(
                    &mut fixture.store,
                    source,
                    &sources,
                    &targets,
                    None,
                    Some((owner, &[])),
                    &mut session,
                ),
                Ok(error_type)
            );
            assert!(session.limit_event_occurred_since(mark));
            assert_eq!(session.active_mappers.len(), 1);
            assert_eq!(
                session.active_mappers[0].cache, cache,
                "a guarded cache hit survives, and an absent key stays absent"
            );
            assert_eq!(
                (session.depth, session.query_count(), session.total_count()),
                (10, 4, 9)
            );
            assert_eq!(deferred_intersection_store_state(&fixture.store), before);
        }
    }

    #[test]
    fn borrowed_alias_validation_stays_after_nonvariable_and_limit_guards() {
        let mut fixture = deferred_generic_intersection_fixture();
        let foreign = deferred_generic_intersection_fixture();
        let source = fixture.props;
        let sources = [source];
        let targets = [fixture.string];
        let foreign_argument = [foreign.string];
        let invalid = [
            Some((foreign.outer_aliases[0], &[][..])),
            Some((fixture.outer_aliases[0], foreign_argument.as_slice())),
        ];
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mark = session.limit_event_mark();
        let before = deferred_intersection_store_state(&fixture.store);
        for alias in invalid {
            assert_eq!(
                instantiate_type_with_vector_and_alias_and_session(
                    &mut fixture.store,
                    source,
                    &sources,
                    &targets,
                    None,
                    alias,
                    &mut session,
                ),
                Err(InstantiationError::InvalidType(source))
            );
        }
        assert_eq!(
            (session.depth, session.query_count(), session.total_count()),
            (0, 0, 0)
        );
        assert!(session.active_mappers.is_empty());
        assert_eq!(session.limit_event_mark(), mark);
        assert_eq!(deferred_intersection_store_state(&fixture.store), before);

        session.limits.max_depth = 0;
        session.limits.max_count = 0;
        assert_eq!(
            instantiate_type_with_vector_and_alias_and_session(
                &mut fixture.store,
                fixture.string,
                &sources,
                &targets,
                None,
                invalid[0],
                &mut session,
            ),
            Ok(fixture.string)
        );
        assert_eq!(session.limit_event_mark(), mark);
        assert_eq!(
            instantiate_type_with_vector_and_alias_and_session(
                &mut fixture.store,
                source,
                &sources,
                &targets,
                None,
                invalid[0],
                &mut session,
            ),
            Err(InstantiationError::DepthLimit { depth: 0, limit: 0 })
        );
        assert!(session.limit_event_occurred_since(mark));
        assert_eq!(
            (session.depth, session.query_count(), session.total_count()),
            (0, 0, 0)
        );
        assert!(session.active_mappers.is_empty());
        assert_eq!(deferred_intersection_store_state(&fixture.store), before);
    }

    #[test]
    fn malformed_or_foreign_alias_rejection_does_not_mutate_the_dynamic_session() {
        let mut store = initialized_store();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, parameter).unwrap();
        let malformed_alias = store.alloc_type_alias(None).unwrap();
        let mut foreign = initialized_store();
        let foreign_alias = foreign.alloc_type_alias(None).unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());

        for alias in [malformed_alias, foreign_alias] {
            assert_eq!(
                instantiate_type_with_alias(
                    &mut store,
                    parameter,
                    InstantiationMapping::Stored(mapper),
                    None,
                    Some(alias),
                    &mut session,
                ),
                Err(InstantiationError::InvalidAlias(alias)),
            );
        }
        assert_eq!(session.depth, 0);
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 0);
        assert!(session.active_mappers.is_empty());
    }

    #[test]
    fn vector_instantiation_maps_many_parameters_without_allocating_a_mapper() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let first = store.alloc_type_parameter(None).unwrap();
        let second = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![first, second])
            .unwrap();
        let mapper_count = store.mapper_len();

        let result =
            instantiate_type_with_vector(&mut store, source, &[first, second], &[string, number])
                .unwrap();

        assert_eq!(store.mapper_len(), mapper_count);
        let TypeData::Union(data) = store.type_payload(result).unwrap().data() else {
            panic!("two distinct mapped leaves must remain a union");
        };
        assert_eq!(data.union.types, [string, number]);
    }

    #[test]
    fn vector_instantiation_is_single_pass_for_dependent_recovery_arguments() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let first = store.alloc_type_parameter(None).unwrap();
        let second = store.alloc_type_parameter(None).unwrap();

        assert_eq!(
            instantiate_type_with_vector(&mut store, second, &[first, second], &[string, first],),
            Ok(first),
            "newTypeMapper maps U to its raw recovery target T without remapping T"
        );
    }

    #[test]
    fn vector_instantiation_can_share_one_checker_query_session() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let first = store.alloc_type_parameter(None).unwrap();
        let second = store.alloc_type_parameter(None).unwrap();
        let sources = [first, second];
        let targets = [string, number];
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 10,
            max_count: 1,
        });

        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut store,
                first,
                &sources,
                &targets,
                None,
                &mut session,
            ),
            Ok(string),
        );
        assert_eq!(session.query_count(), 1);
        assert_eq!(session.total_count(), 1);
        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut store,
                second,
                &sources,
                &targets,
                None,
                &mut session,
            ),
            Err(InstantiationError::CountLimit { count: 1, limit: 1 }),
        );
        assert_eq!(session.query_count(), 1);
        assert_eq!(session.total_count(), 1);

        session.reset_query();
        assert_eq!(
            instantiate_type_with_vector_and_session(
                &mut store,
                second,
                &sources,
                &targets,
                None,
                &mut session,
            ),
            Ok(number),
        );
        assert_eq!(session.query_count(), 1);
        assert_eq!(session.total_count(), 2);
    }

    #[test]
    fn unchanged_generic_union_preserves_its_original_identity() {
        let mut store = initialized_store();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, string])
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, parameter).unwrap();
        let before = store.type_len();

        assert_eq!(instantiate_type(&mut store, source, mapper), Ok(source));
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn non_variable_leaves_do_not_consume_instantiation_limits() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let limits = InstantiationLimits {
            max_depth: 0,
            max_count: 0,
        };
        let mut session = InstantiationSession::new(limits);
        let mark = session.limit_event_mark();
        assert_eq!(
            instantiate_type_with_session(&mut store, string, mapper, None, &mut session),
            Ok(string),
        );
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 0);
        assert!(!session.limit_event_occurred_since(mark));

        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![string, number])
            .unwrap();
        assert_eq!(
            instantiate_type_with_session(&mut store, union, mapper, None, &mut session),
            Ok(union),
        );
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 0);
        assert!(!session.limit_event_occurred_since(mark));
        assert_eq!(
            instantiate_type_with_session(&mut store, parameter, mapper, None, &mut session),
            Err(InstantiationError::DepthLimit { depth: 0, limit: 0 }),
        );
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 0);
        assert!(session.limit_event_occurred_since(mark));
    }

    #[test]
    fn aliases_and_limits_fail_closed_without_semantic_writes() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let parameter = store.alloc_type_parameter(None).unwrap();
        let source = store
            .alloc_union_type(ObjectFlags::NONE, vec![parameter, string])
            .unwrap();
        let alias = store.alloc_type_alias(None).unwrap();
        assert!(store.set_type_alias(source, Some(alias)));
        let mapper = store.new_simple_type_mapper(parameter, number).unwrap();
        let before = store.type_len();

        assert_eq!(
            instantiate_type(&mut store, source, mapper),
            Err(InstantiationError::UnsupportedAliasedUnion(source))
        );
        assert_eq!(store.type_len(), before);

        assert!(store.set_type_alias(source, None));
        assert_eq!(
            instantiate_type_with_limits(
                &mut store,
                source,
                mapper,
                InstantiationLimits {
                    max_depth: 1,
                    max_count: 10,
                },
            ),
            Err(InstantiationError::DepthLimit { depth: 1, limit: 1 })
        );
        assert_eq!(store.type_len(), before);
    }

    const MAPPED_RESULT_SESSION_FILE: FileId = FileId::new(202_811);

    fn mapped_result_session_context<'arena>(
        library: &'arena ParseResult,
        source: &'arena ParseResult,
    ) -> CanonicalCheckerContext<'arena> {
        let library_file = FileId::new(202_810);
        let mut binder = CanonicalBinder::new();
        for (file, parsed, declaration, path) in [
            (
                library_file,
                library,
                true,
                "\"/result-session-library.d.ts\"",
            ),
            (
                MAPPED_RESULT_SESSION_FILE,
                source,
                false,
                "\"/result-session.ts\"",
            ),
        ] {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![
                (library_file, &library.arena),
                (MAPPED_RESULT_SESSION_FILE, &source.arena),
            ],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn mapped_result_interface(store: &CanonicalTypeMapperStore, name: &str) -> TypeId {
        let owner = store
            .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
            .and_then(|globals| globals.get_source(name))
            .and_then(|owner| store.get_merged_symbol(owner))
            .unwrap();
        store
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap()
    }

    fn mapped_result_return(
        context: &mut CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        name: &str,
    ) -> (TypeId, Vec<TypeId>) {
        let name = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                let node = function.name?;
                let NodeData::Identifier(identifier) = &parsed.arena.get(node)?.data else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(
                    parsed.arena.id(),
                    MAPPED_RESULT_SESSION_FILE,
                    node,
                ))
            })
            .unwrap();
        let callable = context.get_type_at_location(name).unwrap();
        let signature = context
            .store()
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let parameters = context
            .store()
            .signature(signature)
            .unwrap()
            .type_parameters()
            .to_vec();
        let returned = context.get_return_type_of_signature(signature).unwrap();
        (returned, parameters)
    }

    fn dirty_mapped_result_union(
        context: &mut CanonicalCheckerContext<'_>,
    ) -> (SemanticSymbolId, TypeId) {
        let globals = context.global_types().clone();
        let derived = mapped_result_interface(context.store(), "Derived");
        let plain = mapped_result_interface(context.store(), "Plain");
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let source_union = store
            .expression_union_type_with_global_types_and_session(
                &globals,
                &[number, derived],
                UnionReduction::Literal,
                &mut setup,
            )
            .unwrap();
        store
            .expression_union_type_with_global_types_and_session(
                &globals,
                &[source_union, plain],
                UnionReduction::Subtype,
                &mut setup,
            )
            .unwrap();
        let members = store
            .type_payload(derived)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .members
            .unwrap();
        let proxy = store
            .symbol_table(members)
            .and_then(|members| members.get_source("value"))
            .unwrap();
        let links = store.value_symbol_links(proxy).unwrap().clone();
        assert_eq!(links.resolved_type, Some(number));
        assert!(links.target.is_some());
        assert!(links.mapper.is_some());
        assert!(store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                resolved_type: None,
                ..links
            }
        ));
        store.mark_union_cache_validation_dirty();
        (proxy, derived.max(plain))
    }

    #[allow(clippy::too_many_lines)] // Each result path shares the same dirty-cache limit and retry proof.
    fn assert_mapped_result_union_budget(interface_name: Option<&str>) {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: number; }",
        ));
        let source = parse_source_file(concat!(
            "interface Derived extends Base<number> {} ",
            "interface Plain { value: number; } ",
            "interface Optional { item?: number; } ",
            "interface OptionalIndexed { item?: number; [key: string]: number | undefined; } ",
            "declare function read<Model, Key extends keyof Model>(): Model[Key]; ",
            "declare function build<Value>(): Value | number | `id-${number}`;",
        ));
        let mut context = mapped_result_session_context(&library, &source);
        context
            .check_source_file(MAPPED_RESULT_SESSION_FILE)
            .unwrap();
        assert!(context.diagnostics().is_empty());
        let (template, parameters) = mapped_result_return(
            &mut context,
            &source,
            if interface_name.is_some() {
                "read"
            } else {
                "build"
            },
        );
        let array_targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let undefined = bootstrap.undefined_type;
        let arguments = interface_name.map_or_else(
            || vec![string],
            |name| vec![mapped_result_interface(context.store(), name)],
        );
        let store = context.store_mut_for_test();
        let mut arguments = arguments;
        if let Some(name) = interface_name {
            let key = store.regular_string_literal_type("item".into()).unwrap();
            arguments.push(key);
            let resolution = indexed_access_resolution(
                store,
                arguments[0],
                key,
                AccessFlags::NONE,
                Some(array_targets),
            )
            .unwrap();
            if name == "Optional" {
                assert!(matches!(resolution, IndexedAccessResolution::Property(_)));
            } else {
                assert!(matches!(
                    resolution,
                    IndexedAccessResolution::TypeWithSentinel(value, sentinel)
                        if value == number && sentinel == undefined
                ));
            }
        }
        let mapper = store
            .new_type_mapper(parameters.clone(), arguments.clone())
            .unwrap();
        let expected = store
            .literal_union_type_with_alias_and_array_targets(
                &[
                    number,
                    if interface_name.is_some() {
                        undefined
                    } else {
                        string
                    },
                ],
                None,
                Some(array_targets),
            )
            .unwrap();
        let (proxy, failed_constituent) = dirty_mapped_result_union(&mut context);
        let store = context.store_mut_for_test();
        let max_count = if interface_name.is_some() { 4 } else { 3 };
        let mut limited = InstantiationSession::new(InstantiationLimits {
            max_count,
            ..InstantiationLimits::default()
        });
        assert_eq!(
            instantiate_type_with_session(
                store,
                parameters[0],
                mapper,
                Some(array_targets),
                &mut limited,
            ),
            Ok(arguments[0])
        );
        assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
        let before = deferred_intersection_store_state(store);
        let scans = store.union_cache_validation_scan_count();
        let expected_error = if interface_name.is_some() {
            InstantiationError::Union(LiteralTypeCacheError::UnsupportedUnionConstituent(
                failed_constituent,
            ))
        } else {
            InstantiationError::Template(TemplateTypeError::UnsupportedUnionConstituent(
                failed_constituent,
            ))
        };
        assert_eq!(
            instantiate_type_with_session(
                store,
                template,
                mapper,
                Some(array_targets),
                &mut limited,
            ),
            Err(expected_error)
        );
        assert_eq!(
            (limited.depth, limited.query_count(), limited.total_count()),
            (0, max_count, max_count)
        );
        assert_eq!(limited.limit_event_count(), 1);
        assert!(limited.active_mappers.is_empty());
        assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
        assert_eq!(deferred_intersection_store_state(store), before);
        assert_eq!(store.union_cache_validation_scan_count(), scans + 1);
        assert_eq!(
            instantiate_type_with_session(
                store,
                template,
                mapper,
                Some(array_targets),
                &mut limited,
            ),
            Err(InstantiationError::CountLimit {
                count: max_count,
                limit: max_count,
            })
        );
        assert_eq!(limited.limit_event_count(), 2);
        assert_eq!(
            (limited.depth, limited.query_count(), limited.total_count()),
            (0, max_count, max_count)
        );
        assert_eq!(store.union_cache_validation_scan_count(), scans + 1);
        assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
        assert_eq!(deferred_intersection_store_state(store), before);

        let mut healthy = InstantiationSession::new(InstantiationLimits::default());
        healthy.active_mappers.push(ActiveMapperFrame {
            mapping: InstantiationMappingIdentity::Stored(mapper),
            cache: HashMap::new(),
        });
        assert_eq!(
            instantiate_type_with_session(
                store,
                template,
                mapper,
                Some(array_targets),
                &mut healthy,
            ),
            Ok(expected)
        );
        assert_eq!(
            store.value_symbol_links(proxy).unwrap().resolved_type,
            Some(number)
        );
        assert_eq!(healthy.limit_event_count(), 0);
        assert_eq!(healthy.depth, 0);
        assert_eq!(healthy.active_mappers.len(), 1);
        assert!(healthy.query_count() >= max_count);
        let count = healthy.total_count();
        let warm = deferred_intersection_store_state(store);
        for _ in 0..2 {
            assert_eq!(
                instantiate_type_with_session(
                    store,
                    template,
                    mapper,
                    Some(array_targets),
                    &mut healthy,
                ),
                Ok(expected)
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    template,
                    &parameters,
                    &arguments,
                    Some(array_targets),
                    None,
                ),
                Ok(Some(expected))
            );
            assert_eq!(healthy.total_count(), count);
            assert_eq!(healthy.query_count(), count);
            assert_eq!(healthy.limit_event_count(), 0);
            assert_eq!(deferred_intersection_store_state(store), warm);
        }
    }

    #[test]
    fn indexed_sentinel_unions_validate_dirty_caches_with_the_caller() {
        for interface in ["Optional", "OptionalIndexed"] {
            assert_mapped_result_union_budget(Some(interface));
        }
    }

    #[test]
    fn reduced_template_unions_validate_dirty_caches_with_the_caller() {
        assert_mapped_result_union_budget(None);
    }
}
