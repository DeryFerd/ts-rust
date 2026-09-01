//! Cached object-literal regularization and root-context widening.
//!
//! This is the dependency-closed property-object and canonical-array prefix
//! of pinned `getRegularTypeOfObjectLiteral`, `getWidenedType`, and
//! `getWidenedTypeOfObjectLiteral`. Derived anonymous types preserve the
//! source object's symbol, clone only properties whose type changes, and keep
//! the upstream cache identities stable across warm queries.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, EscapedNameRef, InternalSymbolName, SemanticSymbolId, SymbolData,
    SymbolFlags, SymbolTableId,
};

use super::{
    ArrayTypeError, CanonicalGlobalTypes,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    ids::TypeId,
    instantiate::InstantiationSession,
    links::ValueSymbolLinks,
    mapper::TypeMapper,
    object_members::{
        DeclaredPropertyObjectValidation, object_literal_getter_projection,
        validate_resolved_declared_property_object,
    },
    store::{SemanticStore, SourceNodeParent},
    type_records::{
        ConstrainedTypeData, ObjectTypeData, StructuredTypeData, TypeCacheState, TypeData,
        TypeRecord,
    },
    types::{ObjectFlags, TypeFlags},
};

/// Store-owned caches corresponding to pinned `CachedTypeKind` entries used
/// by object-literal regularization, root-context widening, and array-literal
/// reference cloning.
#[derive(Debug, Default)]
pub(super) struct DerivedTypeCaches {
    regular_object_literals: HashMap<TypeId, TypeId>,
    widened_types: HashMap<TypeId, TypeId>,
    contextual_widened_types: HashMap<(TypeId, TypeId), TypeId>,
    undefined_properties: HashMap<EscapedName, SemanticSymbolId>,
    pub(super) array_literal_types: HashMap<TypeId, TypeId>,
}

/// Exact relation-facing classification of an object type against the two
/// derived object-literal caches.
///
/// `Invalid` means the type is named by a cache entry, but the entry no longer
/// satisfies the same provenance checks used by a warm derived-type query.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DerivedObjectLiteralValidation {
    NotDerived,
    Valid {
        owner: SemanticSymbolId,
        source: TypeId,
    },
    Invalid,
}

impl DerivedTypeCaches {
    fn try_reserve_regular(&mut self, additional: usize) -> bool {
        self.regular_object_literals.try_reserve(additional).is_ok()
    }

    fn try_reserve_widened(&mut self, additional: usize) -> bool {
        self.widened_types.try_reserve(additional).is_ok()
    }

    fn try_reserve_contextual_widened(&mut self, additional: usize) -> bool {
        self.contextual_widened_types
            .try_reserve(additional)
            .is_ok()
    }

    fn try_reserve_undefined_properties(&mut self, additional: usize) -> bool {
        self.undefined_properties.try_reserve(additional).is_ok()
    }

    pub(super) fn try_reserve_array_literals(&mut self, additional: usize) -> bool {
        self.array_literal_types.try_reserve(additional).is_ok()
    }
}

/// A derived-type query rejected before publishing a semantic identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DerivedTypeError {
    BootstrapUninitialized,
    Type(TypeId),
    ArrayType(ArrayTypeError),
    MalformedObjectLiteral(TypeId),
    UnresolvedPropertyType(SemanticSymbolId),
    InvalidRegularObjectLiteralCache { source: TypeId, cached: TypeId },
    InvalidWidenedTypeCache { source: TypeId, cached: TypeId },
    UnsupportedWideningType(TypeId),
    RecursiveWideningType(TypeId),
    RecursiveObjectLiteral(TypeId),
    Capacity(TypeId),
}

impl std::fmt::Display for DerivedTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BootstrapUninitialized => {
                formatter.write_str("derived types require intrinsic checker bootstrap")
            }
            Self::Type(type_) => write!(formatter, "type {type_:?} is not store-owned"),
            Self::ArrayType(error) => write!(formatter, "array widening failed: {error}"),
            Self::MalformedObjectLiteral(type_) => {
                write!(formatter, "object-literal type {type_:?} is malformed")
            }
            Self::UnresolvedPropertyType(property) => {
                write!(formatter, "property {property:?} has no resolved type")
            }
            Self::InvalidRegularObjectLiteralCache { source, cached } => write!(
                formatter,
                "regular object-literal cache entry {source:?} -> {cached:?} is invalid"
            ),
            Self::InvalidWidenedTypeCache { source, cached } => write!(
                formatter,
                "widened type cache entry {source:?} -> {cached:?} is invalid"
            ),
            Self::UnsupportedWideningType(type_) => {
                write!(
                    formatter,
                    "type {type_:?} requires an unsupported widening family"
                )
            }
            Self::RecursiveWideningType(type_) => {
                write!(formatter, "type {type_:?} has a recursive widening graph")
            }
            Self::RecursiveObjectLiteral(type_) => write!(
                formatter,
                "object-literal type {type_:?} has a recursive property graph"
            ),
            Self::Capacity(type_) => write!(
                formatter,
                "derived type capacity was exhausted while transforming {type_:?}"
            ),
        }
    }
}

impl std::error::Error for DerivedTypeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ArrayType(error) => Some(error),
            Self::BootstrapUninitialized
            | Self::Type(_)
            | Self::MalformedObjectLiteral(_)
            | Self::UnresolvedPropertyType(_)
            | Self::InvalidRegularObjectLiteralCache { .. }
            | Self::InvalidWidenedTypeCache { .. }
            | Self::UnsupportedWideningType(_)
            | Self::RecursiveWideningType(_)
            | Self::RecursiveObjectLiteral(_)
            | Self::Capacity(_) => None,
        }
    }
}

impl From<ArrayTypeError> for DerivedTypeError {
    fn from(error: ArrayTypeError) -> Self {
        Self::ArrayType(error)
    }
}

#[derive(Clone, Debug)]
struct PropertyShape {
    symbol: SemanticSymbolId,
    name: EscapedName,
    type_: TypeId,
}

#[derive(Clone, Debug)]
struct ObjectShape {
    flags: TypeFlags,
    object_flags: ObjectFlags,
    symbol: SemanticSymbolId,
    members: SymbolTableId,
    properties: Vec<PropertyShape>,
    index_infos: Option<Vec<super::IndexInfoId>>,
}

#[derive(Clone, Copy, Debug)]
enum RegularTransform {
    Identity(TypeId),
    Object(TypeId),
}

#[derive(Debug)]
struct RegularPropertyPlan {
    source: SemanticSymbolId,
    name: EscapedName,
    transform: RegularTransform,
}

#[derive(Debug)]
struct RegularObjectPlan {
    source: TypeId,
    shape: ObjectShape,
    properties: Vec<RegularPropertyPlan>,
}

#[derive(Clone, Copy, Debug)]
enum WidenTransform {
    Identity(TypeId),
    Cached(TypeId),
    ContextualCached { union: TypeId, source: TypeId },
}

#[derive(Debug)]
struct WidenPropertyPlan {
    source: SemanticSymbolId,
    name: EscapedName,
    transform: WidenTransform,
}

#[derive(Debug)]
struct WidenIndexPlan {
    source: super::IndexInfoId,
    transform: WidenTransform,
}

#[derive(Debug)]
enum WidenPlan {
    Existing {
        source: TypeId,
        target: TypeId,
    },
    Object {
        source: TypeId,
        shape: ObjectShape,
        properties: Vec<WidenPropertyPlan>,
        indexes: Vec<WidenIndexPlan>,
    },
    ContextualObject {
        union: TypeId,
        source: TypeId,
        shape: ObjectShape,
        properties: Vec<WidenPropertyPlan>,
        undefined_properties: Vec<PropertyShape>,
        indexes: Vec<WidenIndexPlan>,
    },
    Array {
        source: TypeId,
        element: WidenTransform,
        readonly: bool,
    },
    Union {
        source: TypeId,
        constituents: Vec<WidenTransform>,
    },
}

impl SemanticStore<TypeRecord, TypeMapper> {
    /// Returns the cached regular counterpart of a fresh object literal.
    /// Non-fresh and non-object-literal inputs follow upstream identity
    /// semantics.
    pub(super) fn get_regular_type_of_object_literal(
        &mut self,
        type_: TypeId,
    ) -> Result<TypeId, DerivedTypeError> {
        let record = self
            .type_payload(type_)
            .ok_or(DerivedTypeError::Type(type_))?;
        if !record
            .object_flags()
            .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL)
        {
            return Ok(type_);
        }
        if self.intrinsic_bootstrap().is_none() {
            return Err(DerivedTypeError::BootstrapUninitialized);
        }

        let mut plans = Vec::new();
        let mut visiting = HashSet::new();
        let mut planned = HashSet::new();
        self.plan_regular_object(type_, &mut plans, &mut visiting, &mut planned)?;
        if plans.is_empty() {
            return self
                .derived_types
                .regular_object_literals
                .get(&type_)
                .copied()
                .ok_or(DerivedTypeError::MalformedObjectLiteral(type_));
        }

        let clone_count = plans.iter().try_fold(0usize, |count, plan| {
            count.checked_add(
                plan.properties
                    .iter()
                    .filter(|property| matches!(property.transform, RegularTransform::Object(_)))
                    .count(),
            )
        });
        let Some(clone_count) = clone_count else {
            return Err(DerivedTypeError::Capacity(type_));
        };
        if !self.derived_types.try_reserve_regular(plans.len())
            || !self.try_reserve_types(plans.len())
            || !self.try_reserve_checker_symbol_allocations(clone_count, plans.len())
        {
            return Err(DerivedTypeError::Capacity(type_));
        }

        for plan in plans {
            self.publish_regular_object(plan);
        }
        Ok(*self
            .derived_types
            .regular_object_literals
            .get(&type_)
            .expect("the root regular object plan was published"))
    }

    /// Applies pinned root-context widening for the dependency-closed
    /// property-only object-literal prefix.
    #[cfg(test)]
    pub(super) fn get_widened_type(&mut self, type_: TypeId) -> Result<TypeId, DerivedTypeError> {
        self.get_widened_type_worker(type_, None, None)
    }

    /// Applies pinned root-context widening with authoritative global-array
    /// identities available to the canonical `Array<T>` and
    /// `ReadonlyArray<T>` prefix.
    pub(super) fn get_widened_type_with_global_types(
        &mut self,
        type_: TypeId,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<TypeId, DerivedTypeError> {
        self.get_widened_type_worker(type_, Some(global_types), None)
    }

    /// Keeps widening's union checks in the caller's instantiation session.
    pub(super) fn get_widened_type_with_global_types_and_session(
        &mut self,
        type_: TypeId,
        global_types: &CanonicalGlobalTypes,
        session: &mut InstantiationSession,
    ) -> Result<TypeId, DerivedTypeError> {
        self.get_widened_type_worker(type_, Some(global_types), Some(session))
    }

    fn get_widened_type_worker(
        &mut self,
        type_: TypeId,
        global_types: Option<&CanonicalGlobalTypes>,
        mut session: Option<&mut InstantiationSession>,
    ) -> Result<TypeId, DerivedTypeError> {
        let record = self
            .type_payload(type_)
            .ok_or(DerivedTypeError::Type(type_))?;
        if !record
            .object_flags()
            .intersects(ObjectFlags::REQUIRES_WIDENING)
        {
            return Ok(type_);
        }
        if self.intrinsic_bootstrap().is_none() {
            return Err(DerivedTypeError::BootstrapUninitialized);
        }

        let mut plans = Vec::new();
        let mut visiting = HashSet::new();
        let mut planned = HashSet::new();
        self.plan_widened_type(type_, global_types, &mut plans, &mut visiting, &mut planned)?;
        if plans.is_empty() {
            return self.derived_types.widened_types.get(&type_).copied().ok_or(
                DerivedTypeError::InvalidWidenedTypeCache {
                    source: type_,
                    cached: type_,
                },
            );
        }

        let object_count = plans
            .iter()
            .filter(|plan| {
                matches!(
                    plan,
                    WidenPlan::Object { .. } | WidenPlan::ContextualObject { .. }
                )
            })
            .count();
        let contextual_count = plans
            .iter()
            .filter(|plan| matches!(plan, WidenPlan::ContextualObject { .. }))
            .count();
        let array_count = plans
            .iter()
            .filter(|plan| matches!(plan, WidenPlan::Array { .. }))
            .count();
        let union_count = plans
            .iter()
            .filter(|plan| matches!(plan, WidenPlan::Union { .. }))
            .count();
        let index_count = plans
            .iter()
            .try_fold(0usize, |count, plan| match plan {
                WidenPlan::Object { indexes, .. } | WidenPlan::ContextualObject { indexes, .. } => {
                    count.checked_add(indexes.len())
                }
                _ => Some(count),
            })
            .ok_or(DerivedTypeError::Capacity(type_))?;
        let mut undefined_names = HashSet::new();
        let clone_count = plans.iter().try_fold(0usize, |count, plan| match plan {
            WidenPlan::Existing { .. } | WidenPlan::Array { .. } | WidenPlan::Union { .. } => {
                Some(count)
            }
            WidenPlan::Object { properties, .. } => count.checked_add(
                properties
                    .iter()
                    .filter(|property| matches!(property.transform, WidenTransform::Cached(_)))
                    .count(),
            ),
            WidenPlan::ContextualObject {
                properties,
                undefined_properties,
                ..
            } => {
                for property in undefined_properties {
                    if !self
                        .derived_types
                        .undefined_properties
                        .contains_key(&property.name)
                    {
                        undefined_names.insert(property.name.clone());
                    }
                }
                count.checked_add(properties.len())
            }
        });
        let Some(clone_count) =
            clone_count.and_then(|count| count.checked_add(undefined_names.len()))
        else {
            return Err(DerivedTypeError::Capacity(type_));
        };
        let Some(type_count) = object_count.checked_add(array_count).and_then(|count| {
            union_count
                .checked_mul(2)
                .and_then(|unions| count.checked_add(unions))
        }) else {
            return Err(DerivedTypeError::Capacity(type_));
        };
        if !self.derived_types.try_reserve_widened(plans.len())
            || !self
                .derived_types
                .try_reserve_contextual_widened(contextual_count)
            || !self
                .derived_types
                .try_reserve_undefined_properties(undefined_names.len())
            || !self.try_reserve_types(type_count)
            || !self.try_reserve_checker_symbol_allocations(clone_count, object_count)
            || !self.try_reserve_index_infos(index_count)
        {
            return Err(DerivedTypeError::Capacity(type_));
        }
        if array_count != 0
            && let Some(global_types) = global_types
        {
            let mutable_count = plans
                .iter()
                .filter(|plan| {
                    matches!(
                        plan,
                        WidenPlan::Array {
                            readonly: false,
                            ..
                        }
                    )
                })
                .count();
            let readonly_count = array_count - mutable_count;
            if global_types.array_type == global_types.readonly_array_type {
                if !self.try_reserve_object_instantiations(global_types.array_type, array_count) {
                    return Err(DerivedTypeError::Capacity(type_));
                }
            } else {
                let mutable_reserved = mutable_count == 0
                    || self
                        .try_reserve_object_instantiations(global_types.array_type, mutable_count);
                let readonly_reserved = readonly_count == 0
                    || self.try_reserve_object_instantiations(
                        global_types.readonly_array_type,
                        readonly_count,
                    );
                if !mutable_reserved || !readonly_reserved {
                    return Err(DerivedTypeError::Capacity(type_));
                }
            }
        }
        if union_count != 0 {
            let result = match (global_types, session.as_deref_mut()) {
                (Some(global_types), Some(session)) => self
                    .prepare_type_query_types_with_global_types_and_session(
                        &[],
                        &[],
                        &[],
                        union_count,
                        0,
                        global_types,
                        session,
                    ),
                (Some(global_types), None) => self.prepare_type_query_types_with_global_types(
                    &[],
                    &[],
                    &[],
                    union_count,
                    0,
                    global_types,
                ),
                (None, _) => self.prepare_type_query_types(&[], &[], &[], union_count, 0),
            };
            result.map_err(|error| widening_union_error(type_, error))?;
        }

        for plan in plans {
            self.publish_widened_type(plan, global_types, session.as_deref_mut())?;
        }
        Ok(*self
            .derived_types
            .widened_types
            .get(&type_)
            .expect("the root widened type plan was published"))
    }

    /// Checks one retained widening cache pair without publishing a type.
    pub(super) fn validate_cached_widened_type(
        &self,
        source: TypeId,
        target: TypeId,
        global_types: Option<&CanonicalGlobalTypes>,
    ) -> bool {
        self.derived_types.widened_types.get(&source) == Some(&target)
            && self.widened_cache_entry_is_valid(
                source,
                target,
                &mut HashSet::new(),
                &mut HashSet::new(),
                global_types.map(CanonicalArrayTargets::from_global_types),
            )
    }

    /// Validates a relation operand that may be a cached regular or widened
    /// object-literal type.
    ///
    /// The reverse cache lookup is intentionally unique and the selected
    /// entry is checked by the existing warm-cache validator. This keeps the
    /// structural relation boundary fail-closed without teaching the relater
    /// a second, looser definition of checker-derived property clones.
    pub(super) fn validate_derived_object_literal_for_relation(
        &self,
        type_: TypeId,
    ) -> DerivedObjectLiteralValidation {
        self.validate_derived_object_literal(type_, None)
    }

    /// Reuses the complete source-owned fresh-object proof for readonly relations.
    pub(super) fn validate_fresh_object_literal_for_relation(&self, type_: TypeId) -> bool {
        self.fresh_object_shape(type_).is_some()
    }

    /// Validates a cached regular or widened object literal while retaining
    /// the authoritative array identities needed by nested widened arrays.
    pub(super) fn validate_derived_object_literal_with_global_types(
        &self,
        type_: TypeId,
        global_types: &CanonicalGlobalTypes,
    ) -> DerivedObjectLiteralValidation {
        self.validate_derived_object_literal_with_array_targets(
            type_,
            CanonicalArrayTargets::from_global_types(global_types),
        )
    }

    /// Relation-facing form that retains only the exact global-array
    /// capability installed on the relation session. Getter-owned objects
    /// retain the read and checked-body array edges.
    pub(super) fn validate_derived_object_literal_with_array_targets(
        &self,
        type_: TypeId,
        array_targets: CanonicalArrayTargets,
    ) -> DerivedObjectLiteralValidation {
        let structure =
            self.validate_derived_object_literal_structure_with_array_targets(type_, array_targets);
        if matches!(structure, DerivedObjectLiteralValidation::Valid { .. })
            && self.derived_object_literal_has_getter_origin(type_)
            && self
                .validate_cached_array_capability_with_array_targets(array_targets, type_)
                .is_err()
        {
            return DerivedObjectLiteralValidation::Invalid;
        }
        structure
    }

    /// Checks source-cache identity without starting another array graph walk.
    pub(super) fn validate_derived_object_literal_structure_with_array_targets(
        &self,
        type_: TypeId,
        array_targets: CanonicalArrayTargets,
    ) -> DerivedObjectLiteralValidation {
        self.validate_derived_object_literal(type_, Some(array_targets))
    }

    /// Recognizes getter-owned source chains even when a derived payload is damaged.
    /// Callers must still validate the caches before using their source identities.
    pub(super) fn derived_object_literal_has_getter_origin(&self, type_: TypeId) -> bool {
        let mut pending = vec![type_];
        let mut visited = HashSet::new();
        while let Some(current) = pending.pop() {
            if !visited.insert(current) {
                continue;
            }
            if self
                .object_literal_getter_origin_for_type(current)
                .is_some()
            {
                return true;
            }
            self.observe_relation_derived_cache_target_read(current);
            for (&source, &target) in self
                .derived_types
                .regular_object_literals
                .iter()
                .chain(&self.derived_types.widened_types)
            {
                if target == current {
                    self.observe_relation_derived_cache_source_read(source);
                    pending.push(source);
                }
            }
            for (&(_, source), &target) in &self.derived_types.contextual_widened_types {
                if target == current {
                    self.observe_relation_derived_cache_source_read(source);
                    pending.push(source);
                }
            }
        }
        false
    }

    /// Authenticates a donor-owned optional property on a contextual object.
    pub(super) fn validate_contextual_widened_object_property(
        &self,
        receiver: TypeId,
        property: SemanticSymbolId,
    ) -> bool {
        let Some((union, source)) = self.contextual_widened_source(receiver) else {
            return false;
        };
        self.contextual_optional_property_is_valid(union, source, receiver, property)
    }

    fn validate_derived_object_literal(
        &self,
        type_: TypeId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> DerivedObjectLiteralValidation {
        if !matches!(
            self.type_payload(type_).map(TypeRecord::data),
            Some(TypeData::Object(_))
        ) {
            return DerivedObjectLiteralValidation::NotDerived;
        }
        self.observe_relation_derived_cache_target_read(type_);
        let mut regular_source = None;
        for (source, cached) in &self.derived_types.regular_object_literals {
            if *cached == type_ && regular_source.replace(*source).is_some() {
                return DerivedObjectLiteralValidation::Invalid;
            }
        }
        let mut widened_source = None;
        for (source, cached) in &self.derived_types.widened_types {
            if *cached == type_ && widened_source.replace(*source).is_some() {
                return DerivedObjectLiteralValidation::Invalid;
            }
        }
        let contextual_source = self.contextual_widened_source(type_);
        if self
            .derived_types
            .contextual_widened_types
            .values()
            .filter(|cached| **cached == type_)
            .count()
            > 1
        {
            return DerivedObjectLiteralValidation::Invalid;
        }

        let (source, valid) = match (regular_source, widened_source, contextual_source) {
            (None, None, None) => return DerivedObjectLiteralValidation::NotDerived,
            (Some(source), None, None) => {
                let mut visiting = HashSet::new();
                (
                    source,
                    self.regular_cache_entry_is_valid(source, type_, &mut visiting),
                )
            }
            (None, Some(source), None) => {
                let mut visiting = HashSet::new();
                let mut regular_visiting = HashSet::new();
                (
                    source,
                    self.widened_cache_entry_is_valid(
                        source,
                        type_,
                        &mut visiting,
                        &mut regular_visiting,
                        array_targets,
                    ),
                )
            }
            (None, None, Some((union, source))) => (
                source,
                self.contextual_object_cache_entry_is_valid(union, source, type_, array_targets),
            ),
            _ => return DerivedObjectLiteralValidation::Invalid,
        };
        if !valid {
            return DerivedObjectLiteralValidation::Invalid;
        }
        self.observe_relation_derived_cache_source_read(source);
        match self.resolved_object_shape(type_) {
            Some(shape) => DerivedObjectLiteralValidation::Valid {
                owner: shape.symbol,
                source,
            },
            None => DerivedObjectLiteralValidation::Invalid,
        }
    }

    fn plan_regular_object(
        &self,
        source: TypeId,
        plans: &mut Vec<RegularObjectPlan>,
        visiting: &mut HashSet<TypeId>,
        planned: &mut HashSet<TypeId>,
    ) -> Result<(), DerivedTypeError> {
        if let Some(cached) = self
            .derived_types
            .regular_object_literals
            .get(&source)
            .copied()
        {
            let mut cache_visiting = HashSet::new();
            if !self.regular_cache_entry_is_valid(source, cached, &mut cache_visiting) {
                return Err(DerivedTypeError::InvalidRegularObjectLiteralCache { source, cached });
            }
            return Ok(());
        }
        if planned.contains(&source) {
            return Ok(());
        }
        if !visiting.insert(source) {
            return Err(DerivedTypeError::RecursiveObjectLiteral(source));
        }
        self.preflight_fresh_object_getters(source)?;
        let shape = self
            .fresh_object_shape(source)
            .ok_or(DerivedTypeError::MalformedObjectLiteral(source))?;
        let mut properties = Vec::with_capacity(shape.properties.len());
        for property in &shape.properties {
            let transform = if self.is_fresh_object_literal(property.type_) {
                if self.object_literal_getter_origin(property.symbol).is_some()
                    || self
                        .symbol(property.symbol)
                        .is_some_and(|record| record.flags() == SymbolFlags::GET_ACCESSOR)
                {
                    return Err(DerivedTypeError::UnsupportedWideningType(source));
                }
                self.plan_regular_object(property.type_, plans, visiting, planned)?;
                RegularTransform::Object(property.type_)
            } else {
                RegularTransform::Identity(property.type_)
            };
            properties.push(RegularPropertyPlan {
                source: property.symbol,
                name: property.name.clone(),
                transform,
            });
        }
        visiting.remove(&source);
        planned.insert(source);
        plans.push(RegularObjectPlan {
            source,
            shape,
            properties,
        });
        Ok(())
    }

    fn plan_widened_type(
        &self,
        source: TypeId,
        global_types: Option<&CanonicalGlobalTypes>,
        plans: &mut Vec<WidenPlan>,
        visiting: &mut HashSet<TypeId>,
        planned: &mut HashSet<TypeId>,
    ) -> Result<WidenTransform, DerivedTypeError> {
        let record = self
            .type_payload(source)
            .ok_or(DerivedTypeError::Type(source))?;
        if !record
            .object_flags()
            .intersects(ObjectFlags::REQUIRES_WIDENING)
        {
            return Ok(WidenTransform::Identity(source));
        }
        if let Some(cached) = self.derived_types.widened_types.get(&source).copied() {
            let mut widened_visiting = HashSet::new();
            let mut regular_visiting = HashSet::new();
            if !self.widened_cache_entry_is_valid(
                source,
                cached,
                &mut widened_visiting,
                &mut regular_visiting,
                global_types.map(CanonicalArrayTargets::from_global_types),
            ) {
                return Err(DerivedTypeError::InvalidWidenedTypeCache { source, cached });
            }
            return Ok(WidenTransform::Cached(source));
        }
        if planned.contains(&source) {
            return Ok(WidenTransform::Cached(source));
        }

        if record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::NULLABLE)
        {
            let target = self
                .intrinsic_bootstrap()
                .ok_or(DerivedTypeError::BootstrapUninitialized)?
                .any_type;
            planned.insert(source);
            plans.push(WidenPlan::Existing { source, target });
            return Ok(WidenTransform::Cached(source));
        }

        if let TypeData::Union(union) = record.data() {
            let members = union.union.types.clone();
            let has_object_literals = members.iter().any(|member| {
                self.type_payload(*member).is_some_and(|record| {
                    record.object_flags().contains(ObjectFlags::OBJECT_LITERAL)
                        && record
                            .object_flags()
                            .intersects(ObjectFlags::REQUIRES_WIDENING)
                })
            });
            let validation = match global_types {
                Some(global_types) => {
                    self.validate_union_constituent_with_global_types(global_types, source)
                }
                None => self.validate_union_constituent(source),
            };
            validation.map_err(|error| widening_union_error(source, error))?;
            if has_object_literals {
                return self.plan_contextual_widened_union(
                    source,
                    &members,
                    global_types,
                    plans,
                    visiting,
                    planned,
                );
            }
            if !visiting.insert(source) {
                return Err(DerivedTypeError::RecursiveWideningType(source));
            }
            let mut constituents = Vec::with_capacity(members.len());
            for member in members {
                let member_record = self
                    .type_payload(member)
                    .ok_or(DerivedTypeError::Type(member))?;
                let transform = if member_record.flags().intersects(TypeFlags::NULLABLE) {
                    WidenTransform::Identity(member)
                } else {
                    self.plan_widened_type(member, global_types, plans, visiting, planned)?
                };
                constituents.push(transform);
            }
            debug_assert!(visiting.remove(&source));
            planned.insert(source);
            plans.push(WidenPlan::Union {
                source,
                constituents,
            });
            return Ok(WidenTransform::Cached(source));
        }

        if let Some(global_types) = global_types
            && let Some(array) = self.canonical_array_reference(global_types, source)?
        {
            if !visiting.insert(source) {
                return Err(DerivedTypeError::RecursiveWideningType(source));
            }
            let element = self.plan_widened_type(
                array.element_type,
                Some(global_types),
                plans,
                visiting,
                planned,
            )?;
            debug_assert!(visiting.remove(&source));
            planned.insert(source);
            plans.push(WidenPlan::Array {
                source,
                element,
                readonly: array.readonly,
            });
            return Ok(WidenTransform::Cached(source));
        }
        if !record.object_flags().contains(ObjectFlags::OBJECT_LITERAL) {
            return Err(DerivedTypeError::UnsupportedWideningType(source));
        }
        if !visiting.insert(source) {
            return Err(DerivedTypeError::RecursiveObjectLiteral(source));
        }
        self.preflight_fresh_object_getters(source)?;
        let mut regular_visiting = HashSet::new();
        let shape = self
            .validated_widening_object_shape(source, &mut regular_visiting)
            .ok_or(DerivedTypeError::MalformedObjectLiteral(source))?;
        let mut properties = Vec::with_capacity(shape.properties.len());
        for property in &shape.properties {
            let transform =
                self.plan_widened_type(property.type_, global_types, plans, visiting, planned)?;
            if (self.object_literal_getter_origin(property.symbol).is_some()
                || self
                    .symbol(property.symbol)
                    .is_some_and(|record| record.flags() == SymbolFlags::GET_ACCESSOR))
                && !matches!(transform, WidenTransform::Identity(type_) if type_ == property.type_)
            {
                return Err(DerivedTypeError::UnsupportedWideningType(source));
            }
            properties.push(WidenPropertyPlan {
                source: property.symbol,
                name: property.name.clone(),
                transform,
            });
        }
        let indexes =
            self.plan_widened_indexes(source, &shape, global_types, plans, visiting, planned)?;
        visiting.remove(&source);
        planned.insert(source);
        plans.push(WidenPlan::Object {
            source,
            shape,
            properties,
            indexes,
        });
        Ok(WidenTransform::Cached(source))
    }

    fn plan_contextual_widened_union(
        &self,
        union: TypeId,
        members: &[TypeId],
        global_types: Option<&CanonicalGlobalTypes>,
        plans: &mut Vec<WidenPlan>,
        visiting: &mut HashSet<TypeId>,
        planned: &mut HashSet<TypeId>,
    ) -> Result<WidenTransform, DerivedTypeError> {
        if !visiting.insert(union) {
            return Err(DerivedTypeError::RecursiveWideningType(union));
        }

        let mut object_shapes = Vec::with_capacity(members.len());
        let mut context_properties = Vec::<PropertyShape>::new();
        let mut context_names = HashMap::<EscapedName, usize>::new();
        for member in members {
            let record = self
                .type_payload(*member)
                .ok_or(DerivedTypeError::Type(*member))?;
            if record.flags().intersects(TypeFlags::NULLABLE)
                || self.is_non_widening_contextual_scalar(*member)
            {
                continue;
            }
            if !record.object_flags().contains(ObjectFlags::OBJECT_LITERAL) {
                if !matches!(
                    validate_resolved_declared_property_object(self, *member),
                    DeclaredPropertyObjectValidation::Valid(_)
                ) {
                    return Err(DerivedTypeError::UnsupportedWideningType(*member));
                }
                continue;
            }

            let mut regular_visiting = HashSet::new();
            let shape = self
                .validated_widening_object_shape(*member, &mut regular_visiting)
                .ok_or(DerivedTypeError::MalformedObjectLiteral(*member))?;
            for property in &shape.properties {
                let property_record = self
                    .type_payload(property.type_)
                    .ok_or(DerivedTypeError::Type(property.type_))?;
                if property_record.flags().intersects(TypeFlags::OBJECT)
                    && !property_record
                        .object_flags()
                        .contains(ObjectFlags::OBJECT_LITERAL)
                    || !property_record.flags().intersects(TypeFlags::OBJECT)
                        && property_record
                            .object_flags()
                            .intersects(ObjectFlags::REQUIRES_WIDENING)
                        && !property_record
                            .flags()
                            .intersects(TypeFlags::ANY | TypeFlags::NULLABLE)
                {
                    return Err(DerivedTypeError::UnsupportedWideningType(property.type_));
                }
                if self
                    .contextual_property_order_key(property.symbol)
                    .is_none()
                {
                    return Err(DerivedTypeError::MalformedObjectLiteral(*member));
                }
                if let Some(index) = context_names.get(&property.name).copied() {
                    context_properties[index] = property.clone();
                } else {
                    context_names.insert(property.name.clone(), context_properties.len());
                    context_properties.push(property.clone());
                }
            }
            object_shapes.push((*member, shape));
        }

        let mut constituents = Vec::with_capacity(members.len());
        for member in members {
            let record = self
                .type_payload(*member)
                .ok_or(DerivedTypeError::Type(*member))?;
            if record.flags().intersects(TypeFlags::NULLABLE) {
                constituents.push(WidenTransform::Identity(*member));
                continue;
            }
            if !record.object_flags().contains(ObjectFlags::OBJECT_LITERAL) {
                constituents.push(WidenTransform::Identity(*member));
                continue;
            }

            let (_, shape) = object_shapes
                .iter()
                .find(|(source, _)| source == member)
                .expect("each contextual object was authenticated");
            if let Some(cached) = self
                .derived_types
                .contextual_widened_types
                .get(&(union, *member))
                .copied()
            {
                if !self.contextual_object_cache_entry_is_valid(
                    union,
                    *member,
                    cached,
                    global_types.map(CanonicalArrayTargets::from_global_types),
                ) {
                    return Err(DerivedTypeError::InvalidWidenedTypeCache {
                        source: *member,
                        cached,
                    });
                }
                constituents.push(WidenTransform::ContextualCached {
                    union,
                    source: *member,
                });
                continue;
            }

            let mut properties = Vec::with_capacity(shape.properties.len());
            for property in &shape.properties {
                let property_record = self
                    .type_payload(property.type_)
                    .ok_or(DerivedTypeError::Type(property.type_))?;
                let transform = if property_record.flags().intersects(TypeFlags::OBJECT) {
                    self.plan_widened_type(property.type_, global_types, plans, visiting, planned)?
                } else if property_record
                    .object_flags()
                    .intersects(ObjectFlags::REQUIRES_WIDENING)
                {
                    WidenTransform::Identity(
                        self.intrinsic_bootstrap()
                            .ok_or(DerivedTypeError::BootstrapUninitialized)?
                            .any_type,
                    )
                } else {
                    WidenTransform::Identity(property.type_)
                };
                if (self.object_literal_getter_origin(property.symbol).is_some()
                    || self
                        .symbol(property.symbol)
                        .is_some_and(|record| record.flags() == SymbolFlags::GET_ACCESSOR))
                    && !matches!(transform, WidenTransform::Identity(type_) if type_ == property.type_)
                {
                    return Err(DerivedTypeError::UnsupportedWideningType(*member));
                }
                properties.push(WidenPropertyPlan {
                    source: property.symbol,
                    name: property.name.clone(),
                    transform,
                });
            }

            let undefined_properties = context_properties
                .iter()
                .filter(|property| {
                    !shape
                        .properties
                        .iter()
                        .any(|source| source.name == property.name)
                })
                .cloned()
                .collect::<Vec<_>>();
            for property in &undefined_properties {
                if self.object_literal_getter_origin(property.symbol).is_some()
                    || self
                        .symbol(property.symbol)
                        .is_some_and(|record| record.flags() == SymbolFlags::GET_ACCESSOR)
                {
                    return Err(DerivedTypeError::UnsupportedWideningType(*member));
                }
                if let Some(cached) = self
                    .derived_types
                    .undefined_properties
                    .get(&property.name)
                    .copied()
                    && (!self.valid_cached_undefined_property(&property.name, cached)
                        || self.contextual_property_order_key(cached).is_none())
                {
                    return Err(DerivedTypeError::MalformedObjectLiteral(*member));
                }
            }

            let indexes =
                self.plan_widened_indexes(*member, shape, global_types, plans, visiting, planned)?;
            plans.push(WidenPlan::ContextualObject {
                union,
                source: *member,
                shape: shape.clone(),
                properties,
                undefined_properties,
                indexes,
            });
            constituents.push(WidenTransform::ContextualCached {
                union,
                source: *member,
            });
        }

        debug_assert!(visiting.remove(&union));
        planned.insert(union);
        plans.push(WidenPlan::Union {
            source: union,
            constituents,
        });
        Ok(WidenTransform::Cached(union))
    }

    fn contextual_property_order_key(
        &self,
        property: SemanticSymbolId,
    ) -> Option<(usize, u32, EscapedNameRef<'_>)> {
        let record = self.symbol(property)?;
        let declaration = *record.declarations()?.first()?;
        let bound = self.source_declaration_symbol(declaration)?;
        let source = self.symbol(bound)?;
        let owner = record.parent()?;
        let SourceNodeParent::Parent(owner_declaration) = self.source_node_parent(declaration)?
        else {
            return None;
        };
        if !self.source_symbol_declarations_match(bound)
            || !self.source_symbol_declarations_match(owner)
            || (source.name() != record.name()
                && self
                    .contextual_computed_property_origin(property, owner_declaration, bound)
                    .is_none())
            || source.declarations() != record.declarations()
            || source.value_declaration() != record.value_declaration()
            || source.parent() != Some(owner)
            || self.source_declaration_symbol(owner_declaration) != Some(owner)
        {
            return None;
        }
        Some((
            self.source_file_rank(declaration.file)?,
            self.source_node_start(declaration)?,
            record.name(),
        ))
    }

    fn contextual_computed_property_origin(
        &self,
        property: SemanticSymbolId,
        owner: NodeRef,
        bound: SemanticSymbolId,
    ) -> Option<()> {
        let source_type = self.type_node_links(owner)?.resolved_type?;
        let properties =
            super::object_members::source_computed_object_named_properties(self, source_type)?;
        let name = self.symbol(property)?.name();
        let original = properties
            .into_iter()
            .find_map(|(symbol, source_name, _)| {
                (source_name.as_ref() == name
                    && self.value_symbol_links(symbol)?.target == Some(bound))
                .then_some(symbol)
            })?;

        // Follow real clone links back to the authenticated computed property.
        let mut current = property;
        let mut seen = HashSet::new();
        while current != original {
            if !seen.insert(current) {
                return None;
            }
            let record = self.symbol(current)?;
            let links = self.value_symbol_links(current)?;
            let target = links.target?;
            let type_ = links.resolved_type?;
            if !self.valid_symbol_clone(target, current, type_) {
                let target_record = self.symbol(target)?;
                let target_links = self.value_symbol_links(target)?;
                let undefined = self.intrinsic_bootstrap()?.undefined_or_missing_type;
                let expected_links = ValueSymbolLinks {
                    resolved_type: Some(undefined),
                    target: Some(target),
                    name_type: target_links.name_type,
                    ..ValueSymbolLinks::default()
                };
                // This cache entry exists before the first contextual object is published.
                if self
                    .derived_types
                    .undefined_properties
                    .get(&record.name().to_owned())
                    != Some(&current)
                    || self.get_merged_symbol(current) != Some(current)
                    || self.get_merged_symbol(target) != Some(target)
                    || record.flags()
                        != SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT | SymbolFlags::OPTIONAL
                    || target_record.flags() != SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
                    || record.check_flags() != target_record.check_flags() & CheckFlags::READONLY
                    || record.name() != target_record.name()
                    || record.declarations() != target_record.declarations()
                    || record.value_declaration() != target_record.value_declaration()
                    || record.parent() != target_record.parent()
                    || record.members().is_some()
                    || record.exports().is_some()
                    || record.export_symbol().is_some()
                    || links != &expected_links
                {
                    return None;
                }
            }
            current = target;
        }
        Some(())
    }

    /// Pinned `compareSymbols` orders each selected symbol by its retained declaration.
    fn sort_contextual_properties(&self, properties: &mut [SemanticSymbolId]) -> Option<()> {
        let mut ordered = properties
            .iter()
            .map(|property| Some((self.contextual_property_order_key(*property)?, *property)))
            .collect::<Option<Vec<_>>>()?;
        // Member names are unique, so declaration and name order resolve every tie.
        ordered.sort_unstable_by_key(|(key, _)| *key);
        for (property, (_, symbol)) in properties.iter_mut().zip(ordered) {
            *property = symbol;
        }
        Some(())
    }

    #[allow(clippy::too_many_arguments)] // Index values share the caller's widening graph.
    fn plan_widened_indexes(
        &self,
        source: TypeId,
        shape: &ObjectShape,
        global_types: Option<&CanonicalGlobalTypes>,
        plans: &mut Vec<WidenPlan>,
        visiting: &mut HashSet<TypeId>,
        planned: &mut HashSet<TypeId>,
    ) -> Result<Vec<WidenIndexPlan>, DerivedTypeError> {
        shape
            .index_infos
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|index| {
                let value = self
                    .index_info(*index)
                    .ok_or(DerivedTypeError::MalformedObjectLiteral(source))?
                    .value_type();
                Ok(WidenIndexPlan {
                    source: *index,
                    transform: self.plan_widened_type(
                        value,
                        global_types,
                        plans,
                        visiting,
                        planned,
                    )?,
                })
            })
            .collect()
    }

    fn publish_widened_indexes(
        &mut self,
        plans: Vec<WidenIndexPlan>,
    ) -> Option<Vec<super::IndexInfoId>> {
        if plans.is_empty() {
            return None;
        }
        Some(
            plans
                .into_iter()
                .map(|plan| {
                    let value = match plan.transform {
                        WidenTransform::Identity(type_) => type_,
                        WidenTransform::Cached(source) => self.derived_types.widened_types[&source],
                        WidenTransform::ContextualCached { union, source } => {
                            self.derived_types.contextual_widened_types[&(union, source)]
                        }
                    };
                    let info = self
                        .index_info(plan.source)
                        .expect("the widening plan checked its source index");
                    self.alloc_index_info(
                        info.key_type(),
                        value,
                        info.is_readonly(),
                        info.declaration(),
                        info.components().to_vec(),
                    )
                    .expect("the widening plan checked and reserved its index inputs")
                })
                .collect(),
        )
    }

    fn publish_regular_object(&mut self, plan: RegularObjectPlan) {
        let members = self.alloc_symbol_table();
        let mut properties = Vec::with_capacity(plan.properties.len());
        for property in plan.properties {
            let transformed = match property.transform {
                RegularTransform::Identity(type_) => type_,
                RegularTransform::Object(source) => *self
                    .derived_types
                    .regular_object_literals
                    .get(&source)
                    .expect("regular child objects are published before their parent"),
            };
            let property_symbol = match property.transform {
                RegularTransform::Identity(_) => property.source,
                RegularTransform::Object(_) => {
                    self.clone_symbol_with_type(property.source, transformed)
                }
            };
            assert_eq!(
                self.insert_symbol(members, property.name, property_symbol),
                Some(None)
            );
            properties.push(property_symbol);
        }
        let regular = self
            .alloc_plain_object_type(
                plan.shape.object_flags & !ObjectFlags::FRESH_LITERAL,
                Some(plan.shape.symbol),
            )
            .expect("the regular object plan validated its owner and flags");
        assert!(self.set_structured_type_members(
            regular,
            Some(members),
            (!properties.is_empty()).then_some(properties),
            None,
            None,
            plan.shape.index_infos,
        ));
        assert_eq!(plan.shape.flags, TypeFlags::OBJECT);
        assert_eq!(
            self.derived_types
                .regular_object_literals
                .insert(plan.source, regular),
            None
        );
        if self.relation_derived_cache_source_is_observable(plan.source)
            || self.relation_derived_cache_target_is_observable(regular)
        {
            self.mark_relation_inputs_dirty();
        }
    }

    fn publish_widened_type(
        &mut self,
        plan: WidenPlan,
        global_types: Option<&CanonicalGlobalTypes>,
        session: Option<&mut InstantiationSession>,
    ) -> Result<(), DerivedTypeError> {
        match plan {
            WidenPlan::Existing { source, target } => {
                assert_eq!(
                    self.derived_types.widened_types.insert(source, target),
                    None
                );
                if self.relation_derived_cache_source_is_observable(source)
                    || self.relation_derived_cache_target_is_observable(target)
                {
                    self.mark_relation_inputs_dirty();
                }
            }
            WidenPlan::Object {
                source,
                shape,
                properties: property_plans,
                indexes,
            } => {
                let members = self.alloc_symbol_table();
                let mut properties = Vec::with_capacity(property_plans.len());
                for property in property_plans {
                    let transformed = match property.transform {
                        WidenTransform::Identity(type_) => type_,
                        WidenTransform::Cached(source) => *self
                            .derived_types
                            .widened_types
                            .get(&source)
                            .expect("widened child types are published before their parent"),
                        WidenTransform::ContextualCached { union, source } => *self
                            .derived_types
                            .contextual_widened_types
                            .get(&(union, source))
                            .expect("contextual child objects are published before their parent"),
                    };
                    let original = self
                        .value_symbol_links(property.source)
                        .and_then(|links| links.resolved_type)
                        .expect("the widening plan validated the source property type");
                    let property_symbol = if transformed == original {
                        property.source
                    } else {
                        self.clone_symbol_with_type(property.source, transformed)
                    };
                    assert_eq!(
                        self.insert_symbol(members, property.name, property_symbol),
                        Some(None)
                    );
                    properties.push(property_symbol);
                }
                let retained = shape.object_flags
                    & (ObjectFlags::JS_LITERAL | ObjectFlags::NON_INFERRABLE_TYPE);
                let widened = self
                    .alloc_plain_object_type(ObjectFlags::ANONYMOUS | retained, Some(shape.symbol))
                    .expect("the widened object plan validated its owner and flags");
                let index_infos = self.publish_widened_indexes(indexes);
                assert!(self.set_structured_type_members(
                    widened,
                    Some(members),
                    (!properties.is_empty()).then_some(properties),
                    None,
                    None,
                    index_infos,
                ));
                assert_eq!(
                    self.derived_types.widened_types.insert(source, widened),
                    None
                );
                if self.relation_derived_cache_source_is_observable(source)
                    || self.relation_derived_cache_target_is_observable(widened)
                {
                    self.mark_relation_inputs_dirty();
                }
            }
            WidenPlan::ContextualObject {
                union,
                source,
                shape,
                properties: property_plans,
                undefined_properties,
                indexes,
            } => {
                let members = self.alloc_symbol_table();
                let mut properties =
                    Vec::with_capacity(property_plans.len() + undefined_properties.len());
                for property in property_plans {
                    let transformed = match property.transform {
                        WidenTransform::Identity(type_) => type_,
                        WidenTransform::Cached(source) => *self
                            .derived_types
                            .widened_types
                            .get(&source)
                            .expect("widened child types are published before their parent"),
                        WidenTransform::ContextualCached { union, source } => *self
                            .derived_types
                            .contextual_widened_types
                            .get(&(union, source))
                            .expect("contextual child objects are published before their parent"),
                    };
                    let original = self
                        .value_symbol_links(property.source)
                        .and_then(|links| links.resolved_type)
                        .expect("the contextual plan authenticated its source property");
                    let property_symbol = if transformed == original {
                        property.source
                    } else {
                        self.clone_symbol_with_type(property.source, transformed)
                    };
                    assert_eq!(
                        self.insert_symbol(members, property.name, property_symbol),
                        Some(None)
                    );
                    properties.push(property_symbol);
                }

                for property in undefined_properties {
                    let property_symbol = self
                        .derived_types
                        .undefined_properties
                        .get(&property.name)
                        .copied()
                        .unwrap_or_else(|| {
                            let symbol = self.clone_undefined_property(property.symbol);
                            assert_eq!(
                                self.derived_types
                                    .undefined_properties
                                    .insert(property.name.clone(), symbol),
                                None
                            );
                            symbol
                        });
                    assert_eq!(
                        self.insert_symbol(members, property.name, property_symbol),
                        Some(None)
                    );
                    properties.push(property_symbol);
                }
                self.sort_contextual_properties(&mut properties)
                    .expect("the contextual plan checked every own, donor, and cached declaration");

                let retained = shape.object_flags
                    & (ObjectFlags::JS_LITERAL | ObjectFlags::NON_INFERRABLE_TYPE);
                let widened = self
                    .alloc_plain_object_type(ObjectFlags::ANONYMOUS | retained, Some(shape.symbol))
                    .expect("the contextual object plan authenticated its owner and flags");
                let index_infos = self.publish_widened_indexes(indexes);
                assert!(self.set_structured_type_members(
                    widened,
                    Some(members),
                    (!properties.is_empty()).then_some(properties),
                    None,
                    None,
                    index_infos,
                ));
                assert_eq!(
                    self.derived_types
                        .contextual_widened_types
                        .insert((union, source), widened),
                    None
                );
                if self.relation_derived_cache_source_is_observable(union)
                    || self.relation_derived_cache_source_is_observable(source)
                    || self.relation_derived_cache_target_is_observable(widened)
                {
                    self.mark_relation_inputs_dirty();
                }
            }
            WidenPlan::Array {
                source,
                element,
                readonly,
            } => {
                let element = match element {
                    WidenTransform::Identity(type_) => type_,
                    WidenTransform::Cached(source) => *self
                        .derived_types
                        .widened_types
                        .get(&source)
                        .expect("widened array elements are published before their parent"),
                    WidenTransform::ContextualCached { union, source } => *self
                        .derived_types
                        .contextual_widened_types
                        .get(&(union, source))
                        .expect("contextual array elements are published before their parent"),
                };
                let widened = self
                    .create_canonical_array_type(
                        global_types.expect("array plans require authoritative global types"),
                        element,
                        readonly,
                    )
                    .expect("the widening plan preflighted its canonical array target");
                assert_eq!(
                    self.derived_types.widened_types.insert(source, widened),
                    None
                );
                if self.relation_derived_cache_source_is_observable(source)
                    || self.relation_derived_cache_target_is_observable(widened)
                {
                    self.mark_relation_inputs_dirty();
                }
            }
            WidenPlan::Union {
                source,
                constituents,
            } => {
                let members = constituents
                    .into_iter()
                    .map(|constituent| match constituent {
                        WidenTransform::Identity(type_) => type_,
                        WidenTransform::Cached(source) => *self
                            .derived_types
                            .widened_types
                            .get(&source)
                            .expect("widened union members are published before their parent"),
                        WidenTransform::ContextualCached { union, source } => *self
                            .derived_types
                            .contextual_widened_types
                            .get(&(union, source))
                            .expect("contextual union members are published before their parent"),
                    })
                    .collect::<Vec<_>>();
                let reduction = if members.iter().any(|member| {
                    matches!(
                        self.type_payload(*member).map(TypeRecord::data),
                        Some(TypeData::Object(object)) if object.structured.properties.is_none()
                    )
                }) {
                    super::bootstrap::UnionReduction::Subtype
                } else {
                    super::bootstrap::UnionReduction::Literal
                };
                let widened = if let Some(global_types) = global_types {
                    match session {
                        Some(session) => self
                            .expression_union_type_with_global_types_and_session(
                                global_types,
                                &members,
                                reduction,
                                session,
                            )
                            .map_err(|error| widening_union_error(source, error))?,
                        None => self
                            .expression_union_type_with_global_types(
                                global_types,
                                &members,
                                reduction,
                            )
                            .expect("preflighted widened union members remain canonical"),
                    }
                } else {
                    let mut prepared = self
                        .prepare_type_query_types(&[], &[], &[], 1, 0)
                        .expect("widened union preparation was preflighted");
                    self.literal_union_type_prepared(&members, None, &mut prepared)
                        .expect("preflighted widened union members remain canonical")
                };
                assert_eq!(
                    self.derived_types.widened_types.insert(source, widened),
                    None
                );
                if self.relation_derived_cache_source_is_observable(source)
                    || self.relation_derived_cache_target_is_observable(widened)
                {
                    self.mark_relation_inputs_dirty();
                }
            }
        }
        Ok(())
    }

    fn clone_symbol_with_type(
        &mut self,
        source: SemanticSymbolId,
        type_: TypeId,
    ) -> SemanticSymbolId {
        let (data, name_type) = {
            let source_record = self
                .symbol(source)
                .expect("the derived-type plan validated its source property");
            let mut data = SymbolData::new(source_record.flags(), source_record.name().to_owned());
            data.check_flags = source_record.check_flags() & CheckFlags::READONLY;
            data.declarations = source_record.declarations().map(<[NodeRef]>::to_vec);
            data.value_declaration = source_record.value_declaration();
            data.parent = source_record.parent();
            let name_type = self
                .value_symbol_links(source)
                .and_then(|links| links.name_type);
            (data, name_type)
        };
        let clone = self
            .alloc_symbol(data)
            .expect("the derived-type plan validated clone provenance");
        assert!(self.set_value_symbol_links(
            clone,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                target: Some(source),
                name_type,
                ..ValueSymbolLinks::default()
            },
        ));
        clone
    }

    fn clone_undefined_property(&mut self, source: SemanticSymbolId) -> SemanticSymbolId {
        let undefined = self
            .intrinsic_bootstrap()
            .expect("contextual widening requires intrinsic bootstrap")
            .undefined_or_missing_type;
        let (data, name_type) = {
            let source_record = self
                .symbol(source)
                .expect("the contextual plan authenticated its donor property");
            let mut data = SymbolData::new(
                source_record.flags() | SymbolFlags::OPTIONAL,
                source_record.name().to_owned(),
            );
            data.check_flags = source_record.check_flags() & CheckFlags::READONLY;
            data.declarations = source_record.declarations().map(<[NodeRef]>::to_vec);
            data.value_declaration = source_record.value_declaration();
            data.parent = source_record.parent();
            let name_type = self
                .value_symbol_links(source)
                .and_then(|links| links.name_type);
            (data, name_type)
        };
        let clone = self
            .alloc_symbol(data)
            .expect("the contextual plan authenticated optional clone provenance");
        assert!(self.set_value_symbol_links(
            clone,
            ValueSymbolLinks {
                resolved_type: Some(undefined),
                target: Some(source),
                name_type,
                ..ValueSymbolLinks::default()
            },
        ));
        clone
    }

    fn contextual_widened_source(&self, target: TypeId) -> Option<(TypeId, TypeId)> {
        let mut found = None;
        for (&source, &cached) in &self.derived_types.contextual_widened_types {
            if cached == target && found.replace(source).is_some() {
                return None;
            }
        }
        found
    }

    fn valid_cached_undefined_property(
        &self,
        name: &EscapedName,
        property: SemanticSymbolId,
    ) -> bool {
        let Some(bootstrap) = self.intrinsic_bootstrap() else {
            return false;
        };
        if self.derived_types.undefined_properties.get(name) != Some(&property)
            || self.get_merged_symbol(property) != Some(property)
        {
            return false;
        }
        let Some(record) = self.symbol(property) else {
            return false;
        };
        let Some(links) = self.value_symbol_links(property) else {
            return false;
        };
        let Some(donor) = links.target else {
            return false;
        };
        let Some(donor_record) = self.symbol(donor) else {
            return false;
        };
        let Some(donor_links) = self.value_symbol_links(donor) else {
            return false;
        };
        let expected_links = ValueSymbolLinks {
            resolved_type: Some(bootstrap.undefined_or_missing_type),
            target: Some(donor),
            name_type: donor_links.name_type,
            ..ValueSymbolLinks::default()
        };
        if record.flags()
            != (SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT | SymbolFlags::OPTIONAL)
            || donor_record.flags() != (SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
            || record.check_flags() != donor_record.check_flags() & CheckFlags::READONLY
            || record.name() != name.as_ref()
            || record.name() != donor_record.name()
            || record.declarations() != donor_record.declarations()
            || record.value_declaration() != donor_record.value_declaration()
            || record.parent() != donor_record.parent()
            || record.parent().is_none()
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || links != &expected_links
            || self.get_merged_symbol(donor) != Some(donor)
        {
            return false;
        }

        self.derived_types
            .contextual_widened_types
            .keys()
            .any(|(union, _)| {
                let Some(TypeData::Union(members)) =
                    self.type_payload(*union).map(TypeRecord::data)
                else {
                    return false;
                };
                members.union.types.iter().any(|member| {
                    let mut regular_visiting = HashSet::new();
                    self.validated_widening_object_shape(*member, &mut regular_visiting)
                        .is_some_and(|shape| {
                            shape
                                .properties
                                .iter()
                                .any(|candidate| candidate.symbol == donor)
                        })
                })
            })
    }

    fn contextual_optional_property_is_valid(
        &self,
        union: TypeId,
        source: TypeId,
        receiver: TypeId,
        property: SemanticSymbolId,
    ) -> bool {
        if self
            .derived_types
            .contextual_widened_types
            .get(&(union, source))
            != Some(&receiver)
        {
            return false;
        }
        let Some(record) = self.type_payload(receiver) else {
            return false;
        };
        let Some(owner) = record.symbol() else {
            return false;
        };
        let TypeData::Object(object) = record.data() else {
            return false;
        };
        let Some(property_record) = self.symbol(property) else {
            return false;
        };
        let Some(members) = object.structured.members else {
            return false;
        };
        if property_record.parent() == Some(owner)
            || self
                .symbol_table(members)
                .and_then(|table| table.get(property_record.name()))
                != Some(property)
            || object
                .structured
                .properties
                .as_deref()
                .is_none_or(|properties| !properties.contains(&property))
        {
            return false;
        }

        let name = property_record.name().to_owned();
        if !self.valid_cached_undefined_property(&name, property) {
            return false;
        }
        let mut regular_visiting = HashSet::new();
        let Some(shape) = self.validated_widening_object_shape(source, &mut regular_visiting)
        else {
            return false;
        };
        if shape.symbol != owner
            || shape
                .properties
                .iter()
                .any(|candidate| candidate.name == name)
        {
            return false;
        }
        self.contextual_sibling_properties(union)
            .is_some_and(|properties| properties.iter().any(|candidate| candidate.name == name))
    }

    // Scalar siblings keep their exact type and add no contextual properties.
    // Fresh literals remain outside this regular-literal admission.
    fn is_non_widening_contextual_scalar(&self, type_: TypeId) -> bool {
        let Some(record) = self.type_payload(type_) else {
            return false;
        };
        if record.object_flags() != ObjectFlags::NONE {
            return false;
        }
        let supported = match record.data() {
            TypeData::Intrinsic(_) => matches!(
                record.flags(),
                TypeFlags::STRING | TypeFlags::NUMBER | TypeFlags::BIG_INT | TypeFlags::ES_SYMBOL
            ),
            TypeData::Literal(literal) => {
                literal.regular_type == type_
                    && matches!(
                        record.flags(),
                        TypeFlags::STRING_LITERAL
                            | TypeFlags::NUMBER_LITERAL
                            | TypeFlags::BIG_INT_LITERAL
                            | TypeFlags::BOOLEAN_LITERAL
                    )
            }
            _ => false,
        };
        supported && self.validate_union_constituent(type_).is_ok()
    }

    fn contextual_sibling_properties(&self, union: TypeId) -> Option<Vec<PropertyShape>> {
        let TypeData::Union(data) = self.type_payload(union)?.data() else {
            return None;
        };
        let mut properties = Vec::<PropertyShape>::new();
        let mut names = HashMap::<EscapedName, usize>::new();
        for member in &data.union.types {
            let record = self.type_payload(*member)?;
            if record.flags().intersects(TypeFlags::NULLABLE)
                || self.is_non_widening_contextual_scalar(*member)
            {
                continue;
            }
            if !record.object_flags().contains(ObjectFlags::OBJECT_LITERAL) {
                if !matches!(
                    validate_resolved_declared_property_object(self, *member),
                    DeclaredPropertyObjectValidation::Valid(_)
                ) {
                    return None;
                }
                continue;
            }
            let mut regular_visiting = HashSet::new();
            let shape = self.validated_widening_object_shape(*member, &mut regular_visiting)?;
            for property in shape.properties {
                let record = self.type_payload(property.type_)?;
                if record.flags().intersects(TypeFlags::OBJECT)
                    && !record.object_flags().contains(ObjectFlags::OBJECT_LITERAL)
                    || !record.flags().intersects(TypeFlags::OBJECT)
                        && record
                            .object_flags()
                            .intersects(ObjectFlags::REQUIRES_WIDENING)
                        && !record
                            .flags()
                            .intersects(TypeFlags::ANY | TypeFlags::NULLABLE)
                {
                    return None;
                }
                if let Some(index) = names.get(&property.name).copied() {
                    properties[index] = property;
                } else {
                    names.insert(property.name.clone(), properties.len());
                    properties.push(property);
                }
            }
        }
        Some(properties)
    }

    fn is_fresh_object_literal(&self, type_: TypeId) -> bool {
        self.type_payload(type_).is_some_and(|record| {
            record
                .object_flags()
                .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL)
        })
    }

    fn preflight_fresh_object_getters(&self, type_: TypeId) -> Result<(), DerivedTypeError> {
        let record = self
            .type_payload(type_)
            .ok_or(DerivedTypeError::Type(type_))?;
        if !record
            .object_flags()
            .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL)
        {
            return Ok(());
        }
        for property in record
            .data()
            .structured()
            .and_then(|structured| structured.properties.as_deref())
            .unwrap_or_default()
        {
            if self.object_literal_getter_origin(*property).is_none()
                && self
                    .symbol(*property)
                    .is_none_or(|record| record.flags() != SymbolFlags::GET_ACCESSOR)
            {
                continue;
            }
            let getter = object_literal_getter_projection(self, *property)
                .map_err(|_| DerivedTypeError::MalformedObjectLiteral(type_))?;
            if getter.object_type != type_ || record.symbol() != Some(getter.owner) {
                return Err(DerivedTypeError::MalformedObjectLiteral(type_));
            }
            getter
                .require_type()
                .map_err(|_| DerivedTypeError::UnresolvedPropertyType(*property))?;
        }
        Ok(())
    }

    /// A published method clone must keep its source proof if its flags change.
    pub(super) fn object_literal_property_requires_method_proof(
        &self,
        symbol: SemanticSymbolId,
    ) -> bool {
        self.symbol(symbol)
            .is_some_and(|record| record.flags().intersects(SymbolFlags::METHOD))
            || self
                .object_literal_property_clone_origin(symbol)
                .is_some_and(|origin| {
                    self.source_callable_type_for_owner(origin.source())
                        .is_some()
                })
    }

    /// Reads the publisher's exact method clone without resolving a new callable.
    pub(super) fn object_literal_method_clone_type(
        &self,
        symbol: SemanticSymbolId,
        owner: SemanticSymbolId,
    ) -> Option<TypeId> {
        let origin = self.object_literal_property_clone_origin(symbol)?;
        let cloned = self.symbol(symbol)?;
        let source = self.symbol(origin.source())?;
        let [declaration] = source.declarations()? else {
            return None;
        };
        let callable = self.source_callable_type_for_owner(origin.source())?;
        let provenance = self.source_callable_provenance(callable)?;
        if origin.symbol() != symbol
            || origin.source() == symbol
            || self.symbol(owner)?.value_declaration() != Some(origin.owner())
            || self.source_node_parent(*declaration)
                != Some(SourceNodeParent::Parent(origin.owner()))
            || !self.source_symbol_declarations_match(origin.source())
            || !self.source_object_literal_method_owner_is_exact(*declaration, origin.source())
            || source.parent() != Some(owner)
            || cloned.flags()
                != SymbolFlags::METHOD | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            || cloned.check_flags() != CheckFlags::NONE
            || cloned.name() != source.name()
            || cloned.name().is_internal()
            || cloned.name().is_private_identifier()
            || cloned.name().is_late_bound()
            || cloned.declarations() != source.declarations()
            || cloned.value_declaration() != Some(*declaration)
            || cloned.parent() != Some(owner)
            || cloned.members().is_some()
            || cloned.exports().is_some()
            || cloned.export_symbol().is_some()
            || self.get_merged_symbol(symbol) != Some(symbol)
            || self.value_symbol_links(symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(callable),
                    target: Some(origin.source()),
                    ..ValueSymbolLinks::default()
                })
            || provenance.family != super::store::SourceCallableFamily::ObjectLiteralMethod
            || provenance.declaration != *declaration
            || provenance.owner_symbol != origin.source()
            || !matches!(
                super::source_callables::validate_stored_source_callable(self, callable),
                super::source_callables::StoredSourceCallableValidation::Valid(_)
            )
        {
            return None;
        }
        Some(callable)
    }

    fn fresh_object_shape(&self, type_: TypeId) -> Option<ObjectShape> {
        let record = self.type_payload(type_)?;
        let TypeData::Object(object) = record.data() else {
            return None;
        };
        if object.source_computed_literal.is_some()
            || super::object_members::source_object_requires_computed_proof(self, type_)
        {
            let properties =
                super::object_members::source_computed_object_named_properties(self, type_)?;
            return Some(ObjectShape {
                flags: record.flags(),
                object_flags: record.object_flags(),
                symbol: record.symbol()?,
                members: object.structured.members?,
                properties: properties
                    .into_iter()
                    .map(|(symbol, name, type_)| PropertyShape {
                        symbol,
                        name,
                        type_,
                    })
                    .collect(),
                index_infos: object.structured.index_infos.clone(),
            });
        }
        let owner = record.symbol()?;
        let owner_record = self.symbol(owner)?;
        let [owner_declaration] = owner_record.declarations()? else {
            return None;
        };
        if record.flags() != TypeFlags::OBJECT
            || record.alias().is_some()
            || !valid_object_tail(object)
            || !valid_structured_tail(&object.structured)
            || self.get_merged_symbol(owner) != Some(owner)
            || owner_record.flags() != SymbolFlags::OBJECT_LITERAL
            || owner_record.check_flags() != CheckFlags::NONE
            || owner_record.name() != InternalSymbolName::Object.as_ref()
            || owner_record.value_declaration() != Some(*owner_declaration)
            || owner_record.parent().is_some()
            || owner_record.exports().is_some()
            || owner_record.export_symbol().is_some()
            || self.source_node_kind(*owner_declaration)
                != Some(SyntaxKind::ObjectLiteralExpression)
        {
            return None;
        }

        let members = object.structured.members?;
        if owner_record.members() == Some(members) {
            return None;
        }
        let table = self.symbol_table(members)?;
        let property_symbols = optional_nonempty_slice(object.structured.properties.as_deref());
        let properties = property_symbols?;
        if table.len() != properties.len()
            || owner_record.members().is_some() == properties.is_empty()
        {
            return None;
        }
        let raw_table = match owner_record.members() {
            Some(raw_members) => Some(self.symbol_table(raw_members)?),
            None => None,
        };
        if raw_table.is_some_and(|raw| raw.len() != properties.len()) {
            return None;
        }
        let first_ordinary_property = properties.iter().find(|property| {
            self.object_literal_getter_origin(**property).is_none()
                && self
                    .symbol(**property)
                    .is_none_or(|record| record.flags() != SymbolFlags::GET_ACCESSOR)
        });
        let expected_property_checks = match first_ordinary_property {
            Some(property) if self.symbol(*property)?.check_flags() == CheckFlags::READONLY => {
                if !self.readonly_object_literal_source(*owner_declaration) {
                    return None;
                }
                CheckFlags::READONLY
            }
            Some(property) if self.symbol(*property)?.check_flags() != CheckFlags::NONE => {
                return None;
            }
            _ => CheckFlags::NONE,
        };

        let mut expected_flags = ObjectFlags::ANONYMOUS
            | ObjectFlags::OBJECT_LITERAL
            | ObjectFlags::FRESH_LITERAL
            | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL
            | ObjectFlags::MEMBERS_RESOLVED;
        let mut seen_properties = HashSet::with_capacity(properties.len());
        let mut seen_raw = HashSet::with_capacity(properties.len());
        let mut result = Vec::with_capacity(properties.len());
        for property in properties {
            if !seen_properties.insert(*property) {
                return None;
            }
            let property_record = self.symbol(*property)?;
            if self.object_literal_getter_origin(*property).is_some()
                || property_record.flags() == SymbolFlags::GET_ACCESSOR
            {
                let getter = object_literal_getter_projection(self, *property).ok()?;
                let property_type = getter.require_type().ok()?;
                if getter.object_type != type_
                    || getter.owner != owner
                    || !seen_raw.insert(*property)
                    || table.get(property_record.name()) != Some(*property)
                    || raw_table.and_then(|raw| raw.get(property_record.name())) != Some(*property)
                {
                    return None;
                }
                result.push(PropertyShape {
                    symbol: *property,
                    name: property_record.name().to_owned(),
                    type_: property_type,
                });
                continue;
            }
            if self.object_literal_property_requires_method_proof(*property) {
                let property_type = self.object_literal_method_clone_type(*property, owner)?;
                let raw = self
                    .object_literal_property_clone_origin(*property)?
                    .source();
                if expected_property_checks != CheckFlags::NONE
                    || !seen_raw.insert(raw)
                    || table.get(property_record.name()) != Some(*property)
                    || raw_table.and_then(|raw| raw.get(property_record.name())) != Some(raw)
                {
                    return None;
                }
                expected_flags |= self.type_payload(property_type)?.object_flags()
                    & ObjectFlags::PROPAGATING_FLAGS;
                result.push(PropertyShape {
                    symbol: *property,
                    name: property_record.name().to_owned(),
                    type_: property_type,
                });
                continue;
            }
            let property_links = self.value_symbol_links(*property)?;
            let property_type = property_links.resolved_type?;
            let property_type_record = self.type_payload(property_type)?;
            let raw = property_links.target?;
            if raw == *property || !seen_raw.insert(raw) {
                return None;
            }
            let raw_record = self.symbol(raw)?;
            let expected_links = ValueSymbolLinks {
                resolved_type: Some(property_type),
                target: Some(raw),
                ..ValueSymbolLinks::default()
            };
            if property_links != &expected_links
                || property_record.flags() != (SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
                || property_record.check_flags() != expected_property_checks
                || expected_property_checks == CheckFlags::READONLY
                    && !matches!(
                        property_type_record.data(),
                        TypeData::Literal(literal) if literal.regular_type == property_type
                    )
                || property_record.parent() != Some(owner)
                || property_record.members().is_some()
                || property_record.exports().is_some()
                || property_record.export_symbol().is_some()
                || self.get_merged_symbol(*property) != Some(*property)
                || raw_record.flags() != SymbolFlags::PROPERTY
                || raw_record.check_flags() != CheckFlags::NONE
                || raw_record.name() != property_record.name()
                || raw_record.declarations() != property_record.declarations()
                || raw_record.value_declaration() != property_record.value_declaration()
                || raw_record.parent() != Some(owner)
                || raw_record.members().is_some()
                || raw_record.exports().is_some()
                || raw_record.export_symbol().is_some()
                || self.get_merged_symbol(raw) != Some(raw)
                || self
                    .value_symbol_links(raw)
                    .is_some_and(|links| links != &ValueSymbolLinks::default())
            {
                return None;
            }
            let [declaration] = property_record.declarations()? else {
                return None;
            };
            if property_record.value_declaration() != Some(*declaration)
                || !matches!(
                    self.source_node_kind(*declaration),
                    Some(SyntaxKind::PropertyAssignment | SyntaxKind::ShorthandPropertyAssignment)
                )
                || table.get(property_record.name()) != Some(*property)
                || raw_table.and_then(|raw| raw.get(raw_record.name())) != Some(raw)
            {
                return None;
            }
            expected_flags |= property_type_record.object_flags() & ObjectFlags::PROPAGATING_FLAGS;
            result.push(PropertyShape {
                symbol: *property,
                name: property_record.name().to_owned(),
                type_: property_type,
            });
        }
        if record.object_flags() != expected_flags
            || raw_table.is_some_and(|raw| raw.iter().any(|(_, id)| !seen_raw.contains(&id)))
        {
            return None;
        }
        Some(ObjectShape {
            flags: record.flags(),
            object_flags: record.object_flags(),
            symbol: owner,
            members,
            properties: result,
            index_infos: None,
        })
    }

    fn readonly_object_literal_source(&self, declaration: NodeRef) -> bool {
        let mut current = declaration;
        while let Some(SourceNodeParent::Parent(parent)) = self.source_node_parent(current) {
            match self.source_node_kind(parent) {
                Some(SyntaxKind::ParenthesizedExpression) => current = parent,
                Some(SyntaxKind::AsExpression | SyntaxKind::TypeAssertionExpression) => {
                    return true;
                }
                _ => return false,
            }
        }
        false
    }

    fn resolved_object_shape(&self, type_: TypeId) -> Option<ObjectShape> {
        let record = self.type_payload(type_)?;
        let TypeData::Object(object) = record.data() else {
            return None;
        };
        if record.flags() != TypeFlags::OBJECT
            || record.alias().is_some()
            || !valid_object_tail(object)
            || !valid_structured_tail_with_indexes(&object.structured)
            || object.source_computed_literal.is_some()
        {
            return None;
        }
        let symbol = record.symbol()?;
        let members = object.structured.members?;
        let table = self.symbol_table(members)?;
        let property_symbols = optional_nonempty_slice(object.structured.properties.as_deref())?;
        if table.len() != property_symbols.len() {
            return None;
        }
        let mut seen = HashSet::with_capacity(property_symbols.len());
        let mut properties = Vec::with_capacity(property_symbols.len());
        for property in property_symbols {
            if !seen.insert(*property) {
                return None;
            }
            let property_record = self.symbol(*property)?;
            let property_type = self.value_symbol_links(*property)?.resolved_type?;
            self.type_payload(property_type)?;
            if table.get(property_record.name()) != Some(*property)
                || property_record.parent() != Some(symbol)
                    && !self.validate_contextual_widened_object_property(type_, *property)
            {
                return None;
            }
            properties.push(PropertyShape {
                symbol: *property,
                name: property_record.name().to_owned(),
                type_: property_type,
            });
        }
        Some(ObjectShape {
            flags: record.flags(),
            object_flags: record.object_flags(),
            symbol,
            members,
            properties,
            index_infos: object.structured.index_infos.clone(),
        })
    }

    fn validated_widening_object_shape(
        &self,
        type_: TypeId,
        regular_visiting: &mut HashSet<TypeId>,
    ) -> Option<ObjectShape> {
        let record = self.type_payload(type_)?;
        if record.flags() != TypeFlags::OBJECT
            || !record.object_flags().contains(ObjectFlags::OBJECT_LITERAL)
        {
            return None;
        }
        if record.object_flags().contains(ObjectFlags::FRESH_LITERAL) {
            return self.fresh_object_shape(type_);
        }
        self.observe_relation_derived_cache_target_read(type_);
        let mut source = None;
        for (candidate, cached) in &self.derived_types.regular_object_literals {
            if *cached == type_ && source.replace(*candidate).is_some() {
                return None;
            }
        }
        let source = source?;
        if !self.regular_cache_entry_is_valid(source, type_, regular_visiting) {
            return None;
        }
        self.resolved_object_shape(type_)
    }

    fn regular_cache_entry_is_valid(
        &self,
        source: TypeId,
        target: TypeId,
        visiting: &mut HashSet<TypeId>,
    ) -> bool {
        self.observe_relation_derived_cache_source_read(source);
        if !visiting.insert(source) {
            return false;
        }
        let valid = (|| {
            let source_shape = self.fresh_object_shape(source)?;
            let target_shape = self.resolved_object_shape(target)?;
            if source == target
                || target_shape.flags != source_shape.flags
                || target_shape.object_flags
                    != source_shape.object_flags & !ObjectFlags::FRESH_LITERAL
                || target_shape.symbol != source_shape.symbol
                || target_shape.members == source_shape.members
                || target_shape.properties.len() != source_shape.properties.len()
                || target_shape.index_infos != source_shape.index_infos
            {
                return None;
            }
            for (source_property, target_property) in
                source_shape.properties.iter().zip(&target_shape.properties)
            {
                let expected_type = if self.is_fresh_object_literal(source_property.type_) {
                    let cached = self
                        .derived_types
                        .regular_object_literals
                        .get(&source_property.type_)
                        .copied()?;
                    if !self.regular_cache_entry_is_valid(source_property.type_, cached, visiting) {
                        return None;
                    }
                    cached
                } else {
                    source_property.type_
                };
                if target_property.name != source_property.name
                    || target_property.type_ != expected_type
                    || if expected_type == source_property.type_ {
                        target_property.symbol != source_property.symbol
                    } else {
                        !self.valid_symbol_clone(
                            source_property.symbol,
                            target_property.symbol,
                            expected_type,
                        )
                    }
                {
                    return None;
                }
            }
            Some(())
        })()
        .is_some();
        visiting.remove(&source);
        valid
    }

    fn widened_cache_entry_is_valid(
        &self,
        source: TypeId,
        target: TypeId,
        visiting: &mut HashSet<TypeId>,
        regular_visiting: &mut HashSet<TypeId>,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        self.observe_relation_derived_cache_source_read(source);
        let Some(source_record) = self.type_payload(source) else {
            return false;
        };
        if !source_record
            .object_flags()
            .intersects(ObjectFlags::REQUIRES_WIDENING)
        {
            return false;
        }
        if source_record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::NULLABLE)
        {
            return self
                .intrinsic_bootstrap()
                .is_some_and(|bootstrap| target == bootstrap.any_type);
        }
        if matches!(source_record.data(), TypeData::Union(_)) {
            return self.widened_union_cache_entry_is_valid(
                source,
                target,
                visiting,
                regular_visiting,
                array_targets,
            );
        }
        if let Some(array_targets) = array_targets {
            let source_array =
                match self.canonical_array_reference_with_targets(array_targets, source) {
                    Ok(Some(source_array)) => source_array,
                    Ok(None) => {
                        return self.widened_object_cache_entry_is_valid(
                            source,
                            target,
                            visiting,
                            regular_visiting,
                            Some(array_targets),
                        );
                    }
                    Err(_) => return false,
                };
            if !visiting.insert(source) {
                return false;
            }
            let valid = (|| {
                let target_array = self
                    .canonical_array_reference_with_targets(array_targets, target)
                    .ok()??;
                if target_array.array_literal
                    || target_array.readonly != source_array.readonly
                    || target != target_array.base_type
                {
                    return None;
                }
                let element_record = self.type_payload(source_array.element_type)?;
                let expected_element = if element_record
                    .object_flags()
                    .intersects(ObjectFlags::REQUIRES_WIDENING)
                {
                    let cached = self
                        .derived_types
                        .widened_types
                        .get(&source_array.element_type)
                        .copied()?;
                    if !self.widened_cache_entry_is_valid(
                        source_array.element_type,
                        cached,
                        visiting,
                        regular_visiting,
                        Some(array_targets),
                    ) {
                        return None;
                    }
                    cached
                } else {
                    source_array.element_type
                };
                (target_array.element_type == expected_element).then_some(())
            })()
            .is_some();
            debug_assert!(visiting.remove(&source));
            return valid;
        }
        self.widened_object_cache_entry_is_valid(source, target, visiting, regular_visiting, None)
    }

    fn widened_union_cache_entry_is_valid(
        &self,
        source: TypeId,
        target: TypeId,
        visiting: &mut HashSet<TypeId>,
        regular_visiting: &mut HashSet<TypeId>,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        let Some(TypeData::Union(source_union)) = self.type_payload(source).map(TypeRecord::data)
        else {
            return false;
        };
        let source_valid = match array_targets {
            Some(targets) => self.validate_union_constituent_with_array_targets(targets, source),
            None => self.validate_union_constituent(source),
        };
        if source_valid.is_err() || !visiting.insert(source) {
            return false;
        }

        let valid = (|| {
            let mut expected = Vec::with_capacity(source_union.union.types.len());
            for constituent in &source_union.union.types {
                let record = self.type_payload(*constituent)?;
                let widened = if !record.flags().intersects(TypeFlags::NULLABLE)
                    && record
                        .object_flags()
                        .intersects(ObjectFlags::REQUIRES_WIDENING)
                {
                    if record.object_flags().contains(ObjectFlags::OBJECT_LITERAL) {
                        let cached = *self
                            .derived_types
                            .contextual_widened_types
                            .get(&(source, *constituent))?;
                        if !self.contextual_object_cache_entry_is_valid(
                            source,
                            *constituent,
                            cached,
                            array_targets,
                        ) {
                            return None;
                        }
                        cached
                    } else {
                        let cached = *self.derived_types.widened_types.get(constituent)?;
                        if !self.widened_cache_entry_is_valid(
                            *constituent,
                            cached,
                            visiting,
                            regular_visiting,
                            array_targets,
                        ) {
                            return None;
                        }
                        cached
                    }
                } else {
                    *constituent
                };
                if !expected.contains(&widened) {
                    expected.push(widened);
                }
            }

            let target_valid = match array_targets {
                Some(targets) => {
                    self.validate_cached_union_result_with_array_targets(targets, target, None)
                }
                None => self.validate_cached_union_result(target, None),
            };
            if target_valid.is_err() {
                return None;
            }
            match self.type_payload(target)?.data() {
                TypeData::Union(union) => (union.union.types.len() == expected.len()
                    && expected
                        .iter()
                        .all(|constituent| union.union.types.contains(constituent)))
                .then_some(()),
                _ => (expected.as_slice() == [target]).then_some(()),
            }
        })()
        .is_some();
        debug_assert!(visiting.remove(&source));
        valid
    }

    fn contextual_object_cache_entry_is_valid(
        &self,
        union: TypeId,
        source: TypeId,
        target: TypeId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        self.observe_relation_derived_cache_source_read(union);
        self.observe_relation_derived_cache_source_read(source);
        if source == target
            || self
                .derived_types
                .contextual_widened_types
                .get(&(union, source))
                != Some(&target)
        {
            return false;
        }
        let source_valid = match array_targets {
            Some(targets) => self.validate_union_constituent_with_array_targets(targets, union),
            None => self.validate_union_constituent(union),
        };
        if source_valid.is_err() {
            return false;
        }
        let Some(TypeData::Union(union_data)) = self.type_payload(union).map(TypeRecord::data)
        else {
            return false;
        };
        if !union_data.union.types.contains(&source) {
            return false;
        }

        let mut regular_visiting = HashSet::new();
        let Some(source_shape) =
            self.validated_widening_object_shape(source, &mut regular_visiting)
        else {
            return false;
        };
        let Some(target_shape) = self.resolved_object_shape(target) else {
            return false;
        };
        let Some(context_properties) = self.contextual_sibling_properties(union) else {
            return false;
        };
        let missing_properties = context_properties
            .iter()
            .filter(|property| {
                !source_shape
                    .properties
                    .iter()
                    .any(|source| source.name == property.name)
            })
            .collect::<Vec<_>>();
        let retained = source_shape.object_flags
            & (ObjectFlags::JS_LITERAL | ObjectFlags::NON_INFERRABLE_TYPE);
        if target_shape.flags != TypeFlags::OBJECT
            || target_shape.object_flags
                != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED | retained
            || target_shape.symbol != source_shape.symbol
            || target_shape.members == source_shape.members
            || !self.widened_indexes_are_valid(
                &source_shape,
                &target_shape,
                &mut HashSet::from([source]),
                &mut regular_visiting,
                array_targets,
            )
            || target_shape.properties.len()
                != source_shape.properties.len() + missing_properties.len()
        {
            return false;
        }

        let mut expected_properties = Vec::with_capacity(target_shape.properties.len());
        for source_property in &source_shape.properties {
            let Some(target_property) = target_shape
                .properties
                .iter()
                .find(|property| property.name == source_property.name)
            else {
                return false;
            };
            let Some(property_record) = self.type_payload(source_property.type_) else {
                return false;
            };
            let expected_type = if property_record.flags().intersects(TypeFlags::OBJECT) {
                if !property_record
                    .object_flags()
                    .contains(ObjectFlags::OBJECT_LITERAL)
                {
                    return false;
                }
                if property_record
                    .object_flags()
                    .intersects(ObjectFlags::REQUIRES_WIDENING)
                {
                    let Some(widened) = self
                        .derived_types
                        .widened_types
                        .get(&source_property.type_)
                        .copied()
                    else {
                        return false;
                    };
                    let mut widened_visiting = HashSet::new();
                    let mut nested_regular_visiting = HashSet::new();
                    if !self.widened_cache_entry_is_valid(
                        source_property.type_,
                        widened,
                        &mut widened_visiting,
                        &mut nested_regular_visiting,
                        array_targets,
                    ) {
                        return false;
                    }
                    widened
                } else {
                    source_property.type_
                }
            } else if property_record
                .object_flags()
                .intersects(ObjectFlags::REQUIRES_WIDENING)
            {
                let Some(bootstrap) = self.intrinsic_bootstrap() else {
                    return false;
                };
                bootstrap.any_type
            } else {
                source_property.type_
            };
            if target_property.name != source_property.name
                || target_property.type_ != expected_type
                || if expected_type == source_property.type_ {
                    target_property.symbol != source_property.symbol
                } else {
                    !self.valid_symbol_clone(
                        source_property.symbol,
                        target_property.symbol,
                        expected_type,
                    )
                }
            {
                return false;
            }
            expected_properties.push(target_property.symbol);
        }

        for donor in missing_properties {
            let Some(property) = target_shape
                .properties
                .iter()
                .find(|property| property.name == donor.name)
            else {
                return false;
            };
            if !self.validate_contextual_widened_object_property(target, property.symbol) {
                return false;
            }
            expected_properties.push(property.symbol);
        }
        self.sort_contextual_properties(&mut expected_properties)
            .is_some()
            && expected_properties.iter().copied().eq(target_shape
                .properties
                .iter()
                .map(|property| property.symbol))
    }

    fn widened_object_cache_entry_is_valid(
        &self,
        source: TypeId,
        target: TypeId,
        visiting: &mut HashSet<TypeId>,
        regular_visiting: &mut HashSet<TypeId>,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        let Some(source_record) = self.type_payload(source) else {
            return false;
        };
        if !source_record
            .object_flags()
            .contains(ObjectFlags::OBJECT_LITERAL)
            || !visiting.insert(source)
        {
            return false;
        }
        let valid = (|| {
            let source_shape = self.validated_widening_object_shape(source, regular_visiting)?;
            let target_shape = self.resolved_object_shape(target)?;
            let retained = source_shape.object_flags
                & (ObjectFlags::JS_LITERAL | ObjectFlags::NON_INFERRABLE_TYPE);
            if source == target
                || target_shape.flags != TypeFlags::OBJECT
                || target_shape.object_flags
                    != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED | retained
                || target_shape.symbol != source_shape.symbol
                || target_shape.members == source_shape.members
                || !self.widened_indexes_are_valid(
                    &source_shape,
                    &target_shape,
                    visiting,
                    regular_visiting,
                    array_targets,
                )
                || target_shape.properties.len() != source_shape.properties.len()
            {
                return None;
            }
            for (source_property, target_property) in
                source_shape.properties.iter().zip(&target_shape.properties)
            {
                let property_record = self.type_payload(source_property.type_)?;
                let expected_type = if property_record
                    .object_flags()
                    .intersects(ObjectFlags::REQUIRES_WIDENING)
                {
                    let cached = self
                        .derived_types
                        .widened_types
                        .get(&source_property.type_)
                        .copied()?;
                    if !self.widened_cache_entry_is_valid(
                        source_property.type_,
                        cached,
                        visiting,
                        regular_visiting,
                        array_targets,
                    ) {
                        return None;
                    }
                    cached
                } else {
                    source_property.type_
                };
                if target_property.name != source_property.name
                    || target_property.type_ != expected_type
                    || if expected_type == source_property.type_ {
                        target_property.symbol != source_property.symbol
                    } else {
                        !self.valid_symbol_clone(
                            source_property.symbol,
                            target_property.symbol,
                            expected_type,
                        )
                    }
                {
                    return None;
                }
            }
            Some(())
        })()
        .is_some();
        visiting.remove(&source);
        valid
    }

    fn widened_indexes_are_valid(
        &self,
        source: &ObjectShape,
        target: &ObjectShape,
        visiting: &mut HashSet<TypeId>,
        regular_visiting: &mut HashSet<TypeId>,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        let source_indexes = source.index_infos.as_deref().unwrap_or_default();
        let target_indexes = target.index_infos.as_deref().unwrap_or_default();
        if source_indexes.len() != target_indexes.len() {
            return false;
        }
        source_indexes
            .iter()
            .zip(target_indexes)
            .all(|(source, target)| {
                let (Some(source_info), Some(target_info)) =
                    (self.index_info(*source), self.index_info(*target))
                else {
                    return false;
                };
                if source == target
                    || source_info.key_type() != target_info.key_type()
                    || source_info.is_readonly() != target_info.is_readonly()
                    || source_info.declaration() != target_info.declaration()
                    || source_info.components() != target_info.components()
                    || target_info.index_symbol().is_some()
                {
                    return false;
                }
                let value = source_info.value_type();
                let Some(record) = self.type_payload(value) else {
                    return false;
                };
                if !record
                    .object_flags()
                    .intersects(ObjectFlags::REQUIRES_WIDENING)
                {
                    return target_info.value_type() == value;
                }
                self.derived_types
                    .widened_types
                    .get(&value)
                    .is_some_and(|expected| {
                        target_info.value_type() == *expected
                            && self.widened_cache_entry_is_valid(
                                value,
                                *expected,
                                visiting,
                                regular_visiting,
                                array_targets,
                            )
                    })
            })
    }

    fn valid_symbol_clone(
        &self,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
        expected_type: TypeId,
    ) -> bool {
        if source == target || self.get_merged_symbol(target) != Some(target) {
            return false;
        }
        let Some(source_record) = self.symbol(source) else {
            return false;
        };
        if self.object_literal_getter_origin(source).is_some()
            || source_record.flags().intersects(SymbolFlags::GET_ACCESSOR)
        {
            return false;
        }
        let Some(target_record) = self.symbol(target) else {
            return false;
        };
        let name_type = self
            .value_symbol_links(source)
            .and_then(|links| links.name_type);
        let expected_links = ValueSymbolLinks {
            resolved_type: Some(expected_type),
            target: Some(source),
            name_type,
            ..ValueSymbolLinks::default()
        };
        target_record.flags() == source_record.flags()
            && target_record.check_flags() == source_record.check_flags() & CheckFlags::READONLY
            && target_record.name() == source_record.name()
            && target_record.declarations() == source_record.declarations()
            && target_record.value_declaration() == source_record.value_declaration()
            && target_record.parent() == source_record.parent()
            && target_record.members().is_none()
            && target_record.exports().is_none()
            && target_record.export_symbol().is_none()
            && self.value_symbol_links(target) == Some(&expected_links)
    }
}

fn widening_union_error(source: TypeId, error: LiteralTypeCacheError) -> DerivedTypeError {
    match error {
        LiteralTypeCacheError::BootstrapUninitialized => DerivedTypeError::BootstrapUninitialized,
        LiteralTypeCacheError::Capacity => DerivedTypeError::Capacity(source),
        LiteralTypeCacheError::ArrayType { error, .. } => DerivedTypeError::ArrayType(error),
        LiteralTypeCacheError::UnsupportedUnionConstituent(type_) => {
            DerivedTypeError::UnsupportedWideningType(type_)
        }
        LiteralTypeCacheError::InvalidCachedLiteral(cached)
        | LiteralTypeCacheError::InvalidCachedUnion(cached) => {
            DerivedTypeError::InvalidWidenedTypeCache { source, cached }
        }
        LiteralTypeCacheError::InvalidValue
        | LiteralTypeCacheError::InvalidUnionAlias(_)
        | LiteralTypeCacheError::InvalidPreparedQuery => {
            DerivedTypeError::InvalidWidenedTypeCache {
                source,
                cached: source,
            }
        }
    }
}

fn valid_object_tail(object: &ObjectTypeData) -> bool {
    object.target.is_none()
        && object.mapper.is_none()
        && object.instantiations == TypeCacheState::Unallocated
}

fn valid_structured_tail(structured: &StructuredTypeData) -> bool {
    valid_structured_tail_with_indexes(structured) && structured.index_infos.is_none()
}

fn valid_structured_tail_with_indexes(structured: &StructuredTypeData) -> bool {
    structured.constrained == ConstrainedTypeData::default()
        && structured.signatures.is_none()
        && structured.call_signature_count == 0
        && structured
            .index_infos
            .as_ref()
            .is_none_or(|indexes| !indexes.is_empty())
        && structured
            .object_type_without_abstract_construct_signatures
            .is_none()
}

fn optional_nonempty_slice<T>(value: Option<&[T]>) -> Option<&[T]> {
    match value {
        None => Some(&[]),
        Some(value) if !value.is_empty() => Some(value),
        Some(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalProgramBindings, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, bootstrap::UnionReduction,
        mapper::CanonicalTypeMapperStore,
    };

    fn parsed(text: &str) -> ParseResult {
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn completed_bindings(files: &[(FileId, &ParseResult)]) -> CanonicalProgramBindings {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for &(file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        binder.finish()
    }

    fn checker_context<'arena>(
        files: &[(FileId, &'arena ParseResult)],
    ) -> CanonicalCheckerContext<'arena> {
        CanonicalCheckerContext::new(
            completed_bindings(files),
            files
                .iter()
                .map(|(file, parsed)| (*file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let initializer = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::VariableDeclaration(variable) = &node.data else {
                    return None;
                };
                let name = parsed.arena.get(variable.name)?;
                let NodeData::Identifier(identifier) = &name.data else {
                    return None;
                };
                (identifier.text == expected)
                    .then_some(variable.initializer)
                    .flatten()
            })
            .unwrap_or_else(|| panic!("missing initializer for variable {expected}"));
        NodeRef::new(parsed.arena.id(), file, initializer)
    }

    fn resolved_expression_type(
        context: &CanonicalCheckerContext<'_>,
        expression: NodeRef,
    ) -> TypeId {
        context
            .store()
            .type_node_links(expression)
            .and_then(|links| links.resolved_type)
            .expect("the expression was checked")
    }

    fn property<'a>(shape: &'a ObjectShape, name: &str) -> &'a PropertyShape {
        shape
            .properties
            .iter()
            .find(|property| property.name.as_utf8() == Some(name))
            .unwrap_or_else(|| panic!("missing property {name}"))
    }

    fn observable_state(store: &CanonicalTypeMapperStore) -> (usize, usize, usize, usize, usize) {
        (
            store.type_len(),
            store.symbol_len(),
            store.derived_types.regular_object_literals.len(),
            store.derived_types.widened_types.len(),
            store.derived_types.array_literal_types.len(),
        )
    }

    fn assert_widening_query_preserves_store(
        store: &mut CanonicalTypeMapperStore,
        source: TypeId,
        expected: Result<TypeId, DerivedTypeError>,
    ) {
        let before = format!("{store:?}");
        assert_eq!(store.get_widened_type(source), expected);
        assert!(
            format!("{store:?}") == before,
            "the widening query changed the store"
        );
    }

    #[test]
    fn object_method_clones_keep_their_callables_during_regularization_and_widening() {
        let source = parsed(concat!(
            "const object: any = { text: 'ready', missing: undefined, ",
            "identity(value: number): number { return value; }, ",
            "inferred(value: string) { return value; } };",
        ));
        let file = FileId::new(202);
        let mut context = checker_context(&[(file, &source)]);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let node = variable_initializer(&source, file, "object");
        let fresh = resolved_expression_type(&context, node);
        let store = context.store_mut_for_test();
        assert!(
            !store
                .derived_types
                .regular_object_literals
                .contains_key(&fresh)
        );
        let shape = store.fresh_object_shape(fresh).unwrap();
        let methods = ["identity", "inferred"].map(|name| property(&shape, name).clone());
        for method in &methods {
            let origin = store
                .object_literal_property_clone_origin(method.symbol)
                .unwrap();
            assert_eq!(origin.owner(), node);
            assert_eq!(origin.symbol(), method.symbol);
            assert_ne!(origin.source(), method.symbol);
            assert_eq!(
                store.source_callable_type_for_owner(origin.source()),
                Some(method.type_)
            );
            assert_eq!(
                store.object_literal_method_clone_type(method.symbol, shape.symbol),
                Some(method.type_)
            );
            assert_eq!(
                store.symbol(method.symbol).unwrap().flags(),
                SymbolFlags::METHOD | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            );
        }
        let symbols = store.symbol_len();
        let signatures = store.signature_len();
        let regular = store.get_regular_type_of_object_literal(fresh).unwrap();
        assert_ne!(regular, fresh);
        assert_eq!(store.symbol_len(), symbols);
        let widened = store.get_widened_type(regular).unwrap();
        assert_ne!(widened, regular);
        assert_eq!(store.symbol_len(), symbols + 1);
        assert_eq!(store.signature_len(), signatures);
        let widened_shape = store.resolved_object_shape(widened).unwrap();
        assert_eq!(
            property(&widened_shape, "text").type_,
            store.intrinsic_bootstrap().unwrap().string_type
        );
        assert_eq!(
            property(&widened_shape, "missing").type_,
            store.intrinsic_bootstrap().unwrap().any_type
        );
        assert_ne!(
            property(&widened_shape, "missing").symbol,
            property(&shape, "missing").symbol
        );
        for result in [regular, widened] {
            let result_shape = store.resolved_object_shape(result).unwrap();
            for method in &methods {
                let retained = property(&result_shape, method.name.as_utf8().unwrap());
                assert_eq!(retained.symbol, method.symbol);
                assert_eq!(retained.type_, method.type_);
            }
        }
        let warm = format!("{store:?}");
        for _ in 0..2 {
            assert_eq!(store.get_regular_type_of_object_literal(fresh), Ok(regular));
            assert_eq!(store.get_widened_type(regular), Ok(widened));
            assert_eq!(format!("{store:?}"), warm);
        }
    }

    #[test]
    fn object_method_clones_reject_source_and_callable_damage_before_cache_reuse() {
        let source = parsed(concat!(
            "const object: any = { method(value: number): number { return value; } }; ",
            "const donor: any = { method(value: number): number { return value; } };",
        ));
        let file = FileId::new(203);
        let mut context = checker_context(&[(file, &source)]);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let fresh =
            resolved_expression_type(&context, variable_initializer(&source, file, "object"));
        let donor =
            resolved_expression_type(&context, variable_initializer(&source, file, "donor"));
        let store = context.store_mut_for_test();
        let shape = store.fresh_object_shape(fresh).unwrap();
        let method = property(&shape, "method").clone();
        let donor_shape = store.fresh_object_shape(donor).unwrap();
        let donor_method = property(&donor_shape, "method");
        let donor_raw = store
            .value_symbol_links(donor_method.symbol)
            .unwrap()
            .target
            .unwrap();
        let original = store.value_symbol_links(method.symbol).unwrap().clone();
        let raw = original.target.unwrap();
        let raw_links = store.value_symbol_links(raw).unwrap().clone();
        let declaration = store.symbol(raw).unwrap().value_declaration().unwrap();
        let callable = store.source_callable_provenance(method.type_).unwrap();
        let returned = store
            .signature(callable.signature)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let mapper = store.new_simple_type_mapper(returned, string).unwrap();
        let reject = |store: &mut CanonicalTypeMapperStore| {
            let expected = store
                .derived_types
                .regular_object_literals
                .get(&fresh)
                .map_or(DerivedTypeError::MalformedObjectLiteral(fresh), |cached| {
                    DerivedTypeError::InvalidRegularObjectLiteralCache {
                        source: fresh,
                        cached: *cached,
                    }
                });
            let before = format!("{store:?}");
            for _ in 0..2 {
                assert!(store.fresh_object_shape(fresh).is_none());
                assert_eq!(
                    store.object_literal_method_clone_type(method.symbol, shape.symbol),
                    None
                );
                assert_eq!(
                    store.get_regular_type_of_object_literal(fresh),
                    Err(expected)
                );
                assert_eq!(format!("{store:?}"), before);
            }
        };
        assert!(
            !store
                .derived_types
                .regular_object_literals
                .contains_key(&fresh)
        );
        assert!(store.set_value_symbol_links(
            method.symbol,
            ValueSymbolLinks {
                resolved_type: Some(donor_method.type_),
                ..original.clone()
            }
        ));
        reject(store);
        assert!(store.set_value_symbol_links(method.symbol, original.clone()));
        let regular = store.get_regular_type_of_object_literal(fresh).unwrap();

        for symbol in [method.symbol, raw] {
            assert!(store.set_symbol_relationships(
                symbol,
                None,
                None,
                Some(donor_shape.symbol),
                None
            ));
            reject(store);
            assert!(store.set_symbol_relationships(symbol, None, None, Some(shape.symbol), None));
            assert_eq!(store.get_regular_type_of_object_literal(fresh), Ok(regular));
            assert!(store.set_symbol_declarations(symbol, Some(vec![declaration]), None));
            reject(store);
            assert!(store.set_symbol_declarations(
                symbol,
                Some(vec![declaration]),
                Some(declaration)
            ));
            assert_eq!(store.get_regular_type_of_object_literal(fresh), Ok(regular));
        }
        for links in [
            ValueSymbolLinks {
                target: Some(donor_raw),
                ..original.clone()
            },
            ValueSymbolLinks {
                mapper: Some(mapper),
                ..original.clone()
            },
        ] {
            assert!(store.set_value_symbol_links(method.symbol, links));
            reject(store);
            assert!(store.set_value_symbol_links(method.symbol, original.clone()));
            assert_eq!(store.get_regular_type_of_object_literal(fresh), Ok(regular));
        }
        assert!(store.set_value_symbol_links(raw, ValueSymbolLinks::default()));
        reject(store);
        assert!(store.set_symbol_flags(
            method.symbol,
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            CheckFlags::NONE
        ));
        assert!(store.set_symbol_flags(raw, SymbolFlags::PROPERTY, CheckFlags::NONE));
        reject(store);
        assert!(store.set_symbol_flags(raw, SymbolFlags::METHOD, CheckFlags::NONE));
        assert!(store.set_symbol_flags(
            method.symbol,
            SymbolFlags::METHOD | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            CheckFlags::NONE
        ));
        assert!(store.set_value_symbol_links(raw, raw_links));
        assert_eq!(store.get_regular_type_of_object_literal(fresh), Ok(regular));
        assert!(store.set_signature_resolved_return_type(callable.signature, Some(string)));
        reject(store);
        assert!(store.set_signature_resolved_return_type(callable.signature, Some(returned)));
        assert_eq!(store.get_regular_type_of_object_literal(fresh), Ok(regular));

        let mut forged = SymbolData::new(
            SymbolFlags::METHOD | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            method.name.clone(),
        );
        forged.declarations = Some(vec![declaration]);
        forged.value_declaration = Some(declaration);
        forged.parent = Some(shape.symbol);
        let forged = store.alloc_symbol(forged).unwrap();
        assert!(store.set_value_symbol_links(forged, original));
        assert!(store.object_literal_property_clone_origin(forged).is_none());
        assert_eq!(
            store.insert_symbol(shape.members, method.name.clone(), forged),
            Some(Some(method.symbol))
        );
        assert!(store.set_structured_type_members(
            fresh,
            Some(shape.members),
            Some(vec![forged]),
            None,
            None,
            None
        ));
        let before = format!("{store:?}");
        assert!(store.fresh_object_shape(fresh).is_none());
        assert_eq!(
            store.object_literal_method_clone_type(forged, shape.symbol),
            None
        );
        assert_eq!(
            store.get_regular_type_of_object_literal(fresh),
            Err(DerivedTypeError::InvalidRegularObjectLiteralCache {
                source: fresh,
                cached: regular
            })
        );
        assert_eq!(format!("{store:?}"), before);
        assert_eq!(
            store.insert_symbol(shape.members, method.name.clone(), method.symbol),
            Some(Some(forged))
        );
        assert!(store.set_structured_type_members(
            fresh,
            Some(shape.members),
            Some(vec![method.symbol]),
            None,
            None,
            None
        ));
        assert_eq!(store.get_regular_type_of_object_literal(fresh), Ok(regular));
    }

    #[test]
    fn cached_widened_type_display_proof_keeps_exact_pairs_and_rejects_damage() {
        let library = parsed("interface Array<T> {}");
        let source = parsed(concat!(
            "const object: any = { value: 1 }; ",
            "const array: any = [{ value: 1 }]; ",
            "const union: any = [{ value: 1 }, { value: 'x' }]; ",
            "const donor: any = { value: 2 };",
        ));
        let library_file = FileId::new(200);
        let file = FileId::new(201);
        let mut context = checker_context(&[(library_file, &library), (file, &source)]);
        context.check_source_file(file).unwrap();
        let global_types = context.global_types().clone();
        let types = ["object", "array", "union", "donor"].map(|name| {
            resolved_expression_type(&context, variable_initializer(&source, file, name))
        });
        let union = context
            .store()
            .canonical_array_element_type(&global_types, types[2])
            .unwrap()
            .unwrap();
        assert!(matches!(
            context.store().type_payload(union).unwrap().data(),
            TypeData::Union(_)
        ));
        let donor = context
            .store_mut_for_test()
            .get_widened_type_with_global_types(types[3], &global_types)
            .unwrap();
        for source_type in [types[0], types[1], union] {
            let target = context
                .store_mut_for_test()
                .get_widened_type_with_global_types(source_type, &global_types)
                .unwrap();
            assert_ne!(target, source_type);
            assert_ne!(target, donor);
            let before = format!("{:?}", context.store());
            for _ in 0..2 {
                assert!(context.store().validate_cached_widened_type(
                    source_type,
                    target,
                    Some(&global_types),
                ));
                assert!(!context.store().validate_cached_widened_type(
                    source_type,
                    donor,
                    Some(&global_types),
                ));
                assert_eq!(format!("{:?}", context.store()), before);
            }
            assert_eq!(
                context
                    .store_mut_for_test()
                    .derived_types
                    .widened_types
                    .insert(source_type, donor),
                Some(target),
            );
            let damaged = format!("{:?}", context.store());
            for candidate in [target, donor] {
                assert!(!context.store().validate_cached_widened_type(
                    source_type,
                    candidate,
                    Some(&global_types),
                ));
                assert_eq!(format!("{:?}", context.store()), damaged);
            }
            assert_eq!(
                context
                    .store_mut_for_test()
                    .derived_types
                    .widened_types
                    .insert(source_type, target),
                Some(donor),
            );
            assert_eq!(format!("{:?}", context.store()), before);
            assert!(context.store().validate_cached_widened_type(
                source_type,
                target,
                Some(&global_types),
            ));
            assert_eq!(format!("{:?}", context.store()), before);
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn regular_and_widened_object_literals_are_dependency_closed_and_stable() {
        let source = parsed(concat!(
            r#"const value: any = { text: "ok", "#,
            "nested: { missing: undefined } };",
        ));
        let file = FileId::new(1);
        let mut context = checker_context(&[(file, &source)]);
        let initializer = variable_initializer(&source, file, "value");
        context.check_source_file(file).unwrap();

        let fresh = resolved_expression_type(&context, initializer);
        let fresh_shape = context.store().fresh_object_shape(fresh).unwrap();
        let fresh_nested = property(&fresh_shape, "nested").clone();
        let fresh_text = property(&fresh_shape, "text").clone();
        let before_regular = observable_state(context.store());

        let regular = context
            .store_mut_for_test()
            .get_regular_type_of_object_literal(fresh)
            .unwrap();
        assert_ne!(regular, fresh);
        assert_eq!(context.store().type_len(), before_regular.0 + 2);
        assert_eq!(context.store().symbol_len(), before_regular.1 + 1);
        assert_eq!(
            context.store().derived_types.regular_object_literals.len(),
            before_regular.2 + 2
        );

        let regular_shape = context.store().resolved_object_shape(regular).unwrap();
        assert_eq!(
            regular_shape.object_flags,
            fresh_shape.object_flags & !ObjectFlags::FRESH_LITERAL
        );
        let regular_nested = property(&regular_shape, "nested").clone();
        let regular_text = property(&regular_shape, "text").clone();
        assert_ne!(regular_nested.symbol, fresh_nested.symbol);
        assert_ne!(regular_nested.type_, fresh_nested.type_);
        assert_eq!(
            context
                .store()
                .value_symbol_links(regular_nested.symbol)
                .and_then(|links| links.target),
            Some(fresh_nested.symbol)
        );
        assert_eq!(regular_text.symbol, fresh_text.symbol);

        let warm_regular_state = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_regular_type_of_object_literal(fresh)
                .unwrap(),
            regular
        );
        assert_eq!(observable_state(context.store()), warm_regular_state);

        let before_widened = observable_state(context.store());
        let widened = context
            .store_mut_for_test()
            .get_widened_type(regular)
            .unwrap();
        assert_ne!(widened, regular);
        assert_eq!(context.store().type_len(), before_widened.0 + 2);
        assert_eq!(context.store().symbol_len(), before_widened.1 + 2);
        assert_eq!(
            context.store().derived_types.widened_types.len(),
            before_widened.3 + 3
        );

        let widened_shape = context.store().resolved_object_shape(widened).unwrap();
        assert_eq!(
            widened_shape.object_flags,
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        let widened_nested = property(&widened_shape, "nested").clone();
        let widened_text = property(&widened_shape, "text").clone();
        assert_ne!(widened_nested.symbol, regular_nested.symbol);
        assert_eq!(
            context
                .store()
                .value_symbol_links(widened_nested.symbol)
                .and_then(|links| links.target),
            Some(regular_nested.symbol)
        );
        assert_eq!(widened_text.symbol, regular_text.symbol);

        let widened_nested_shape = context
            .store()
            .resolved_object_shape(widened_nested.type_)
            .unwrap();
        let widened_missing = property(&widened_nested_shape, "missing");
        let regular_nested_shape = context
            .store()
            .resolved_object_shape(regular_nested.type_)
            .unwrap();
        let regular_missing = property(&regular_nested_shape, "missing");
        assert_ne!(widened_missing.symbol, regular_missing.symbol);
        assert_eq!(
            widened_missing.type_,
            context.store().intrinsic_bootstrap().unwrap().any_type
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(widened_missing.symbol)
                .and_then(|links| links.target),
            Some(regular_missing.symbol)
        );

        let warm_widened_state = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type(regular)
                .unwrap(),
            widened
        );
        assert_eq!(observable_state(context.store()), warm_widened_state);
    }

    #[test]
    fn readonly_const_objects_retain_literal_properties_and_reject_mixed_flags() {
        let source = parsed(concat!(
            "const ordinary = { value: 1 }; ",
            "const frozen = ({ value: 1, label: 'ready' }) as const;",
        ));
        let file = FileId::new(43);
        let mut context = checker_context(&[(file, &source)]);

        context.check_source_file(file).unwrap();

        let ordinary =
            resolved_expression_type(&context, variable_initializer(&source, file, "ordinary"));
        let frozen =
            resolved_expression_type(&context, variable_initializer(&source, file, "frozen"));
        let ordinary_shape = context.store().fresh_object_shape(ordinary).unwrap();
        let frozen_shape = context.store().fresh_object_shape(frozen).unwrap();
        assert_eq!(
            context
                .store()
                .symbol(property(&ordinary_shape, "value").symbol)
                .unwrap()
                .check_flags(),
            CheckFlags::NONE,
        );
        for property in &frozen_shape.properties {
            assert_eq!(
                context
                    .store()
                    .symbol(property.symbol)
                    .unwrap()
                    .check_flags(),
                CheckFlags::READONLY,
            );
            assert!(matches!(
                context.store().type_payload(property.type_).unwrap().data(),
                TypeData::Literal(literal) if literal.regular_type == property.type_
            ));
        }

        let regular = context
            .store_mut_for_test()
            .get_regular_type_of_object_literal(frozen)
            .unwrap();
        let regular_shape = context.store().resolved_object_shape(regular).unwrap();
        for (fresh, regular) in frozen_shape
            .properties
            .iter()
            .zip(&regular_shape.properties)
        {
            assert_eq!(regular.symbol, fresh.symbol);
            assert_eq!(regular.type_, fresh.type_);
        }

        let warm = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_regular_type_of_object_literal(frozen),
            Ok(regular),
        );
        assert_eq!(observable_state(context.store()), warm);

        let property = frozen_shape.properties[0].symbol;
        let flags = context.store().symbol(property).unwrap().flags();
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_flags(property, flags, CheckFlags::NONE,)
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .get_regular_type_of_object_literal(frozen),
            Err(DerivedTypeError::InvalidRegularObjectLiteralCache {
                source: frozen,
                cached: regular,
            }),
        );
        assert!(context.store_mut_for_test().set_symbol_flags(
            property,
            flags,
            CheckFlags::READONLY,
        ));
        assert_eq!(
            context
                .store_mut_for_test()
                .get_regular_type_of_object_literal(frozen),
            Ok(regular),
        );
    }

    #[test]
    fn foreign_and_poisoned_dependency_entries_fail_atomically_then_retry() {
        let source = parsed("const value: any = { nested: { missing: undefined } };");
        let file = FileId::new(2);
        let mut context = checker_context(&[(file, &source)]);
        let initializer = variable_initializer(&source, file, "value");
        context.check_source_file(file).unwrap();
        let fresh = resolved_expression_type(&context, initializer);
        let fresh_shape = context.store().fresh_object_shape(fresh).unwrap();
        let fresh_nested = property(&fresh_shape, "nested").type_;

        let foreign_source = parsed("const foreign: any = {};");
        let foreign_file = FileId::new(3);
        let foreign_context = checker_context(&[(foreign_file, &foreign_source)]);
        let foreign = foreign_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .any_type;

        let before_foreign = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_regular_type_of_object_literal(foreign),
            Err(DerivedTypeError::Type(foreign))
        );
        assert_eq!(
            context.store_mut_for_test().get_widened_type(foreign),
            Err(DerivedTypeError::Type(foreign))
        );
        assert_eq!(observable_state(context.store()), before_foreign);

        let regular_nested = context
            .store_mut_for_test()
            .get_regular_type_of_object_literal(fresh_nested)
            .unwrap();
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .regular_object_literals
                .insert(fresh_nested, foreign),
            Some(regular_nested)
        );
        let poisoned_regular_state = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_regular_type_of_object_literal(fresh),
            Err(DerivedTypeError::InvalidRegularObjectLiteralCache {
                source: fresh_nested,
                cached: foreign,
            })
        );
        assert_eq!(observable_state(context.store()), poisoned_regular_state);
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .regular_object_literals
                .insert(fresh_nested, regular_nested),
            Some(foreign)
        );

        let regular = context
            .store_mut_for_test()
            .get_regular_type_of_object_literal(fresh)
            .unwrap();
        assert_eq!(
            context
                .store()
                .derived_types
                .regular_object_literals
                .get(&fresh_nested),
            Some(&regular_nested)
        );

        let widened_nested = context
            .store_mut_for_test()
            .get_widened_type(regular_nested)
            .unwrap();
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(regular_nested, foreign),
            Some(widened_nested)
        );
        let poisoned_widened_state = observable_state(context.store());
        assert_eq!(
            context.store_mut_for_test().get_widened_type(regular),
            Err(DerivedTypeError::InvalidWidenedTypeCache {
                source: regular_nested,
                cached: foreign,
            })
        );
        assert_eq!(observable_state(context.store()), poisoned_widened_state);
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(regular_nested, widened_nested),
            Some(foreign)
        );

        let widened = context
            .store_mut_for_test()
            .get_widened_type(regular)
            .unwrap();
        let widened_shape = context.store().resolved_object_shape(widened).unwrap();
        assert_eq!(
            property(&widened_shape, "nested").type_,
            widened_nested,
            "the successful retry must retain the already-published child identity"
        );
    }

    #[test]
    fn logical_array_unions_widen_each_member_and_reuse_the_canonical_result() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("var value: any = [1, 2];");
        let library_file = FileId::new(40);
        let file = FileId::new(41);
        let files = [(library_file, &library), (file, &source)];
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&files),
            files
                .iter()
                .map(|(file, parsed)| (*file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: crate::semantic::IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..crate::semantic::IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let initializer = variable_initializer(&source, file, "value");
        context.check_source_file(file).unwrap();

        let array_literal = resolved_expression_type(&context, initializer);
        let global_types = context.global_types().clone();
        let zero = context.store().intrinsic_bootstrap().unwrap().zero_type;
        let union = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(
                &global_types,
                &[zero, array_literal],
                UnionReduction::Literal,
            )
            .unwrap();
        assert!(
            context
                .store()
                .type_payload(union)
                .unwrap()
                .object_flags()
                .intersects(ObjectFlags::REQUIRES_WIDENING)
        );
        let widened = context
            .store_mut_for_test()
            .get_widened_type_with_global_types(union, &global_types)
            .unwrap();
        let Some(TypeData::Union(result)) =
            context.store().type_payload(widened).map(TypeRecord::data)
        else {
            panic!("the widened logical result must remain a union");
        };
        assert_eq!(result.union.types.len(), 2);
        assert!(result.union.types.contains(&zero));
        let array = result
            .union
            .types
            .iter()
            .copied()
            .find(|type_| *type_ != zero)
            .unwrap();
        let reference = context
            .store()
            .canonical_array_reference(&global_types, array)
            .unwrap()
            .unwrap();
        assert!(!reference.array_literal);
        assert_eq!(
            reference.element_type,
            context.store().intrinsic_bootstrap().unwrap().number_type,
        );

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(union, number),
            Some(widened),
        );
        let poisoned = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(union, &global_types),
            Err(DerivedTypeError::InvalidWidenedTypeCache {
                source: union,
                cached: number,
            }),
        );
        assert_eq!(observable_state(context.store()), poisoned);
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(union, widened),
            Some(number),
        );

        let warm = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(union, &global_types),
            Ok(widened),
        );
        assert_eq!(observable_state(context.store()), warm);
    }

    #[test]
    fn contextual_scalar_unions_keep_regular_identities_cold_and_warm() {
        let source = parsed("const first: any = { now: 1 }; const second: any = { later: 2 };");
        let file = FileId::new(202_360);
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(&[(file, &source)]),
            vec![(file, &source.arena)],
            CanonicalCheckerOptions {
                intrinsic: crate::semantic::IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..crate::semantic::IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let first =
            resolved_expression_type(&context, variable_initializer(&source, file, "first"));
        let second =
            resolved_expression_type(&context, variable_initializer(&source, file, "second"));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let undefined = bootstrap.undefined_or_missing_type;
        let scalar_rows = [
            vec![bootstrap.zero_type, bootstrap.regular_false_type],
            vec![bootstrap.empty_string_type, bootstrap.zero_bigint_type],
            vec![bootstrap.string_type],
            vec![bootstrap.number_type],
            vec![bootstrap.bigint_type],
            vec![bootstrap.es_symbol_type],
        ];

        for scalars in scalar_rows {
            let members = scalars
                .iter()
                .copied()
                .chain([first, second])
                .collect::<Vec<_>>();
            let union = context
                .store_mut_for_test()
                .expression_union_type(&members, UnionReduction::None)
                .unwrap();
            let TypeData::Union(source_union) = context.store().type_payload(union).unwrap().data()
            else {
                panic!("the source must retain scalar and object members");
            };
            assert_eq!(source_union.union.types.len(), members.len());
            assert!(
                members
                    .iter()
                    .all(|member| source_union.union.types.contains(member))
            );
            assert!(
                !context
                    .store()
                    .derived_types
                    .widened_types
                    .contains_key(&union)
            );

            let widened = context
                .store_mut_for_test()
                .get_widened_type(union)
                .unwrap();
            let TypeData::Union(result) = context.store().type_payload(widened).unwrap().data()
            else {
                panic!("widening must retain scalar and object members");
            };
            assert_eq!(result.union.types.len(), members.len());
            for scalar in &scalars {
                assert!(result.union.types.contains(scalar));
                assert!(
                    !context
                        .store()
                        .derived_types
                        .widened_types
                        .contains_key(scalar)
                );
                assert!(
                    !context
                        .store()
                        .derived_types
                        .contextual_widened_types
                        .contains_key(&(union, *scalar))
                );
            }
            for (object, own_name, optional_name) in
                [(first, "now", "later"), (second, "later", "now")]
            {
                let fresh_shape = context.store().fresh_object_shape(object).unwrap();
                let target =
                    context.store().derived_types.contextual_widened_types[&(union, object)];
                assert_ne!(target, object);
                assert!(result.union.types.contains(&target));
                let shape = context.store().resolved_object_shape(target).unwrap();
                assert_eq!(shape.properties.len(), 2);
                assert_eq!(shape.symbol, fresh_shape.symbol);
                assert_eq!(
                    shape.object_flags,
                    ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
                );
                assert_eq!(
                    property(&shape, own_name).symbol,
                    property(&fresh_shape, own_name).symbol
                );
                assert_eq!(
                    property(&shape, own_name).type_,
                    property(&fresh_shape, own_name).type_
                );
                let optional = property(&shape, optional_name);
                assert_eq!(optional.type_, undefined);
                assert!(
                    context
                        .store()
                        .validate_contextual_widened_object_property(target, optional.symbol)
                );
            }
            for _ in 0..3 {
                assert_widening_query_preserves_store(
                    context.store_mut_for_test(),
                    union,
                    Ok(widened),
                );
            }
        }
    }

    #[test]
    fn contextual_scalar_unions_reject_poisoned_cold_and_warm_caches() {
        let source = parsed("const value: any = { now: 1 };");
        let file = FileId::new(202_361);
        let mut context = checker_context(&[(file, &source)]);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let object =
            resolved_expression_type(&context, variable_initializer(&source, file, "value"));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let zero = bootstrap.zero_type;
        let regular_false = bootstrap.regular_false_type;
        let fresh_false = bootstrap.false_type;
        let number = bootstrap.number_type;
        let union = context
            .store_mut_for_test()
            .expression_union_type(&[zero, regular_false, object], UnionReduction::None)
            .unwrap();
        assert!(
            !context
                .store()
                .derived_types
                .widened_types
                .contains_key(&union)
        );
        assert!(
            !context
                .store()
                .derived_types
                .contextual_widened_types
                .contains_key(&(union, object))
        );

        assert!(
            context
                .store_mut_for_test()
                .set_literal_links(regular_false, None, regular_false)
        );
        assert_widening_query_preserves_store(
            context.store_mut_for_test(),
            union,
            Err(DerivedTypeError::InvalidWidenedTypeCache {
                source: union,
                cached: regular_false,
            }),
        );
        assert!(context.store_mut_for_test().set_literal_links(
            regular_false,
            Some(fresh_false),
            regular_false
        ));
        let widened = context
            .store_mut_for_test()
            .get_widened_type(union)
            .unwrap();
        let widened_object =
            context.store().derived_types.contextual_widened_types[&(union, object)];
        let invalid_warm = Err(DerivedTypeError::InvalidWidenedTypeCache {
            source: union,
            cached: widened,
        });

        assert!(
            context
                .store_mut_for_test()
                .set_literal_links(regular_false, None, regular_false)
        );
        assert_widening_query_preserves_store(context.store_mut_for_test(), union, invalid_warm);
        assert!(context.store_mut_for_test().set_literal_links(
            regular_false,
            Some(fresh_false),
            regular_false
        ));
        assert_widening_query_preserves_store(context.store_mut_for_test(), union, Ok(widened));

        let flags = context.store().type_payload(union).unwrap().object_flags();
        assert!(!flags.intersects(ObjectFlags::CONTAINS_WIDENING_TYPE));
        assert!(
            context
                .store_mut_for_test()
                .set_type_object_flags(union, flags | ObjectFlags::CONTAINS_WIDENING_TYPE)
        );
        assert_widening_query_preserves_store(context.store_mut_for_test(), union, invalid_warm);
        assert!(
            context
                .store_mut_for_test()
                .set_type_object_flags(union, flags)
        );
        assert_widening_query_preserves_store(context.store_mut_for_test(), union, Ok(widened));

        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .contextual_widened_types
                .insert((union, object), object),
            Some(widened_object)
        );
        assert_widening_query_preserves_store(context.store_mut_for_test(), union, invalid_warm);
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .contextual_widened_types
                .insert((union, object), widened_object),
            Some(object)
        );
        assert_widening_query_preserves_store(context.store_mut_for_test(), union, Ok(widened));

        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(union, number),
            Some(widened)
        );
        assert_widening_query_preserves_store(
            context.store_mut_for_test(),
            union,
            Err(DerivedTypeError::InvalidWidenedTypeCache {
                source: union,
                cached: number,
            }),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(union, widened),
            Some(number)
        );
        for _ in 0..3 {
            assert_widening_query_preserves_store(context.store_mut_for_test(), union, Ok(widened));
        }
    }

    #[test]
    fn contextual_scalar_unions_keep_fresh_literals_outside_the_scalar_guard() {
        let source = parsed("const value: any = { now: 1 };");
        let file = FileId::new(202_362);
        let mut context = checker_context(&[(file, &source)]);
        context.check_source_file(file).unwrap();
        let object =
            resolved_expression_type(&context, variable_initializer(&source, file, "value"));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let regular = bootstrap.regular_false_type;
        let fresh = bootstrap.false_type;
        let record = context.store().type_payload(fresh).unwrap();
        assert_eq!(record.object_flags(), ObjectFlags::NONE);
        assert!(
            matches!(record.data(), TypeData::Literal(literal) if literal.regular_type == regular && regular != fresh)
        );
        assert_eq!(context.store().validate_union_constituent(fresh), Ok(()));
        let union = context
            .store_mut_for_test()
            .expression_union_type(&[fresh, object], UnionReduction::None)
            .unwrap();
        let TypeData::Union(members) = context.store().type_payload(union).unwrap().data() else {
            panic!("the fresh literal must remain a union sibling");
        };
        assert!(members.union.types.contains(&fresh));
        for _ in 0..2 {
            assert_widening_query_preserves_store(
                context.store_mut_for_test(),
                union,
                Err(DerivedTypeError::UnsupportedWideningType(fresh)),
            );
        }
    }

    fn assert_contextual_property_order(
        store: &CanonicalTypeMapperStore,
        union: TypeId,
        source: TypeId,
        names: &[&str],
    ) -> (TypeId, ObjectShape) {
        let target = store.derived_types.contextual_widened_types[&(union, source)];
        assert!(store.contextual_object_cache_entry_is_valid(union, source, target, None));
        let source_shape = store
            .validated_widening_object_shape(source, &mut HashSet::new())
            .unwrap();
        let shape = store.resolved_object_shape(target).unwrap();
        assert_eq!(shape.symbol, source_shape.symbol);
        assert_eq!(
            shape
                .properties
                .iter()
                .map(|property| property.name.as_utf8().unwrap())
                .collect::<Vec<_>>(),
            names,
        );
        let table = store.symbol_table(shape.members).unwrap();
        assert_eq!(table.len(), names.len());
        for source_property in &source_shape.properties {
            let own = property(&shape, source_property.name.as_utf8().unwrap());
            assert_eq!(own.symbol, source_property.symbol);
            assert_eq!(own.type_, source_property.type_);
        }
        for property in &shape.properties {
            assert_eq!(table.get(property.name.as_ref()), Some(property.symbol));
            if store
                .symbol(property.symbol)
                .unwrap()
                .flags()
                .contains(SymbolFlags::OPTIONAL)
            {
                assert_eq!(
                    property.type_,
                    store
                        .intrinsic_bootstrap()
                        .unwrap()
                        .undefined_or_missing_type
                );
                assert!(store.validate_contextual_widened_object_property(target, property.symbol));
            }
        }
        (target, shape)
    }

    fn assert_contextual_order_rejection(
        store: &mut CanonicalTypeMapperStore,
        union: TypeId,
        members: [TypeId; 2],
        invalid: TypeId,
        widened: Option<TypeId>,
    ) {
        let error = if let Some(cached) = widened {
            assert_eq!(store.derived_types.widened_types.get(&union), Some(&cached));
            DerivedTypeError::InvalidWidenedTypeCache {
                source: union,
                cached,
            }
        } else {
            assert!(!store.derived_types.widened_types.contains_key(&union));
            for source in members {
                assert!(
                    !store
                        .derived_types
                        .contextual_widened_types
                        .contains_key(&(union, source))
                );
            }
            DerivedTypeError::MalformedObjectLiteral(invalid)
        };
        for _ in 0..2 {
            assert_widening_query_preserves_store(store, union, Err(error));
        }
    }

    fn assert_coherent_contextual_donor_rejection(
        store: &mut CanonicalTypeMapperStore,
        cached: SemanticSymbolId,
        union: TypeId,
        original: TypeId,
        replacement: TypeId,
        receiver: TypeId,
        widened: Option<TypeId>,
    ) {
        let original_shape = store.fresh_object_shape(original).unwrap();
        let replacement_shape = store.fresh_object_shape(replacement).unwrap();
        let donor = property(&original_shape, "zeta");
        let foreign = property(&replacement_shape, "zeta");
        assert_eq!(donor.type_, foreign.type_);
        assert_ne!(original_shape.symbol, replacement_shape.symbol);
        let raw = store
            .value_symbol_links(donor.symbol)
            .unwrap()
            .target
            .unwrap();
        let foreign_raw = store
            .value_symbol_links(foreign.symbol)
            .unwrap()
            .target
            .unwrap();
        let declaration = store.symbol(raw).unwrap().value_declaration().unwrap();
        let foreign_declaration = store
            .symbol(foreign_raw)
            .unwrap()
            .value_declaration()
            .unwrap();
        assert_eq!(store.source_declaration_symbol(declaration), Some(raw));
        assert_eq!(
            store.source_declaration_symbol(foreign_declaration),
            Some(foreign_raw)
        );
        let originals = [raw, donor.symbol, cached].map(|symbol| {
            let record = store.symbol(symbol).unwrap();
            (
                symbol,
                record.declarations().unwrap().to_vec(),
                record.value_declaration(),
            )
        });
        for (symbol, _, _) in &originals {
            assert!(store.set_symbol_declarations(
                *symbol,
                Some(vec![foreign_declaration]),
                Some(foreign_declaration),
            ));
        }
        assert!(store.valid_cached_undefined_property(&EscapedName::source("zeta"), cached));
        assert!(store.contextual_property_order_key(cached).is_none());
        assert_contextual_order_rejection(store, union, [replacement, receiver], receiver, widened);
        for (symbol, declarations, value_declaration) in originals {
            assert!(store.set_symbol_declarations(symbol, Some(declarations), value_declaration));
        }
        assert!(store.contextual_property_order_key(cached).is_some());

        for symbol in [foreign_raw, foreign.symbol] {
            let record = store.symbol(symbol).unwrap();
            assert_eq!(
                record.declarations(),
                Some([foreign_declaration].as_slice())
            );
            assert_eq!(record.value_declaration(), Some(foreign_declaration));
            assert!(store.set_symbol_declarations(
                symbol,
                Some(vec![declaration]),
                Some(declaration),
            ));
        }
        assert!(store.fresh_object_shape(replacement).is_some());
        assert!(
            store
                .contextual_property_order_key(foreign.symbol)
                .is_none()
        );
        assert!(store.contextual_property_order_key(cached).is_some());
        assert_contextual_order_rejection(
            store,
            union,
            [replacement, receiver],
            replacement,
            widened,
        );
        for symbol in [foreign_raw, foreign.symbol] {
            assert!(store.set_symbol_declarations(
                symbol,
                Some(vec![foreign_declaration]),
                Some(foreign_declaration),
            ));
        }
        assert!(
            store
                .contextual_property_order_key(foreign.symbol)
                .is_some()
        );
    }

    #[test]
    fn contextual_object_order_keeps_source_members_and_rejects_warm_vector_swaps() {
        let source = parsed(concat!(
            "declare const log: string; declare const highlighted: boolean; ",
            "const first: any = { log, highlighted }; const second: any = { log };",
        ));
        let file = FileId::new(202_380);
        let mut context = checker_context(&[(file, &source)]);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let [first, second] = ["first", "second"].map(|name| {
            resolved_expression_type(&context, variable_initializer(&source, file, name))
        });
        let store = context.store_mut_for_test();
        let union = store
            .expression_union_type(&[first, second], UnionReduction::None)
            .unwrap();
        assert!(!store.derived_types.widened_types.contains_key(&union));
        let widened = store.get_widened_type(union).unwrap();
        let (first_target, _) =
            assert_contextual_property_order(store, union, first, &["log", "highlighted"]);
        let (second_target, shape) =
            assert_contextual_property_order(store, union, second, &["highlighted", "log"]);
        assert_eq!(
            crate::semantic::formatter::type_to_string(store, first_target).unwrap(),
            "{ log: string; highlighted: boolean; }",
        );
        assert_eq!(
            crate::semantic::formatter::type_to_string(store, second_target).unwrap(),
            "{ highlighted?: undefined; log: string; }",
        );
        let properties = shape
            .properties
            .iter()
            .map(|property| property.symbol)
            .collect::<Vec<_>>();
        let mut swapped = properties.clone();
        swapped.swap(0, 1);
        for _ in 0..2 {
            assert_widening_query_preserves_store(store, union, Ok(widened));
            assert!(store.set_structured_type_members(
                second_target,
                Some(shape.members),
                Some(swapped.clone()),
                None,
                None,
                None,
            ));
            let table = store.symbol_table(shape.members).unwrap();
            assert_eq!(table.len(), 2);
            for property in &shape.properties {
                assert_eq!(table.get(property.name.as_ref()), Some(property.symbol));
            }
            assert!(store.resolved_object_shape(second_target).is_some());
            assert_widening_query_preserves_store(
                store,
                union,
                Err(DerivedTypeError::InvalidWidenedTypeCache {
                    source: union,
                    cached: widened,
                }),
            );
            assert!(store.set_structured_type_members(
                second_target,
                Some(shape.members),
                Some(properties.clone()),
                None,
                None,
                None,
            ));
            assert_widening_query_preserves_store(store, union, Ok(widened));
            assert_eq!(
                assert_contextual_property_order(store, union, second, &["highlighted", "log"]).0,
                second_target,
            );
        }
    }

    #[test]
    fn contextual_object_order_uses_cached_donors_and_program_file_rank() {
        let earlier = parsed("const original: any = { zeta: 1 };");
        let later = parsed(concat!(
            "const seed: any = { seed: 2 }; ",
            "const receiver: any = { beta: 3 }; const replacement: any = { zeta: 4 };",
        ));
        let earlier_file = FileId::new(202_382);
        let later_file = FileId::new(202_381);
        let mut context = checker_context(&[(earlier_file, &earlier), (later_file, &later)]);
        for file in [later_file, earlier_file] {
            context.check_source_file(file).unwrap();
        }
        assert!(context.diagnostics().is_empty());
        let original = resolved_expression_type(
            &context,
            variable_initializer(&earlier, earlier_file, "original"),
        );
        let [seed, receiver, replacement] = ["seed", "receiver", "replacement"].map(|name| {
            resolved_expression_type(&context, variable_initializer(&later, later_file, name))
        });
        let store = context.store_mut_for_test();
        assert_eq!(store.source_file_rank(earlier_file), Some(0));
        assert_eq!(store.source_file_rank(later_file), Some(1));
        assert!(earlier_file.index() > later_file.index());
        let original_shape = store.fresh_object_shape(original).unwrap();
        let receiver_shape = store.fresh_object_shape(receiver).unwrap();
        let replacement_shape = store.fresh_object_shape(replacement).unwrap();
        let donor = property(&original_shape, "zeta");
        let current_donor = property(&replacement_shape, "zeta");
        let own = property(&receiver_shape, "beta");
        let seed_union = store
            .expression_union_type(&[original, seed], UnionReduction::None)
            .unwrap();
        let seed_widened = store.get_widened_type(seed_union).unwrap();
        assert_contextual_property_order(store, seed_union, original, &["zeta", "seed"]);
        let (_, seeded) =
            assert_contextual_property_order(store, seed_union, seed, &["zeta", "seed"]);
        let cached = property(&seeded, "zeta").symbol;
        assert_eq!(
            store.value_symbol_links(cached).unwrap().target,
            Some(donor.symbol)
        );
        assert_eq!(
            store.symbol(cached).unwrap().parent(),
            Some(original_shape.symbol)
        );
        assert_eq!(
            store.symbol(cached).unwrap().declarations(),
            store.symbol(donor.symbol).unwrap().declarations(),
        );
        assert!(
            store.contextual_property_order_key(cached).unwrap()
                < store.contextual_property_order_key(own.symbol).unwrap()
        );
        assert!(
            store.contextual_property_order_key(own.symbol).unwrap()
                < store
                    .contextual_property_order_key(current_donor.symbol)
                    .unwrap()
        );
        let union = store
            .expression_union_type(&[receiver, replacement], UnionReduction::None)
            .unwrap();
        assert!(!store.derived_types.widened_types.contains_key(&union));
        let widened = store.get_widened_type(union).unwrap();
        let (_, actual) =
            assert_contextual_property_order(store, union, receiver, &["zeta", "beta"]);
        assert_eq!(property(&actual, "zeta").symbol, cached);
        assert_contextual_property_order(store, union, replacement, &["beta", "zeta"]);
        for _ in 0..2 {
            assert_widening_query_preserves_store(store, seed_union, Ok(seed_widened));
            assert_widening_query_preserves_store(store, union, Ok(widened));
            assert_eq!(
                store.derived_types.undefined_properties[&EscapedName::source("zeta")],
                cached
            );
        }
    }

    #[test]
    fn contextual_object_order_rejects_coherent_donor_damage_cold_and_warm() {
        let source = parsed(concat!(
            "const original: any = { zeta: 1 }; const seed: any = { alpha: 2 }; ",
            "const replacement: any = { zeta: 3 }; const receiver: any = { beta: 4 };",
        ));
        let file = FileId::new(202_383);
        let mut context = checker_context(&[(file, &source)]);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let [original, seed, replacement, receiver] =
            ["original", "seed", "replacement", "receiver"].map(|name| {
                resolved_expression_type(&context, variable_initializer(&source, file, name))
            });
        let store = context.store_mut_for_test();
        let seed_union = store
            .expression_union_type(&[original, seed], UnionReduction::None)
            .unwrap();
        let seed_widened = store.get_widened_type(seed_union).unwrap();
        let cached = store.derived_types.undefined_properties[&EscapedName::source("zeta")];
        let record = store.symbol(cached).unwrap();
        let declarations = record.declarations().unwrap().to_vec();
        let value_declaration = record.value_declaration();
        let parent = record.parent();
        let receiver_shape = store.fresh_object_shape(receiver).unwrap();
        let foreign_declaration = store
            .symbol(property(&receiver_shape, "beta").symbol)
            .unwrap()
            .value_declaration()
            .unwrap();
        let union = store
            .expression_union_type(&[replacement, receiver], UnionReduction::None)
            .unwrap();
        for damage in 0..2 {
            if damage == 0 {
                assert!(store.set_symbol_declarations(
                    cached,
                    Some(vec![foreign_declaration]),
                    Some(foreign_declaration),
                ));
            } else {
                assert!(store.set_symbol_relationships(
                    cached,
                    None,
                    None,
                    Some(receiver_shape.symbol),
                    None
                ));
            }
            assert_contextual_order_rejection(
                store,
                union,
                [replacement, receiver],
                receiver,
                None,
            );
            assert!(store.set_symbol_declarations(
                cached,
                Some(declarations.clone()),
                value_declaration
            ));
            assert!(store.set_symbol_relationships(cached, None, None, parent, None));
            assert_widening_query_preserves_store(store, seed_union, Ok(seed_widened));
        }
        assert_coherent_contextual_donor_rejection(
            store,
            cached,
            union,
            original,
            replacement,
            receiver,
            None,
        );
        assert_widening_query_preserves_store(store, seed_union, Ok(seed_widened));
        let widened = store.get_widened_type(union).unwrap();
        let (_, actual) =
            assert_contextual_property_order(store, union, receiver, &["zeta", "beta"]);
        assert_eq!(property(&actual, "zeta").symbol, cached);
        assert_coherent_contextual_donor_rejection(
            store,
            cached,
            union,
            original,
            replacement,
            receiver,
            Some(widened),
        );
        for _ in 0..2 {
            assert_widening_query_preserves_store(store, union, Ok(widened));
        }
    }

    #[test]
    fn contextual_object_unions_preserve_optional_identity_and_option_sentinels() {
        for (strict_null_checks, exact_optional_property_types) in
            [(false, false), (true, false), (true, true)]
        {
            let library = parsed("interface Array<T> {}");
            let source = parsed("var value: any = [{ first: 1 }, { second: 2 }, { third: 3 }];");
            let library_file = FileId::new(80);
            let file = FileId::new(81);
            let files = [(library_file, &library), (file, &source)];
            let mut context = CanonicalCheckerContext::new(
                completed_bindings(&files),
                files
                    .iter()
                    .map(|(file, parsed)| (*file, &parsed.arena))
                    .collect(),
                CanonicalCheckerOptions {
                    intrinsic: crate::semantic::IntrinsicBootstrapOptions {
                        strict_null_checks,
                        exact_optional_property_types,
                    },
                    ..CanonicalCheckerOptions::default()
                },
            )
            .unwrap();
            context.check_source_file(file).unwrap();

            let value =
                resolved_expression_type(&context, variable_initializer(&source, file, "value"));
            let global_types = context.global_types().clone();
            let source_union = context
                .store()
                .canonical_array_element_type(&global_types, value)
                .unwrap()
                .unwrap();
            let source_members = match context.store().type_payload(source_union).unwrap().data() {
                TypeData::Union(union) => union.union.types.clone(),
                _ => panic!("three object literals must produce an expression union"),
            };

            let widened = context
                .store_mut_for_test()
                .get_widened_type_with_global_types(value, &global_types)
                .unwrap();
            let widened_union = context
                .store()
                .canonical_array_element_type(&global_types, widened)
                .unwrap()
                .unwrap();
            let members = match context.store().type_payload(widened_union).unwrap().data() {
                TypeData::Union(union) => union.union.types.clone(),
                _ => panic!("widened object literals must remain a canonical union"),
            };
            assert_eq!(members.len(), 3);
            let expected_undefined = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_or_missing_type;
            let mut optional_symbols = HashMap::<EscapedName, SemanticSymbolId>::new();
            for member in members {
                let shape = context.store().resolved_object_shape(member).unwrap();
                assert_eq!(shape.properties.len(), 3);
                assert_eq!(
                    shape
                        .properties
                        .iter()
                        .map(|property| property.name.as_utf8().unwrap())
                        .collect::<Vec<_>>(),
                    ["first", "second", "third"],
                );
                let (context_union, source) =
                    context.store().contextual_widened_source(member).unwrap();
                assert_eq!(context_union, source_union);
                assert!(source_members.contains(&source));
                let source_shape = context
                    .store()
                    .validated_widening_object_shape(source, &mut HashSet::new())
                    .unwrap();
                let [source_property] = source_shape.properties.as_slice() else {
                    panic!("each source object has one real required property");
                };
                assert_eq!(shape.symbol, source_shape.symbol);
                let required = property(&shape, source_property.name.as_utf8().unwrap());
                assert_eq!(required.symbol, source_property.symbol);
                assert_eq!(required.type_, source_property.type_);
                assert!(
                    context
                        .store()
                        .symbol(required.symbol)
                        .is_some_and(|record| !record.flags().contains(SymbolFlags::OPTIONAL))
                );
                for property in shape
                    .properties
                    .iter()
                    .filter(|property| property.symbol != required.symbol)
                {
                    let record = context.store().symbol(property.symbol).unwrap();
                    let links = context.store().value_symbol_links(property.symbol).unwrap();
                    let donor = context.store().symbol(links.target.unwrap()).unwrap();
                    assert!(record.flags().contains(SymbolFlags::OPTIONAL));
                    assert_eq!(property.type_, expected_undefined);
                    assert_eq!(record.parent(), donor.parent());
                    assert_ne!(record.parent(), Some(shape.symbol));
                    assert!(
                        context
                            .store()
                            .validate_contextual_widened_object_property(member, property.symbol)
                    );
                    match optional_symbols.get(&property.name) {
                        Some(previous) => assert_eq!(*previous, property.symbol),
                        None => {
                            optional_symbols.insert(property.name.clone(), property.symbol);
                        }
                    }
                }
            }
            assert_eq!(optional_symbols.len(), 3);
            assert!(source_members.iter().all(|source| {
                !context
                    .store()
                    .derived_types
                    .widened_types
                    .contains_key(source)
            }));

            let warm = (
                observable_state(context.store()),
                context.store().derived_types.contextual_widened_types.len(),
                context.store().derived_types.undefined_properties.len(),
            );
            assert_eq!(
                context
                    .store_mut_for_test()
                    .get_widened_type_with_global_types(value, &global_types),
                Ok(widened),
            );
            assert_eq!(
                (
                    observable_state(context.store()),
                    context.store().derived_types.contextual_widened_types.len(),
                    context.store().derived_types.undefined_properties.len(),
                ),
                warm,
            );

            let name = EscapedName::source("first");
            let optional = optional_symbols[&name];
            let donor = context
                .store()
                .value_symbol_links(optional)
                .and_then(|links| links.target)
                .unwrap();
            assert_eq!(
                context
                    .store_mut_for_test()
                    .derived_types
                    .undefined_properties
                    .insert(name.clone(), donor),
                Some(optional),
            );
            assert_eq!(
                context
                    .store_mut_for_test()
                    .get_widened_type_with_global_types(value, &global_types),
                Err(DerivedTypeError::InvalidWidenedTypeCache {
                    source: value,
                    cached: widened,
                }),
            );
            assert_eq!(
                context
                    .store_mut_for_test()
                    .derived_types
                    .undefined_properties
                    .insert(name, optional),
                Some(donor),
            );
            assert_eq!(
                context
                    .store_mut_for_test()
                    .get_widened_type_with_global_types(value, &global_types),
                Ok(widened),
            );

            let ordinary = context
                .store_mut_for_test()
                .get_widened_type_with_global_types(source_members[0], &global_types)
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .resolved_object_shape(ordinary)
                    .unwrap()
                    .properties
                    .len(),
                1,
            );
        }
    }

    #[test]
    fn contextual_object_unions_recursively_widen_nested_objects_and_validate_caches() {
        let library = parsed("interface Array<T> {}");
        let source = parsed("var value: any = [{ nested: { id: 1 } }, {}];");
        let library_file = FileId::new(82);
        let file = FileId::new(83);
        let mut context = checker_context(&[(library_file, &library), (file, &source)]);
        context.check_source_file(file).unwrap();

        let value =
            resolved_expression_type(&context, variable_initializer(&source, file, "value"));
        let global_types = context.global_types().clone();
        let union = context
            .store()
            .canonical_array_element_type(&global_types, value)
            .unwrap()
            .unwrap();
        let nested = match context.store().type_payload(union).unwrap().data() {
            TypeData::Union(union) => union
                .union
                .types
                .iter()
                .find_map(|member| {
                    context
                        .store()
                        .fresh_object_shape(*member)
                        .and_then(|shape| {
                            shape
                                .properties
                                .into_iter()
                                .find(|property| property.name.as_utf8() == Some("nested"))
                        })
                        .map(|property| property.type_)
                })
                .unwrap(),
            _ => panic!("nested and empty object literals must form an expression union"),
        };
        let widened = context
            .store_mut_for_test()
            .get_widened_type_with_global_types(value, &global_types)
            .unwrap();
        let widened_nested = context
            .store()
            .derived_types
            .widened_types
            .get(&nested)
            .copied()
            .unwrap();
        assert_ne!(nested, widened_nested);
        let nested_shape = context
            .store()
            .resolved_object_shape(widened_nested)
            .unwrap();
        assert_eq!(
            property(&nested_shape, "id").type_,
            context.store().intrinsic_bootstrap().unwrap().number_type,
        );

        let widened_union = context
            .store()
            .canonical_array_element_type(&global_types, widened)
            .unwrap()
            .unwrap();
        let TypeData::Union(widened_members) =
            context.store().type_payload(widened_union).unwrap().data()
        else {
            panic!("nested and empty object literals must retain both contextual shapes")
        };
        assert_eq!(widened_members.union.types.len(), 2);
        let mut required = None;
        let mut optional = None;
        for member in &widened_members.union.types {
            let shape = context.store().resolved_object_shape(*member).unwrap();
            let nested_property = property(&shape, "nested");
            let symbol = context.store().symbol(nested_property.symbol).unwrap();
            if symbol.flags().contains(SymbolFlags::OPTIONAL) {
                assert!(
                    context.store().validate_contextual_widened_object_property(
                        *member,
                        nested_property.symbol,
                    )
                );
                optional = Some(nested_property.type_);
            } else {
                required = Some(nested_property.type_);
            }
        }
        assert_eq!(required, Some(widened_nested));
        assert_eq!(
            optional,
            Some(
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .undefined_or_missing_type,
            ),
        );

        let warm = (
            observable_state(context.store()),
            context.store().derived_types.contextual_widened_types.len(),
            context.store().derived_types.undefined_properties.len(),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(value, &global_types),
            Ok(widened),
        );
        assert_eq!(
            (
                observable_state(context.store()),
                context.store().derived_types.contextual_widened_types.len(),
                context.store().derived_types.undefined_properties.len(),
            ),
            warm,
        );

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(nested, number),
            Some(widened_nested),
        );
        let poisoned = (
            observable_state(context.store()),
            context.store().derived_types.contextual_widened_types.len(),
            context.store().derived_types.undefined_properties.len(),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(value, &global_types),
            Err(DerivedTypeError::InvalidWidenedTypeCache {
                source: value,
                cached: widened,
            }),
        );
        assert_eq!(
            (
                observable_state(context.store()),
                context.store().derived_types.contextual_widened_types.len(),
                context.store().derived_types.undefined_properties.len(),
            ),
            poisoned,
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(nested, widened_nested),
            Some(number),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(value, &global_types),
            Ok(widened),
        );
    }

    #[test]
    fn contextual_object_unions_preserve_declared_members_and_validate_their_provenance() {
        let source = parsed(concat!(
            "interface DeclaredInterface { valid: boolean; message: string } ",
            "type DeclaredLiteral = { valid: boolean; detail: number }; ",
            "declare const interfaceValue: DeclaredInterface; ",
            "declare const literalValue: DeclaredLiteral; ",
            "const first: any = { valid: true }; ",
            "const second: any = { valid: true, highlighted: true }; ",
            "const interfaceRead: any = interfaceValue; ",
            "const literalRead: any = literalValue;",
        ));
        let file = FileId::new(84);
        let mut context = checker_context(&[(file, &source)]);
        context.check_source_file(file).unwrap();

        let first =
            resolved_expression_type(&context, variable_initializer(&source, file, "first"));
        let second =
            resolved_expression_type(&context, variable_initializer(&source, file, "second"));

        for (read, declared_only_property) in
            [("interfaceRead", "message"), ("literalRead", "detail")]
        {
            let declared =
                resolved_expression_type(&context, variable_initializer(&source, file, read));
            assert!(matches!(
                validate_resolved_declared_property_object(context.store(), declared),
                DeclaredPropertyObjectValidation::Valid(_)
            ));
            let union = context
                .store_mut_for_test()
                .expression_union_type(&[first, second, declared], UnionReduction::None)
                .unwrap();

            let flags = context
                .store()
                .type_payload(declared)
                .unwrap()
                .object_flags();
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_object_flags(declared, flags & !ObjectFlags::MEMBERS_RESOLVED)
            );
            let cold_poisoned = observable_state(context.store());
            assert!(matches!(
                context.store_mut_for_test().get_widened_type(union),
                Err(DerivedTypeError::InvalidWidenedTypeCache { source, .. }) if source == union
            ));
            assert_eq!(observable_state(context.store()), cold_poisoned);
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_object_flags(declared, flags)
            );

            let widened = context
                .store_mut_for_test()
                .get_widened_type(union)
                .unwrap();
            let TypeData::Union(widened_members) =
                context.store().type_payload(widened).unwrap().data()
            else {
                panic!("fresh and declared objects must remain distinct union members");
            };
            assert_eq!(widened_members.union.types.len(), 3);
            assert!(widened_members.union.types.contains(&declared));

            let mut optional_highlighted = 0;
            for member in widened_members
                .union
                .types
                .iter()
                .copied()
                .filter(|member| *member != declared)
            {
                let shape = context.store().resolved_object_shape(member).unwrap();
                assert_eq!(shape.properties.len(), 2);
                assert!(
                    shape.properties.iter().all(|property| {
                        property.name.as_utf8() != Some(declared_only_property)
                    })
                );
                let highlighted = property(&shape, "highlighted");
                if context
                    .store()
                    .symbol(highlighted.symbol)
                    .unwrap()
                    .flags()
                    .contains(SymbolFlags::OPTIONAL)
                {
                    optional_highlighted += 1;
                    assert!(
                        context.store().validate_contextual_widened_object_property(
                            member,
                            highlighted.symbol,
                        )
                    );
                }
            }
            assert_eq!(optional_highlighted, 1);
            assert!(
                !context
                    .store()
                    .derived_types
                    .contextual_widened_types
                    .contains_key(&(union, declared))
            );
            assert!(
                !context
                    .store()
                    .derived_types
                    .widened_types
                    .contains_key(&declared)
            );

            let warm = (
                observable_state(context.store()),
                context.store().derived_types.contextual_widened_types.len(),
                context.store().derived_types.undefined_properties.len(),
            );
            assert_eq!(
                context.store_mut_for_test().get_widened_type(union),
                Ok(widened),
            );
            assert_eq!(
                (
                    observable_state(context.store()),
                    context.store().derived_types.contextual_widened_types.len(),
                    context.store().derived_types.undefined_properties.len(),
                ),
                warm,
            );

            assert!(
                context
                    .store_mut_for_test()
                    .set_type_object_flags(declared, flags & !ObjectFlags::MEMBERS_RESOLVED)
            );
            let poisoned = observable_state(context.store());
            assert_eq!(
                context.store_mut_for_test().get_widened_type(union),
                Err(DerivedTypeError::InvalidWidenedTypeCache {
                    source: union,
                    cached: widened,
                }),
            );
            assert_eq!(observable_state(context.store()), poisoned);
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_object_flags(declared, flags)
            );
            assert_eq!(
                context.store_mut_for_test().get_widened_type(union),
                Ok(widened),
            );
        }
    }

    #[test]
    fn canonical_array_widening_is_recursive_cached_and_fail_closed() {
        let library = parsed("interface Array<T> {}");
        let source = parsed(concat!(
            "var values: any = [1]; ",
            "var nested: any = [{ id: 1 }];",
            "var union: any = [{ id: 1 }, { name: 2 }];",
        ));
        let library_file = FileId::new(4);
        let file = FileId::new(5);
        let mut context = checker_context(&[(library_file, &library), (file, &source)]);
        context.check_source_file(file).unwrap();

        let values =
            resolved_expression_type(&context, variable_initializer(&source, file, "values"));
        let nested =
            resolved_expression_type(&context, variable_initializer(&source, file, "nested"));
        let union =
            resolved_expression_type(&context, variable_initializer(&source, file, "union"));
        let global_types = context.global_types().clone();
        let values_reference = context
            .store()
            .canonical_array_reference(&global_types, values)
            .unwrap()
            .unwrap();
        let nested_reference = context
            .store()
            .canonical_array_reference(&global_types, nested)
            .unwrap()
            .unwrap();
        assert!(values_reference.array_literal);
        assert!(nested_reference.array_literal);

        let widened_values = context
            .store_mut_for_test()
            .get_widened_type_with_global_types(values, &global_types)
            .unwrap();
        assert_eq!(widened_values, values_reference.base_type);
        let warm_values = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(values, &global_types)
                .unwrap(),
            widened_values,
        );
        assert_eq!(observable_state(context.store()), warm_values);

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .array_literal_types
                .insert(nested_reference.base_type, number),
            Some(nested),
        );
        let poisoned_literal_state = observable_state(context.store());
        let expected_array_error = ArrayTypeError::InvalidArrayLiteralCache {
            base: nested_reference.base_type,
            cached: nested,
        };
        let array_error = context
            .store_mut_for_test()
            .get_widened_type_with_global_types(nested, &global_types)
            .unwrap_err();
        assert_eq!(
            array_error,
            DerivedTypeError::ArrayType(expected_array_error),
        );
        assert_eq!(
            std::error::Error::source(&array_error)
                .and_then(|source| source.downcast_ref::<ArrayTypeError>()),
            Some(&expected_array_error),
        );
        assert_eq!(observable_state(context.store()), poisoned_literal_state);
        assert_eq!(
            context
                .store()
                .derived_types
                .array_literal_types
                .get(&nested_reference.base_type),
            Some(&number),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .array_literal_types
                .insert(nested_reference.base_type, nested),
            Some(number),
        );

        let widened_nested = context
            .store_mut_for_test()
            .get_widened_type_with_global_types(nested, &global_types)
            .unwrap();
        let widened_nested_reference = context
            .store()
            .canonical_array_reference(&global_types, widened_nested)
            .unwrap()
            .unwrap();
        assert!(!widened_nested_reference.array_literal);
        assert_ne!(
            widened_nested_reference.element_type,
            nested_reference.element_type,
        );
        let widened_element_shape = context
            .store()
            .resolved_object_shape(widened_nested_reference.element_type)
            .unwrap();
        assert_eq!(property(&widened_element_shape, "id").type_, number,);
        assert_eq!(
            context.store().derived_types.widened_types.get(&nested),
            Some(&widened_nested),
        );

        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(nested, number),
            Some(widened_nested),
        );
        let poisoned_widened_state = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(nested, &global_types),
            Err(DerivedTypeError::InvalidWidenedTypeCache {
                source: nested,
                cached: number,
            }),
        );
        assert_eq!(observable_state(context.store()), poisoned_widened_state);
        assert_eq!(
            context.store().derived_types.widened_types.get(&nested),
            Some(&number),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .widened_types
                .insert(nested, widened_nested),
            Some(number),
        );
        let warm_nested = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(nested, &global_types)
                .unwrap(),
            widened_nested,
        );
        assert_eq!(observable_state(context.store()), warm_nested);

        let union_element = context
            .store()
            .canonical_array_element_type(&global_types, union)
            .unwrap()
            .unwrap();
        let union_record = context.store().type_payload(union_element).unwrap();
        assert!(union_record.flags().intersects(TypeFlags::UNION));
        assert!(
            union_record
                .object_flags()
                .intersects(ObjectFlags::REQUIRES_WIDENING)
        );
        let source_constituents = match context.store().type_payload(union_element).unwrap().data()
        {
            TypeData::Union(data) => data.union.types.clone(),
            _ => unreachable!("the array element was authenticated as a union"),
        };
        let widened_union = context
            .store_mut_for_test()
            .get_widened_type_with_global_types(union, &global_types)
            .unwrap();
        let widened_union_element = context
            .store()
            .canonical_array_element_type(&global_types, widened_union)
            .unwrap()
            .unwrap();
        let TypeData::Union(widened_constituents) = context
            .store()
            .type_payload(widened_union_element)
            .unwrap()
            .data()
        else {
            panic!("flat object literals must remain a canonical widened union");
        };
        assert_eq!(widened_constituents.union.types.len(), 2);
        for constituent in &widened_constituents.union.types {
            let shape = context.store().resolved_object_shape(*constituent).unwrap();
            assert_eq!(shape.properties.len(), 2);
            let optional = shape
                .properties
                .iter()
                .find(|property| {
                    context
                        .store()
                        .symbol(property.symbol)
                        .unwrap()
                        .flags()
                        .contains(SymbolFlags::OPTIONAL)
                })
                .unwrap();
            assert!(
                context
                    .store()
                    .validate_contextual_widened_object_property(*constituent, optional.symbol)
            );
        }
        assert!(source_constituents.iter().all(|source| {
            !context
                .store()
                .derived_types
                .widened_types
                .contains_key(source)
        }));
        let warm_union = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(union, &global_types),
            Ok(widened_union),
        );
        assert_eq!(observable_state(context.store()), warm_union);

        let recursive = {
            let store = context.store_mut_for_test();
            let symbol = store
                .type_payload(global_types.array_type)
                .unwrap()
                .symbol();
            let recursive = store
                .alloc_type_reference(ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL, symbol)
                .unwrap();
            assert!(store.set_object_target_and_mapper(
                recursive,
                Some(global_types.array_type),
                None,
            ));
            assert!(store.set_type_reference_resolution(recursive, None, Some(vec![recursive]),));
            assert_eq!(
                store.insert_object_instantiation(
                    global_types.array_type,
                    crate::semantic::declared::type_list_key(&[recursive]),
                    recursive,
                ),
                Some(recursive),
            );
            recursive
        };
        let recursive_boundary_state = observable_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(recursive, &global_types),
            Err(DerivedTypeError::RecursiveWideningType(recursive)),
        );
        assert_eq!(observable_state(context.store()), recursive_boundary_state);
    }
}

#[cfg(test)]
#[path = "derived_types_computed_contextual_tests.rs"]
mod computed_contextual_tests;
