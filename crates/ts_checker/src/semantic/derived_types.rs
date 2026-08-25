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
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData, SymbolFlags,
    SymbolTableId,
};

use super::{
    ArrayTypeError, CanonicalGlobalTypes,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    ids::TypeId,
    links::ValueSymbolLinks,
    mapper::TypeMapper,
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
enum WidenPlan {
    Existing {
        source: TypeId,
        target: TypeId,
    },
    Object {
        source: TypeId,
        shape: ObjectShape,
        properties: Vec<WidenPropertyPlan>,
    },
    ContextualObject {
        union: TypeId,
        source: TypeId,
        shape: ObjectShape,
        properties: Vec<WidenPropertyPlan>,
        undefined_properties: Vec<PropertyShape>,
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
        self.get_widened_type_worker(type_, None)
    }

    /// Applies pinned root-context widening with authoritative global-array
    /// identities available to the canonical `Array<T>` and
    /// `ReadonlyArray<T>` prefix.
    pub(super) fn get_widened_type_with_global_types(
        &mut self,
        type_: TypeId,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<TypeId, DerivedTypeError> {
        self.get_widened_type_worker(type_, Some(global_types))
    }

    fn get_widened_type_worker(
        &mut self,
        type_: TypeId,
        global_types: Option<&CanonicalGlobalTypes>,
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
            let result = match global_types {
                Some(global_types) => self.prepare_type_query_types_with_global_types(
                    &[],
                    &[],
                    &[],
                    union_count,
                    0,
                    global_types,
                ),
                None => self.prepare_type_query_types(&[], &[], &[], union_count, 0),
            };
            result.map_err(|error| widening_union_error(type_, error))?;
        }

        for plan in plans {
            self.publish_widened_type(plan, global_types);
        }
        Ok(*self
            .derived_types
            .widened_types
            .get(&type_)
            .expect("the root widened type plan was published"))
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
    /// capability installed on the relation session.
    pub(super) fn validate_derived_object_literal_with_array_targets(
        &self,
        type_: TypeId,
        array_targets: CanonicalArrayTargets,
    ) -> DerivedObjectLiteralValidation {
        self.validate_derived_object_literal(type_, Some(array_targets))
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
        let shape = self
            .fresh_object_shape(source)
            .ok_or(DerivedTypeError::MalformedObjectLiteral(source))?;
        let mut properties = Vec::with_capacity(shape.properties.len());
        for property in &shape.properties {
            let transform = if self.is_fresh_object_literal(property.type_) {
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
        let mut regular_visiting = HashSet::new();
        let shape = self
            .validated_widening_object_shape(source, &mut regular_visiting)
            .ok_or(DerivedTypeError::MalformedObjectLiteral(source))?;
        let mut properties = Vec::with_capacity(shape.properties.len());
        for property in &shape.properties {
            let transform =
                self.plan_widened_type(property.type_, global_types, plans, visiting, planned)?;
            properties.push(WidenPropertyPlan {
                source: property.symbol,
                name: property.name.clone(),
                transform,
            });
        }
        visiting.remove(&source);
        planned.insert(source);
        plans.push(WidenPlan::Object {
            source,
            shape,
            properties,
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
            if record.flags().intersects(TypeFlags::NULLABLE) {
                continue;
            }
            if !record.object_flags().contains(ObjectFlags::OBJECT_LITERAL) {
                return Err(DerivedTypeError::UnsupportedWideningType(*member));
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
                    || property_record
                        .object_flags()
                        .intersects(ObjectFlags::REQUIRES_WIDENING)
                        && !property_record
                            .flags()
                            .intersects(TypeFlags::ANY | TypeFlags::NULLABLE)
                {
                    return Err(DerivedTypeError::UnsupportedWideningType(property.type_));
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
                let transformed = if property_record
                    .object_flags()
                    .intersects(ObjectFlags::REQUIRES_WIDENING)
                {
                    self.intrinsic_bootstrap()
                        .ok_or(DerivedTypeError::BootstrapUninitialized)?
                        .any_type
                } else {
                    property.type_
                };
                properties.push(WidenPropertyPlan {
                    source: property.symbol,
                    name: property.name.clone(),
                    transform: WidenTransform::Identity(transformed),
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
                if let Some(cached) = self
                    .derived_types
                    .undefined_properties
                    .get(&property.name)
                    .copied()
                    && !self.valid_cached_undefined_property(&property.name, cached)
                {
                    return Err(DerivedTypeError::MalformedObjectLiteral(*member));
                }
            }

            plans.push(WidenPlan::ContextualObject {
                union,
                source: *member,
                shape: shape.clone(),
                properties,
                undefined_properties,
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
            None,
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
    ) {
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
                assert!(self.set_structured_type_members(
                    widened,
                    Some(members),
                    (!properties.is_empty()).then_some(properties),
                    None,
                    None,
                    None,
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

                let retained = shape.object_flags
                    & (ObjectFlags::JS_LITERAL | ObjectFlags::NON_INFERRABLE_TYPE);
                let widened = self
                    .alloc_plain_object_type(ObjectFlags::ANONYMOUS | retained, Some(shape.symbol))
                    .expect("the contextual object plan authenticated its owner and flags");
                assert!(self.set_structured_type_members(
                    widened,
                    Some(members),
                    (!properties.is_empty()).then_some(properties),
                    None,
                    None,
                    None,
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
                    self.expression_union_type_with_global_types(global_types, &members, reduction)
                        .expect("preflighted widened union members remain canonical")
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

    fn contextual_sibling_properties(&self, union: TypeId) -> Option<Vec<PropertyShape>> {
        let TypeData::Union(data) = self.type_payload(union)?.data() else {
            return None;
        };
        let mut properties = Vec::<PropertyShape>::new();
        let mut names = HashMap::<EscapedName, usize>::new();
        for member in &data.union.types {
            let record = self.type_payload(*member)?;
            if record.flags().intersects(TypeFlags::NULLABLE) {
                continue;
            }
            let mut regular_visiting = HashSet::new();
            let shape = self.validated_widening_object_shape(*member, &mut regular_visiting)?;
            for property in shape.properties {
                let record = self.type_payload(property.type_)?;
                if record.flags().intersects(TypeFlags::OBJECT)
                    || record
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

    fn fresh_object_shape(&self, type_: TypeId) -> Option<ObjectShape> {
        let record = self.type_payload(type_)?;
        let TypeData::Object(object) = record.data() else {
            return None;
        };
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
        let expected_property_checks = match properties.first() {
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
            || !valid_structured_tail(&object.structured)
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
        if self
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
        if source == target
            || target_shape.flags != TypeFlags::OBJECT
            || target_shape.object_flags
                != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED | retained
            || target_shape.symbol != source_shape.symbol
            || target_shape.members == source_shape.members
            || target_shape.properties.len()
                != source_shape.properties.len() + missing_properties.len()
        {
            return false;
        }

        for (source_property, target_property) in
            source_shape.properties.iter().zip(&target_shape.properties)
        {
            let Some(property_record) = self.type_payload(source_property.type_) else {
                return false;
            };
            let expected_type = if property_record
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
        }

        target_shape.properties[source_shape.properties.len()..]
            .iter()
            .zip(missing_properties)
            .all(|(property, donor)| {
                property.name == donor.name
                    && self.validate_contextual_widened_object_property(target, property.symbol)
            })
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
    structured.constrained == ConstrainedTypeData::default()
        && structured.signatures.is_none()
        && structured.call_signature_count == 0
        && structured.index_infos.is_none()
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
                assert!(
                    context
                        .store()
                        .symbol(shape.properties[0].symbol)
                        .is_some_and(|record| !record.flags().contains(SymbolFlags::OPTIONAL))
                );
                for property in &shape.properties[1..] {
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
    fn contextual_object_unions_reject_nested_objects_before_publication() {
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
        let before = (
            observable_state(context.store()),
            context.store().derived_types.contextual_widened_types.len(),
            context.store().derived_types.undefined_properties.len(),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .get_widened_type_with_global_types(value, &global_types),
            Err(DerivedTypeError::UnsupportedWideningType(nested)),
        );
        assert_eq!(
            (
                observable_state(context.store()),
                context.store().derived_types.contextual_widened_types.len(),
                context.store().derived_types.undefined_properties.len(),
            ),
            before,
        );
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
