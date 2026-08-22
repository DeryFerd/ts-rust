//! Store-owned canonical type mappers.
//!
//! This is the dependency-closed portion of pinned `checker/mapper.go`.
//! Direct and callback-backed mappers are represented here. Deferred targets
//! are called only when their source matches, and callback results are checked
//! against their owning store before they become visible. Composite mappers
//! delegate recursive substitution to the private `instantiate` module.
//! `InferenceTypeMapper` remains with its owning inference algorithm because
//! mapping can mutate an `InferenceContext`.

use std::sync::Arc;

use super::{
    ids::{TypeId, TypeMapperId},
    store::SemanticStore,
    type_records::{CanonicalSemanticStore, TypeData, TypeRecord},
};

/// Exact numeric discriminator returned by pinned `TypeMapper.Kind`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(i32)]
pub enum TypeMapperKind {
    Unknown = 0,
    Simple = 1,
    Array = 2,
    Merged = 3,
}

/// Immutable payload for one dependency-closed canonical type mapper.
///
/// Fields are private so mapper graphs can only be created through
/// [`CanonicalTypeMapperStore`]. Every edge therefore belongs to the same
/// semantic store and points to an earlier mapper allocation, making the graph
/// acyclic without a runtime recursion sentinel.
#[derive(Debug, Eq, PartialEq)]
pub struct TypeMapper {
    data: TypeMapperData,
}

#[derive(Debug, Eq, PartialEq)]
enum TypeMapperData {
    Simple {
        source: TypeId,
        target: TypeId,
    },
    Array {
        sources: Vec<TypeId>,
        targets: Vec<TypeId>,
    },
    ArrayToSingle {
        sources: Vec<TypeId>,
        target: TypeId,
    },
    Deferred {
        sources: Vec<TypeId>,
        targets: Vec<DeferredTypeTarget>,
    },
    Function(FunctionTypeMapping),
    Merged {
        first: TypeMapperId,
        second: TypeMapperId,
    },
    Composite {
        first: TypeMapperId,
        second: TypeMapperId,
    },
}

#[derive(Clone)]
struct DeferredTypeTarget(Arc<dyn Fn() -> TypeId + Send + Sync>);

impl std::fmt::Debug for DeferredTypeTarget {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("DeferredTypeTarget(..)")
    }
}

impl PartialEq for DeferredTypeTarget {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for DeferredTypeTarget {}

#[derive(Clone)]
struct FunctionTypeMapping(Arc<dyn Fn(TypeId) -> TypeId + Send + Sync>);

impl std::fmt::Debug for FunctionTypeMapping {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("FunctionTypeMapping(..)")
    }
}

impl PartialEq for FunctionTypeMapping {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for FunctionTypeMapping {}

/// One dependency-closed mapper operation exposed to the instantiation
/// engine. Direct mappings need no semantic recursion. Merged and composite
/// records retain their distinct pinned evaluation rules.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TypeMapperApplication {
    Direct(TypeId),
    Merged {
        first: TypeMapperId,
        second: TypeMapperId,
    },
    Composite {
        first: TypeMapperId,
        second: TypeMapperId,
    },
}

impl TypeMapper {
    const fn simple(source: TypeId, target: TypeId) -> Self {
        Self {
            data: TypeMapperData::Simple { source, target },
        }
    }

    fn array(sources: Vec<TypeId>, targets: Vec<TypeId>) -> Self {
        Self {
            data: TypeMapperData::Array { sources, targets },
        }
    }

    fn array_to_single(sources: Vec<TypeId>, target: TypeId) -> Self {
        Self {
            data: TypeMapperData::ArrayToSingle { sources, target },
        }
    }

    fn deferred(sources: Vec<TypeId>, targets: Vec<DeferredTypeTarget>) -> Self {
        Self {
            data: TypeMapperData::Deferred { sources, targets },
        }
    }

    fn function(mapping: FunctionTypeMapping) -> Self {
        Self {
            data: TypeMapperData::Function(mapping),
        }
    }

    const fn merged(first: TypeMapperId, second: TypeMapperId) -> Self {
        Self {
            data: TypeMapperData::Merged { first, second },
        }
    }

    const fn composite(first: TypeMapperId, second: TypeMapperId) -> Self {
        Self {
            data: TypeMapperData::Composite { first, second },
        }
    }

    /// Mirrors the overrides in pinned `mapper.go`. Array-to-single inherits
    /// `TypeMapperBase.Kind`, so its exact kind is `Unknown`.
    #[must_use]
    pub const fn kind(&self) -> TypeMapperKind {
        match &self.data {
            TypeMapperData::Simple { .. } => TypeMapperKind::Simple,
            TypeMapperData::Array { .. } => TypeMapperKind::Array,
            TypeMapperData::Merged { .. } => TypeMapperKind::Merged,
            TypeMapperData::ArrayToSingle { .. }
            | TypeMapperData::Deferred { .. }
            | TypeMapperData::Function(_)
            | TypeMapperData::Composite { .. } => TypeMapperKind::Unknown,
        }
    }
}

/// Canonical semantic store with the exact mapper payload installed.
pub type CanonicalTypeMapperStore = CanonicalSemanticStore<TypeMapper>;

impl SemanticStore<TypeRecord, TypeMapper> {
    /// Pinned `newTypeMapper`: one source uses the simple representation;
    /// every other arity, including zero, uses the array representation.
    ///
    /// Invalid arity or foreign type identity is rejected before allocation.
    pub fn new_type_mapper(
        &mut self,
        sources: Vec<TypeId>,
        targets: Vec<TypeId>,
    ) -> Option<TypeMapperId> {
        if sources.len() != targets.len()
            || !self.mapper_types_are_owned(&sources)
            || !self.mapper_types_are_owned(&targets)
        {
            return None;
        }
        if sources.len() == 1 {
            Some(self.alloc_mapper(TypeMapper::simple(sources[0], targets[0])))
        } else {
            Some(self.alloc_mapper(TypeMapper::array(sources, targets)))
        }
    }

    /// Pinned `newSimpleTypeMapper` with store-provenance validation.
    pub fn new_simple_type_mapper(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Option<TypeMapperId> {
        if !self.mapper_types_are_owned(&[source, target]) {
            return None;
        }
        Some(self.alloc_mapper(TypeMapper::simple(source, target)))
    }

    /// Returns the exact endpoints only for the simple mapper representation.
    /// Evaluating a mapper is insufficient for cache validation because an
    /// unrelated simple mapper preserves an input by identity.
    #[cfg(test)]
    pub(super) fn simple_type_mapper_endpoints(
        &self,
        mapper: TypeMapperId,
    ) -> Option<(TypeId, TypeId)> {
        let TypeMapperData::Simple { source, target } = &self.mapper_payload(mapper)?.data else {
            return None;
        };
        Some((*source, *target))
    }

    /// Validates the exact ordered endpoints and representation selected by
    /// pinned `newTypeMapper`. Evaluating a mapper is insufficient for cache
    /// validation because unmatched inputs are preserved by identity.
    pub(super) fn type_mapper_has_exact_endpoints(
        &self,
        mapper: TypeMapperId,
        sources: &[TypeId],
        targets: &[TypeId],
    ) -> Option<bool> {
        let exact = match &self.mapper_payload(mapper)?.data {
            TypeMapperData::Simple { source, target } => {
                sources.len() == 1
                    && targets.len() == 1
                    && sources == [*source]
                    && targets == [*target]
            }
            TypeMapperData::Array {
                sources: actual_sources,
                targets: actual_targets,
            } => {
                sources.len() != 1
                    && targets.len() != 1
                    && sources == actual_sources.as_slice()
                    && targets == actual_targets.as_slice()
            }
            TypeMapperData::ArrayToSingle { .. }
            | TypeMapperData::Deferred { .. }
            | TypeMapperData::Function(_)
            | TypeMapperData::Merged { .. }
            | TypeMapperData::Composite { .. } => false,
        };
        Some(exact)
    }

    /// Pinned `newArrayTypeMapper` with exact parallel-array semantics.
    pub fn new_array_type_mapper(
        &mut self,
        sources: Vec<TypeId>,
        targets: Vec<TypeId>,
    ) -> Option<TypeMapperId> {
        if sources.len() != targets.len()
            || !self.mapper_types_are_owned(&sources)
            || !self.mapper_types_are_owned(&targets)
        {
            return None;
        }
        Some(self.alloc_mapper(TypeMapper::array(sources, targets)))
    }

    /// Pinned `newArrayToSingleTypeMapper`.
    pub fn new_array_to_single_type_mapper(
        &mut self,
        sources: Vec<TypeId>,
        target: TypeId,
    ) -> Option<TypeMapperId> {
        if !self.mapper_types_are_owned(&sources) || self.type_payload(target).is_none() {
            return None;
        }
        Some(self.alloc_mapper(TypeMapper::array_to_single(sources, target)))
    }

    /// Creates pinned `DeferredTypeMapper` without demanding its targets.
    ///
    /// A target is called for each matching lookup, as in upstream. Its result
    /// must belong to this store or the lookup fails.
    pub fn new_deferred_type_mapper<F>(
        &mut self,
        sources: Vec<TypeId>,
        targets: Vec<F>,
    ) -> Option<TypeMapperId>
    where
        F: Fn() -> TypeId + Send + Sync + 'static,
    {
        if sources.len() != targets.len() || !self.mapper_types_are_owned(&sources) {
            return None;
        }
        let targets = targets
            .into_iter()
            .map(|target| DeferredTypeTarget(Arc::new(target)))
            .collect();
        Some(self.alloc_mapper(TypeMapper::deferred(sources, targets)))
    }

    /// Creates pinned `FunctionTypeMapper` with store-validated results.
    pub fn new_function_type_mapper<F>(&mut self, mapping: F) -> TypeMapperId
    where
        F: Fn(TypeId) -> TypeId + Send + Sync + 'static,
    {
        self.alloc_mapper(TypeMapper::function(FunctionTypeMapping(Arc::new(mapping))))
    }

    /// Maps forward type-parameter references to the canonical unknown type.
    ///
    /// `index` is the first unresolved inference, matching pinned
    /// `newBackreferenceMapper`.
    pub fn new_backreference_mapper(
        &mut self,
        type_parameters: &[TypeId],
        index: usize,
        unknown_type: TypeId,
    ) -> Option<TypeMapperId> {
        if index > type_parameters.len()
            || !self.mapper_types_are_owned(type_parameters)
            || self.type_payload(unknown_type).is_none()
        {
            return None;
        }
        self.new_array_to_single_type_mapper(type_parameters[index..].to_vec(), unknown_type)
    }

    /// Pinned `mergeTypeMappers`. A nil first mapper returns `second` without
    /// allocating; otherwise mapping applies `first` and then `second`.
    pub fn merge_type_mappers(
        &mut self,
        first: Option<TypeMapperId>,
        second: TypeMapperId,
    ) -> Option<TypeMapperId> {
        if self.mapper_payload(second).is_none()
            || first.is_some_and(|mapper| self.mapper_payload(mapper).is_none())
        {
            return None;
        }
        match first {
            None => Some(second),
            Some(first) => Some(self.alloc_mapper(TypeMapper::merged(first, second))),
        }
    }

    /// Pinned `combineTypeMappers`. A nil first mapper returns `second`
    /// without allocating. Otherwise a composite mapper first applies
    /// `first`; when that changes the input, the changed result is recursively
    /// instantiated through `second` rather than merely mapped as a whole.
    pub(super) fn combine_type_mappers(
        &mut self,
        first: Option<TypeMapperId>,
        second: TypeMapperId,
    ) -> Option<TypeMapperId> {
        if self.mapper_payload(second).is_none()
            || first.is_some_and(|mapper| self.mapper_payload(mapper).is_none())
        {
            return None;
        }
        match first {
            None => Some(second),
            Some(first) => Some(self.alloc_mapper(TypeMapper::composite(first, second))),
        }
    }

    /// Pinned `prependTypeMapping`.
    pub fn prepend_type_mapping(
        &mut self,
        source: TypeId,
        target: TypeId,
        mapper: Option<TypeMapperId>,
    ) -> Option<TypeMapperId> {
        if !self.mapper_types_are_owned(&[source, target])
            || mapper.is_some_and(|mapper| self.mapper_payload(mapper).is_none())
        {
            return None;
        }
        let simple = self.alloc_mapper(TypeMapper::simple(source, target));
        match mapper {
            None => Some(simple),
            Some(second) => Some(self.alloc_mapper(TypeMapper::merged(simple, second))),
        }
    }

    /// Pinned `appendTypeMapping`.
    pub fn append_type_mapping(
        &mut self,
        mapper: Option<TypeMapperId>,
        source: TypeId,
        target: TypeId,
    ) -> Option<TypeMapperId> {
        if !self.mapper_types_are_owned(&[source, target])
            || mapper.is_some_and(|mapper| self.mapper_payload(mapper).is_none())
        {
            return None;
        }
        let simple = self.alloc_mapper(TypeMapper::simple(source, target));
        match mapper {
            None => Some(simple),
            Some(first) => Some(self.alloc_mapper(TypeMapper::merged(first, simple))),
        }
    }

    /// Applies a canonical mapper that needs no recursive instantiation to one
    /// canonical type identity.
    ///
    /// Foreign or missing handles return `None`. Composite graphs also return
    /// `None`; executing them without the instantiation session would silently
    /// collapse their recursive substitution semantics into merged semantics.
    #[must_use]
    pub fn map_type(&self, mapper: TypeMapperId, type_id: TypeId) -> Option<TypeId> {
        self.type_payload(type_id)?;
        self.mapper_payload(mapper)?;
        self.map_type_without_instantiation(mapper, type_id)
    }

    /// Projects one mapper record without traversing another mapper edge.
    /// Composite execution remains in `instantiate.rs`, which owns recursion,
    /// budgets, and active-mapper caches.
    pub(super) fn mapper_application(
        &self,
        mapper: TypeMapperId,
        type_id: TypeId,
    ) -> Option<TypeMapperApplication> {
        self.type_payload(type_id)?;
        let application = match &self.mapper_payload(mapper)?.data {
            TypeMapperData::Simple { source, target } => {
                TypeMapperApplication::Direct(if type_id == *source { *target } else { type_id })
            }
            TypeMapperData::Array { sources, targets } => TypeMapperApplication::Direct(
                sources
                    .iter()
                    .position(|source| *source == type_id)
                    .map_or(type_id, |index| targets[index]),
            ),
            TypeMapperData::ArrayToSingle { sources, target } => {
                TypeMapperApplication::Direct(if sources.contains(&type_id) {
                    *target
                } else {
                    type_id
                })
            }
            TypeMapperData::Deferred { sources, targets } => {
                let substituted_type = sources
                    .iter()
                    .position(|source| *source == type_id)
                    .map_or(type_id, |index| (targets[index].0)());
                self.type_payload(substituted_type)?;
                TypeMapperApplication::Direct(substituted_type)
            }
            TypeMapperData::Function(mapping) => {
                let substituted_type = (mapping.0)(type_id);
                self.type_payload(substituted_type)?;
                TypeMapperApplication::Direct(substituted_type)
            }
            TypeMapperData::Merged { first, second } => TypeMapperApplication::Merged {
                first: *first,
                second: *second,
            },
            TypeMapperData::Composite { first, second } => TypeMapperApplication::Composite {
                first: *first,
                second: *second,
            },
        };
        Some(application)
    }

    #[must_use]
    pub fn mapper_kind(&self, mapper: TypeMapperId) -> Option<TypeMapperKind> {
        Some(self.mapper_payload(mapper)?.kind())
    }

    /// Mirrors `MapsThisOnly`. Merged mappers inherit the base implementation
    /// and therefore return false even when their components happen to map a
    /// single `this` parameter.
    #[must_use]
    pub fn mapper_maps_this_only(&self, mapper: TypeMapperId) -> Option<bool> {
        let mapper = self.mapper_payload(mapper)?;
        let source = match &mapper.data {
            TypeMapperData::Simple { source, .. } => Some(*source),
            TypeMapperData::Array { sources, .. }
            | TypeMapperData::ArrayToSingle { sources, .. }
            | TypeMapperData::Deferred { sources, .. }
                if sources.len() == 1 =>
            {
                Some(sources[0])
            }
            TypeMapperData::Array { .. }
            | TypeMapperData::ArrayToSingle { .. }
            | TypeMapperData::Deferred { .. }
            | TypeMapperData::Function(_)
            | TypeMapperData::Merged { .. }
            | TypeMapperData::Composite { .. } => None,
        };
        Some(source.is_some_and(|source| {
            matches!(
                self.type_payload(source).map(TypeRecord::data),
                Some(TypeData::TypeParameter(data)) if data.is_this_type
            )
        }))
    }

    fn mapper_types_are_owned(&self, types: &[TypeId]) -> bool {
        types
            .iter()
            .all(|type_id| self.type_payload(*type_id).is_some())
    }

    fn map_type_without_instantiation(
        &self,
        mapper: TypeMapperId,
        type_id: TypeId,
    ) -> Option<TypeId> {
        match &self
            .mapper_payload(mapper)
            .expect("canonical mapper edges are validated at construction")
            .data
        {
            TypeMapperData::Simple { source, target } => {
                if type_id == *source {
                    Some(*target)
                } else {
                    Some(type_id)
                }
            }
            TypeMapperData::Array { sources, targets } => sources
                .iter()
                .position(|source| *source == type_id)
                .map_or(Some(type_id), |index| Some(targets[index])),
            TypeMapperData::ArrayToSingle { sources, target } => {
                if sources.contains(&type_id) {
                    Some(*target)
                } else {
                    Some(type_id)
                }
            }
            TypeMapperData::Deferred { sources, targets } => {
                let substituted_type = sources
                    .iter()
                    .position(|source| *source == type_id)
                    .map_or(type_id, |index| (targets[index].0)());
                self.type_payload(substituted_type)
                    .map(|_| substituted_type)
            }
            TypeMapperData::Function(mapping) => {
                let substituted_type = (mapping.0)(type_id);
                self.type_payload(substituted_type)
                    .map(|_| substituted_type)
            }
            TypeMapperData::Merged { first, second } => {
                let intermediate = self.map_type_without_instantiation(*first, type_id)?;
                self.map_type_without_instantiation(*second, intermediate)
            }
            TypeMapperData::Composite { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };

    use super::*;
    use crate::semantic::{
        type_records::CacheHashKey,
        types::{ObjectFlags, TypeFlags},
    };

    fn type_(store: &mut CanonicalTypeMapperStore, name: &'static str) -> TypeId {
        store
            .alloc_intrinsic_type(TypeFlags::ANY, name)
            .expect("test intrinsic is valid")
    }

    #[test]
    fn mapper_kinds_match_pinned_numeric_and_override_behavior() {
        assert_eq!(TypeMapperKind::Unknown as i32, 0);
        assert_eq!(TypeMapperKind::Simple as i32, 1);
        assert_eq!(TypeMapperKind::Array as i32, 2);
        assert_eq!(TypeMapperKind::Merged as i32, 3);

        let mut store = CanonicalTypeMapperStore::new();
        let a = type_(&mut store, "a");
        let b = type_(&mut store, "b");
        let simple = store.new_simple_type_mapper(a, b).unwrap();
        let array = store.new_array_type_mapper(vec![a], vec![b]).unwrap();
        let array_to_single = store.new_array_to_single_type_mapper(vec![a], b).unwrap();
        let merged = store.merge_type_mappers(Some(simple), array).unwrap();
        let composite = store.combine_type_mappers(Some(simple), array).unwrap();

        assert_eq!(store.mapper_kind(simple), Some(TypeMapperKind::Simple));
        assert_eq!(store.mapper_kind(array), Some(TypeMapperKind::Array));
        assert_eq!(
            store.mapper_kind(array_to_single),
            Some(TypeMapperKind::Unknown)
        );
        assert_eq!(store.mapper_kind(merged), Some(TypeMapperKind::Merged));
        assert_eq!(store.mapper_kind(composite), Some(TypeMapperKind::Unknown));
    }

    #[test]
    fn combined_mappers_retain_composite_semantics_for_instantiation() {
        let mut store = CanonicalTypeMapperStore::new();
        let a = type_(&mut store, "a");
        let b = type_(&mut store, "b");
        let c = type_(&mut store, "c");
        let first = store.new_simple_type_mapper(a, b).unwrap();
        let second = store.new_simple_type_mapper(b, c).unwrap();

        let before = store.mapper_len();
        assert_eq!(store.combine_type_mappers(None, second), Some(second));
        assert_eq!(store.mapper_len(), before);

        let composite = store.combine_type_mappers(Some(first), second).unwrap();
        assert_eq!(store.map_type(composite, a), None);
        assert_eq!(store.mapper_maps_this_only(composite), Some(false));
        assert_eq!(
            store.type_mapper_has_exact_endpoints(composite, &[a], &[c]),
            Some(false)
        );
        assert_eq!(
            store.mapper_application(composite, a),
            Some(TypeMapperApplication::Composite { first, second })
        );
    }

    #[test]
    fn new_type_mapper_preserves_zero_one_many_and_first_match_semantics() {
        let mut store = CanonicalTypeMapperStore::new();
        let a = type_(&mut store, "a");
        let b = type_(&mut store, "b");
        let c = type_(&mut store, "c");
        let d = type_(&mut store, "d");

        let empty = store.new_type_mapper(vec![], vec![]).unwrap();
        assert_eq!(store.mapper_kind(empty), Some(TypeMapperKind::Array));
        assert_eq!(store.map_type(empty, a), Some(a));
        assert_eq!(
            store.type_mapper_has_exact_endpoints(empty, &[], &[]),
            Some(true)
        );

        let one = store.new_type_mapper(vec![a], vec![b]).unwrap();
        assert_eq!(store.mapper_kind(one), Some(TypeMapperKind::Simple));
        assert_eq!(store.map_type(one, a), Some(b));
        assert_eq!(store.map_type(one, c), Some(c));
        assert_eq!(
            store.type_mapper_has_exact_endpoints(one, &[a], &[b]),
            Some(true)
        );
        let wrong_one_representation = store.new_array_type_mapper(vec![a], vec![b]).unwrap();
        assert_eq!(
            store.type_mapper_has_exact_endpoints(wrong_one_representation, &[a], &[b]),
            Some(false),
            "one-row newTypeMapper caches must use the simple representation"
        );

        let many = store
            .new_array_type_mapper(vec![a, a, c], vec![b, d, d])
            .unwrap();
        assert_eq!(store.map_type(many, a), Some(b));
        assert_eq!(store.map_type(many, c), Some(d));
        assert_eq!(store.map_type(many, d), Some(d));
        assert_eq!(
            store.type_mapper_has_exact_endpoints(many, &[a, a, c], &[b, d, d]),
            Some(true)
        );
        assert_eq!(
            store.type_mapper_has_exact_endpoints(many, &[a, c, a], &[b, d, d]),
            Some(false),
            "ordered source rows are part of the cache identity"
        );

        let to_single = store
            .new_array_to_single_type_mapper(vec![a, c], d)
            .unwrap();
        assert_eq!(store.map_type(to_single, a), Some(d));
        assert_eq!(store.map_type(to_single, c), Some(d));
        assert_eq!(store.map_type(to_single, b), Some(b));
        assert_eq!(
            store.type_mapper_has_exact_endpoints(to_single, &[a, c], &[d, d]),
            Some(false)
        );
    }

    #[test]
    fn merged_prepend_and_append_preserve_composition_precedence() {
        let mut store = CanonicalTypeMapperStore::new();
        let a = type_(&mut store, "a");
        let b = type_(&mut store, "b");
        let c = type_(&mut store, "c");
        let d = type_(&mut store, "d");

        let ab = store.new_simple_type_mapper(a, b).unwrap();
        let bc = store.new_simple_type_mapper(b, c).unwrap();
        let merged = store.merge_type_mappers(Some(ab), bc).unwrap();
        assert_eq!(store.map_type(merged, a), Some(c));
        assert_eq!(store.map_type(merged, b), Some(c));
        assert_eq!(store.map_type(merged, d), Some(d));

        let before = store.mapper_len();
        assert_eq!(store.merge_type_mappers(None, ab), Some(ab));
        assert_eq!(store.mapper_len(), before);

        let existing = store.new_simple_type_mapper(a, b).unwrap();
        let prepended = store.prepend_type_mapping(a, c, Some(existing)).unwrap();
        assert_eq!(store.map_type(prepended, a), Some(c));

        let appended = store.append_type_mapping(Some(existing), b, c).unwrap();
        assert_eq!(store.map_type(appended, a), Some(c));
    }

    #[test]
    fn deferred_mapper_demands_only_the_first_matching_target() {
        type DeferredTarget = Box<dyn Fn() -> TypeId + Send + Sync>;

        let mut store = CanonicalTypeMapperStore::new();
        let a = type_(&mut store, "a");
        let b = type_(&mut store, "b");
        let c = type_(&mut store, "c");
        let first_calls = Arc::new(AtomicUsize::new(0));
        let second_calls = Arc::new(AtomicUsize::new(0));
        let first_counter = Arc::clone(&first_calls);
        let second_counter = Arc::clone(&second_calls);
        let targets: Vec<DeferredTarget> = vec![
            Box::new(move || {
                first_counter.fetch_add(1, Ordering::Relaxed);
                b
            }),
            Box::new(move || {
                second_counter.fetch_add(1, Ordering::Relaxed);
                c
            }),
        ];
        let mapper = store.new_deferred_type_mapper(vec![a, a], targets).unwrap();

        assert_eq!(store.mapper_kind(mapper), Some(TypeMapperKind::Unknown));
        assert_eq!(store.map_type(mapper, c), Some(c));
        assert_eq!(first_calls.load(Ordering::Relaxed), 0);
        assert_eq!(second_calls.load(Ordering::Relaxed), 0);
        assert_eq!(store.map_type(mapper, a), Some(b));
        assert_eq!(store.map_type(mapper, a), Some(b));
        assert_eq!(first_calls.load(Ordering::Relaxed), 2);
        assert_eq!(second_calls.load(Ordering::Relaxed), 0);
        assert_eq!(
            store.mapper_application(mapper, a),
            Some(TypeMapperApplication::Direct(b))
        );
        assert_eq!(first_calls.load(Ordering::Relaxed), 3);
    }

    #[test]
    fn callback_mappers_reject_foreign_results_without_eager_demand() {
        let mut store = CanonicalTypeMapperStore::new();
        let local = type_(&mut store, "local");
        let unchanged = type_(&mut store, "unchanged");
        let mut foreign_store = CanonicalTypeMapperStore::new();
        let foreign = type_(&mut foreign_store, "foreign");

        let deferred = store
            .new_deferred_type_mapper(vec![local], vec![move || foreign])
            .unwrap();
        assert_eq!(store.map_type(deferred, unchanged), Some(unchanged));
        assert_eq!(store.map_type(deferred, local), None);
        assert_eq!(store.mapper_application(deferred, local), None);

        let function = store.new_function_type_mapper(
            move |type_| {
                if type_ == local { foreign } else { type_ }
            },
        );
        assert_eq!(store.mapper_kind(function), Some(TypeMapperKind::Unknown));
        assert_eq!(store.mapper_maps_this_only(function), Some(false));
        assert_eq!(store.map_type(function, unchanged), Some(unchanged));
        assert_eq!(store.map_type(function, local), None);
        assert_eq!(store.mapper_application(function, local), None);
    }

    #[test]
    fn function_mapper_composes_without_changing_callback_order() {
        let mut store = CanonicalTypeMapperStore::new();
        let a = type_(&mut store, "a");
        let b = type_(&mut store, "b");
        let c = type_(&mut store, "c");
        let calls = Arc::new(AtomicUsize::new(0));
        let counter = Arc::clone(&calls);
        let function = store.new_function_type_mapper(move |type_| {
            counter.fetch_add(1, Ordering::Relaxed);
            if type_ == a { b } else { type_ }
        });
        let second = store.new_simple_type_mapper(b, c).unwrap();
        let merged = store.merge_type_mappers(Some(function), second).unwrap();

        assert_eq!(calls.load(Ordering::Relaxed), 0);
        assert_eq!(store.map_type(merged, a), Some(c));
        assert_eq!(calls.load(Ordering::Relaxed), 1);
        assert_eq!(store.map_type(merged, c), Some(c));
        assert_eq!(calls.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn backreference_mapper_maps_only_unresolved_forward_parameters() {
        let mut store = CanonicalTypeMapperStore::new();
        let first = store.alloc_type_parameter(None).unwrap();
        let second = store.alloc_type_parameter(None).unwrap();
        let third = store.alloc_type_parameter(None).unwrap();
        let unknown = type_(&mut store, "unknown");
        let mapper = store
            .new_backreference_mapper(&[first, second, third], 1, unknown)
            .unwrap();

        assert_eq!(store.mapper_kind(mapper), Some(TypeMapperKind::Unknown));
        assert_eq!(store.map_type(mapper, first), Some(first));
        assert_eq!(store.map_type(mapper, second), Some(unknown));
        assert_eq!(store.map_type(mapper, third), Some(unknown));

        let before = store.mapper_len();
        assert_eq!(
            store.new_backreference_mapper(&[first, second, third], 4, unknown),
            None
        );
        assert_eq!(store.mapper_len(), before);
        let empty = store
            .new_backreference_mapper(&[first, second, third], 3, unknown)
            .unwrap();
        assert_eq!(store.map_type(empty, third), Some(third));
    }

    #[test]
    fn maps_this_only_uses_the_canonical_marker_and_not_shape() {
        let mut store = CanonicalTypeMapperStore::new();
        let ordinary = store.alloc_type_parameter(None).unwrap();
        let this_type = store.alloc_type_parameter(None).unwrap();
        let owner = store
            .alloc_interface_type(ObjectFlags::INTERFACE, None)
            .unwrap();
        assert!(store.initialize_interface_type_parameters(
            owner,
            vec![ordinary, this_type],
            1,
            this_type,
            CacheHashKey::new(1),
        ));
        let target = type_(&mut store, "target");

        let simple_this = store.new_simple_type_mapper(this_type, target).unwrap();
        let simple_ordinary = store.new_simple_type_mapper(ordinary, target).unwrap();
        let array_this = store
            .new_array_type_mapper(vec![this_type], vec![target])
            .unwrap();
        let array_many = store
            .new_array_type_mapper(vec![this_type, ordinary], vec![target, target])
            .unwrap();
        let to_single = store
            .new_array_to_single_type_mapper(vec![this_type], target)
            .unwrap();
        let deferred = store
            .new_deferred_type_mapper(vec![this_type], vec![move || target])
            .unwrap();
        let merged = store
            .merge_type_mappers(Some(simple_this), simple_ordinary)
            .unwrap();

        assert_eq!(store.mapper_maps_this_only(simple_this), Some(true));
        assert_eq!(store.mapper_maps_this_only(simple_ordinary), Some(false));
        assert_eq!(store.mapper_maps_this_only(array_this), Some(true));
        assert_eq!(store.mapper_maps_this_only(array_many), Some(false));
        assert_eq!(store.mapper_maps_this_only(to_single), Some(true));
        assert_eq!(store.mapper_maps_this_only(deferred), Some(true));
        assert_eq!(store.mapper_maps_this_only(merged), Some(false));
    }

    #[test]
    fn invalid_arity_and_foreign_handles_fail_atomically() {
        let mut first = CanonicalTypeMapperStore::new();
        let first_a = type_(&mut first, "first-a");
        let first_b = type_(&mut first, "first-b");
        let first_mapper = first.new_simple_type_mapper(first_a, first_b).unwrap();

        let mut second = CanonicalTypeMapperStore::new();
        let second_a = type_(&mut second, "second-a");
        let second_b = type_(&mut second, "second-b");
        let second_mapper = second.new_simple_type_mapper(second_a, second_b).unwrap();
        assert_eq!(first_a.get(), second_a.get());
        assert_eq!(first_mapper.get(), second_mapper.get());

        let before = first.mapper_len();
        assert_eq!(
            first.new_type_mapper(vec![first_a], vec![first_b, first_a]),
            None
        );
        assert_eq!(first.mapper_len(), before);
        assert_eq!(first.new_simple_type_mapper(second_a, first_b), None);
        assert_eq!(first.mapper_len(), before);
        assert_eq!(
            first.new_deferred_type_mapper(vec![second_a], vec![move || first_b]),
            None
        );
        assert_eq!(first.mapper_len(), before);
        assert_eq!(
            first.new_deferred_type_mapper(vec![first_a], Vec::<fn() -> TypeId>::new()),
            None
        );
        assert_eq!(first.mapper_len(), before);
        assert_eq!(
            first.new_backreference_mapper(&[first_a, second_a], 1, first_b),
            None
        );
        assert_eq!(first.mapper_len(), before);
        assert_eq!(
            first.new_array_to_single_type_mapper(vec![first_a], second_b),
            None
        );
        assert_eq!(first.mapper_len(), before);
        assert_eq!(
            first.merge_type_mappers(Some(first_mapper), second_mapper),
            None
        );
        assert_eq!(first.mapper_len(), before);
        assert_eq!(
            first.combine_type_mappers(Some(first_mapper), second_mapper),
            None
        );
        assert_eq!(first.mapper_len(), before);
        assert_eq!(
            first.prepend_type_mapping(first_a, first_b, Some(second_mapper)),
            None
        );
        assert_eq!(first.mapper_len(), before);
        assert_eq!(first.map_type(second_mapper, first_a), None);
        assert_eq!(first.map_type(first_mapper, second_a), None);
        assert_eq!(first.mapper_kind(second_mapper), None);
        assert_eq!(first.mapper_maps_this_only(second_mapper), None);
    }
}
