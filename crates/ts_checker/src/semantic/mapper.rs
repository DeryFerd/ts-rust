//! Store-owned canonical type mappers.
//!
//! This is the dependency-closed portion of pinned `checker/mapper.go`.
//! Simple, array, array-to-single, and merged mappers only need canonical
//! `TypeId` identity, so they can be represented and evaluated directly.
//! Composite mappers delegate recursive substitution to `instantiateType`, so
//! their graph is represented here and executed by the private `instantiate`
//! module.
//! `DeferredTypeMapper` and `FunctionTypeMapper` retain executable callbacks;
//! `InferenceTypeMapper` mutates an `InferenceContext`. Their constructors are
//! intentionally absent until those owning algorithms land. Treating any of
//! them as an identity mapper would make an unsupported semantic path look
//! successful.

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
    Merged {
        first: TypeMapperId,
        second: TypeMapperId,
    },
    #[allow(dead_code)] // Constructed by the generic signature/inference consumer.
    Composite {
        first: TypeMapperId,
        second: TypeMapperId,
    },
}

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

    const fn merged(first: TypeMapperId, second: TypeMapperId) -> Self {
        Self {
            data: TypeMapperData::Merged { first, second },
        }
    }

    #[allow(dead_code)] // Constructed by the generic signature/inference consumer.
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
            TypeMapperData::ArrayToSingle { .. } | TypeMapperData::Composite { .. } => {
                TypeMapperKind::Unknown
            }
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
    #[allow(dead_code)] // Installed ahead of the generic signature/inference consumer.
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
                if sources.len() == 1 =>
            {
                Some(sources[0])
            }
            TypeMapperData::Array { .. }
            | TypeMapperData::ArrayToSingle { .. }
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
        let merged = store
            .merge_type_mappers(Some(simple_this), simple_ordinary)
            .unwrap();

        assert_eq!(store.mapper_maps_this_only(simple_this), Some(true));
        assert_eq!(store.mapper_maps_this_only(simple_ordinary), Some(false));
        assert_eq!(store.mapper_maps_this_only(array_this), Some(true));
        assert_eq!(store.mapper_maps_this_only(array_many), Some(false));
        assert_eq!(store.mapper_maps_this_only(to_single), Some(true));
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
