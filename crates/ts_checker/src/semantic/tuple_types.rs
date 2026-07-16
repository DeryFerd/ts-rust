//! Canonical mutable tuple targets and concrete type references.
//!
//! This is the non-variadic construction slice of pinned
//! `checker.go::createTupleTypeEx`, `getTupleTargetType`, and
//! `createTupleTargetType` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Supported shapes contain
//! required elements, trailing optional elements, and at most one trailing
//! syntactic-array rest element. General variadic normalization remains at the
//! type-node boundary.

use std::collections::HashMap;

use ts_binder::{CheckFlags, EscapedName, SymbolFlags};
use ts_jsnum::Number;

use super::{
    CanonicalTypeMapperStore, TypeId,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
    bootstrap::LiteralTypeCacheError,
    declared::type_list_key,
    links::ValueSymbolLinks,
    signatures::{ElementFlags, TupleElementInfo, TupleMetadata},
    store::{
        CanonicalEmptyTupleProvenance, CanonicalTupleTargetKey, CanonicalTupleTargetProvenance,
    },
    type_records::{
        ConstrainedTypeData, LiteralValue, StructuredTypeData, TypeCacheState, TypeData,
        TypeParameterData, TypeRecord,
    },
    types::{ObjectFlags, TypeFlags},
};

const LENGTH: &str = "length";

/// Dependency-closed request for one supported tuple identity.
///
/// Element types are already resolved. In particular, an OPTIONAL element's
/// type already includes `undefined` when strict-null semantics require it.
/// REST stores the resolved element type of syntactic `...T[]`, not `T[]`.
#[derive(Clone, Copy, Debug)]
pub(super) struct CanonicalTupleTypeRequest<'a> {
    pub(super) element_types: &'a [TypeId],
    pub(super) element_infos: &'a [TupleElementInfo],
    pub(super) readonly: bool,
    /// Authoritative Array targets are required for pinned `[...T[]] -> T[]`
    /// collapse. Source/type-node integration supplies this capability later.
    pub(super) array_targets: Option<CanonicalArrayTargets>,
}

impl<'a> CanonicalTupleTypeRequest<'a> {
    pub(super) const fn new(
        element_types: &'a [TypeId],
        element_infos: &'a [TupleElementInfo],
        readonly: bool,
    ) -> Self {
        Self {
            element_types,
            element_infos,
            readonly,
            array_targets: None,
        }
    }

    #[allow(dead_code)] // Typed handoff for the next type-node integration slice.
    pub(super) const fn with_array_targets(mut self, targets: CanonicalArrayTargets) -> Self {
        self.array_targets = Some(targets);
        self
    }
}

/// Read-only projection of a validated tuple target or concrete reference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[cfg_attr(not(test), allow(dead_code))]
pub(super) struct TupleShape<'store> {
    type_: TypeId,
    target: TypeId,
    element_types: &'store [TypeId],
    element_infos: &'store [TupleElementInfo],
    min_length: usize,
    fixed_length: usize,
    combined_flags: ElementFlags,
    readonly: bool,
}

#[cfg_attr(not(test), allow(dead_code))]
impl<'store> TupleShape<'store> {
    pub(super) const fn type_(&self) -> TypeId {
        self.type_
    }

    pub(super) const fn target(&self) -> TypeId {
        self.target
    }

    pub(super) const fn element_types(&self) -> &'store [TypeId] {
        self.element_types
    }

    pub(super) const fn element_infos(&self) -> &'store [TupleElementInfo] {
        self.element_infos
    }

    pub(super) const fn min_length(&self) -> usize {
        self.min_length
    }

    pub(super) const fn fixed_length(&self) -> usize {
        self.fixed_length
    }

    pub(super) const fn combined_flags(&self) -> ElementFlags {
        self.combined_flags
    }

    pub(super) const fn is_readonly(&self) -> bool {
        self.readonly
    }
}

/// A supported tuple construction or read-only validation failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TupleTypeError {
    BootstrapUninitialized,
    ArityMismatch {
        element_types: usize,
        element_infos: usize,
    },
    InvalidElementType {
        index: usize,
        type_: TypeId,
    },
    InvalidElementInfo {
        index: usize,
    },
    UnsupportedElementFlags {
        index: usize,
        flags: ElementFlags,
    },
    UnsupportedElementOrder {
        index: usize,
    },
    ArrayRestCollapseUnavailable,
    ArrayType(ArrayTypeError),
    LengthType(LiteralTypeCacheError),
    InvalidTargetCache(TypeId),
    InvalidInstantiationCache {
        target: TypeId,
        instance: TypeId,
    },
    Capacity,
}

impl std::fmt::Display for TupleTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BootstrapUninitialized => {
                formatter.write_str("tuple type requires intrinsic checker bootstrap")
            }
            Self::ArityMismatch {
                element_types,
                element_infos,
            } => write!(
                formatter,
                "tuple request has {element_types} types but {element_infos} element descriptors"
            ),
            Self::InvalidElementType { index, type_ } => {
                write!(
                    formatter,
                    "tuple element {index} has invalid type {type_:?}"
                )
            }
            Self::InvalidElementInfo { index } => {
                write!(formatter, "tuple element {index} has a foreign label")
            }
            Self::UnsupportedElementFlags { index, flags } => write!(
                formatter,
                "tuple element {index} uses unsupported flags {flags:?}"
            ),
            Self::UnsupportedElementOrder { index } => {
                write!(
                    formatter,
                    "tuple element {index} violates supported ordering"
                )
            }
            Self::ArrayRestCollapseUnavailable => {
                formatter.write_str("sole tuple rest element requires authoritative Array targets")
            }
            Self::ArrayType(error) => error.fmt(formatter),
            Self::LengthType(error) => error.fmt(formatter),
            Self::InvalidTargetCache(target) => {
                write!(formatter, "tuple target cache entry {target:?} is invalid")
            }
            Self::InvalidInstantiationCache { target, instance } => write!(
                formatter,
                "tuple target {target:?} has invalid instantiation {instance:?}"
            ),
            Self::Capacity => formatter.write_str("tuple type capacity was exhausted"),
        }
    }
}

impl std::error::Error for TupleTypeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ArrayType(error) => Some(error),
            Self::LengthType(error) => Some(error),
            _ => None,
        }
    }
}

impl From<ArrayTypeError> for TupleTypeError {
    fn from(error: ArrayTypeError) -> Self {
        Self::ArrayType(error)
    }
}

fn length_type_error(error: LiteralTypeCacheError) -> TupleTypeError {
    match error {
        LiteralTypeCacheError::BootstrapUninitialized => TupleTypeError::BootstrapUninitialized,
        LiteralTypeCacheError::Capacity => TupleTypeError::Capacity,
        _ => TupleTypeError::LengthType(error),
    }
}

fn checked_number(value: usize) -> Result<Number, TupleTypeError> {
    let value = u32::try_from(value).map_err(|_| TupleTypeError::Capacity)?;
    Ok(Number::new(f64::from(value)))
}

fn clone_with_capacity<T: Copy>(values: &[T]) -> Result<Vec<T>, TupleTypeError> {
    let mut result = Vec::new();
    result
        .try_reserve(values.len())
        .map_err(|_| TupleTypeError::Capacity)?;
    result.extend_from_slice(values);
    Ok(result)
}

impl CanonicalTypeMapperStore {
    /// Creates or reuses one supported concrete tuple identity.
    ///
    /// Target ownership is keyed only by element flags, label declarations,
    /// and readonly state. Concrete references are keyed by the exact ordered
    /// type list in the target's instantiation cache.
    pub(super) fn create_canonical_tuple_type(
        &mut self,
        request: CanonicalTupleTypeRequest<'_>,
    ) -> Result<TypeId, TupleTypeError> {
        self.validate_tuple_request(request)?;

        if request.element_infos.is_empty()
            && !request.readonly
            && let Some(cached) = self.canonical_empty_tuple_type_cache()
        {
            self.validate_canonical_empty_tuple_type(cached)
                .map_err(|_| TupleTypeError::InvalidTargetCache(cached))?;
            return Ok(cached);
        }

        if request.element_infos.len() == 1
            && request.element_infos[0].flags() == ElementFlags::REST
        {
            let Some(targets) = request.array_targets else {
                return Err(TupleTypeError::ArrayRestCollapseUnavailable);
            };
            return self
                .create_canonical_array_type_with_targets(
                    targets,
                    request.element_types[0],
                    request.readonly,
                )
                .map_err(Into::into);
        }

        let key = CanonicalTupleTargetKey {
            element_infos: clone_with_capacity(request.element_infos)?,
            readonly: request.readonly,
        };
        if let Some(cached) = self
            .canonical_tuple_target(&key)
            .map(|provenance| provenance.target)
        {
            self.validate_canonical_tuple_target(cached)?;
            if request.element_infos.is_empty() && !request.readonly {
                self.validate_canonical_empty_tuple_type(cached)
                    .map_err(|_| TupleTypeError::InvalidTargetCache(cached))?;
            }
            return self.create_canonical_tuple_instance(cached, request.element_types);
        }

        self.create_cold_canonical_tuple_type(key, request)
    }

    fn validate_tuple_request(
        &self,
        request: CanonicalTupleTypeRequest<'_>,
    ) -> Result<(), TupleTypeError> {
        if self.intrinsic_bootstrap().is_none() {
            return Err(TupleTypeError::BootstrapUninitialized);
        }
        if request.element_types.len() != request.element_infos.len() {
            return Err(TupleTypeError::ArityMismatch {
                element_types: request.element_types.len(),
                element_infos: request.element_infos.len(),
            });
        }
        let mut saw_optional = false;
        for (index, (type_, info)) in request
            .element_types
            .iter()
            .copied()
            .zip(request.element_infos.iter().copied())
            .enumerate()
        {
            if self.type_payload(type_).is_none() {
                return Err(TupleTypeError::InvalidElementType { index, type_ });
            }
            if info
                .labeled_declaration()
                .is_some_and(|node| !self.contains_node_ref(node))
            {
                return Err(TupleTypeError::InvalidElementInfo { index });
            }
            match info.flags() {
                ElementFlags::REQUIRED if !saw_optional => {}
                ElementFlags::REQUIRED => {
                    return Err(TupleTypeError::UnsupportedElementOrder { index });
                }
                ElementFlags::OPTIONAL => saw_optional = true,
                ElementFlags::REST if index + 1 == request.element_infos.len() => {}
                ElementFlags::REST => {
                    return Err(TupleTypeError::UnsupportedElementOrder { index });
                }
                flags => {
                    return Err(TupleTypeError::UnsupportedElementFlags { index, flags });
                }
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn create_cold_canonical_tuple_type(
        &mut self,
        key: CanonicalTupleTargetKey,
        request: CanonicalTupleTypeRequest<'_>,
    ) -> Result<TypeId, TupleTypeError> {
        let metadata_infos = clone_with_capacity(request.element_infos)?;
        let metadata = TupleMetadata::new(metadata_infos, request.readonly);
        let arity = request.element_types.len();
        let concrete_instance_count = usize::from(arity != 0);
        let type_count = arity
            .checked_add(2)
            .and_then(|count| count.checked_add(concrete_instance_count))
            .ok_or(TupleTypeError::Capacity)?;
        let symbol_count = metadata
            .fixed_length()
            .checked_add(1)
            .ok_or(TupleTypeError::Capacity)?;

        let mut length_values = Vec::new();
        let variable_length = metadata.combined_flags().intersects(ElementFlags::VARIABLE);
        if !variable_length {
            let length_count = arity
                .checked_sub(metadata.min_length())
                .and_then(|count| count.checked_add(1))
                .ok_or(TupleTypeError::Capacity)?;
            length_values
                .try_reserve(length_count)
                .map_err(|_| TupleTypeError::Capacity)?;
            for value in metadata.min_length()..=arity {
                length_values.push(checked_number(value)?);
            }
        }
        let union_operations = usize::from(length_values.len() > 1);
        let reserved_type_count = length_values
            .len()
            .checked_mul(2)
            .and_then(|count| count.checked_add(union_operations * 2))
            .and_then(|count| count.checked_add(type_count))
            .ok_or(TupleTypeError::Capacity)?;
        let mut prepared = self
            .prepare_type_query_types(&[], &length_values, &[], union_operations, 0)
            .map_err(length_type_error)?;

        if !self.try_reserve_canonical_tuple_targets(1)
            || !self.try_reserve_types(reserved_type_count)
            || !self.try_reserve_checker_symbol_allocations(symbol_count, 1)
        {
            return Err(TupleTypeError::Capacity);
        }

        let mut instantiations = HashMap::new();
        instantiations
            .try_reserve(1 + concrete_instance_count)
            .map_err(|_| TupleTypeError::Capacity)?;
        let mut resolved_type_arguments = Vec::new();
        resolved_type_arguments
            .try_reserve(arity)
            .map_err(|_| TupleTypeError::Capacity)?;
        let mut all_type_parameters = Vec::new();
        all_type_parameters
            .try_reserve(arity + 1)
            .map_err(|_| TupleTypeError::Capacity)?;
        let mut provenance_type_parameters = Vec::new();
        provenance_type_parameters
            .try_reserve(arity)
            .map_err(|_| TupleTypeError::Capacity)?;
        let mut element_symbols = Vec::new();
        element_symbols
            .try_reserve(metadata.fixed_length())
            .map_err(|_| TupleTypeError::Capacity)?;
        let mut concrete_arguments = clone_with_capacity(request.element_types)?;

        let declared_members = self.alloc_symbol_table();
        for (index, info) in request.element_infos.iter().copied().enumerate() {
            let type_parameter = self
                .alloc_type_parameter(None)
                .expect("preflighted tuple type parameter is valid");
            resolved_type_arguments.push(type_parameter);
            all_type_parameters.push(type_parameter);
            provenance_type_parameters.push(type_parameter);
            if index >= metadata.fixed_length() {
                continue;
            }
            let flags = SymbolFlags::PROPERTY
                | if info.flags() == ElementFlags::OPTIONAL {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                };
            let symbol = self.alloc_transient_symbol(
                flags,
                EscapedName::source(index.to_string()),
                if request.readonly {
                    CheckFlags::READONLY
                } else {
                    CheckFlags::NONE
                },
            );
            assert!(self.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(type_parameter),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert_eq!(
                self.insert_symbol(
                    declared_members,
                    EscapedName::source(index.to_string()),
                    symbol,
                ),
                Some(None),
            );
            element_symbols.push(symbol);
        }

        let length_symbol = self.alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source(LENGTH),
            if request.readonly {
                CheckFlags::READONLY
            } else {
                CheckFlags::NONE
            },
        );
        let (length_type, length_constituents) = if variable_length {
            (
                self.intrinsic_bootstrap()
                    .expect("validated tuple bootstrap disappeared")
                    .number_type,
                Vec::new(),
            )
        } else {
            let mut constituents = Vec::new();
            constituents
                .try_reserve(length_values.len())
                .expect("preflighted tuple length vector capacity");
            for value in length_values {
                constituents.push(
                    self.regular_number_literal_type(value)
                        .expect("preflighted tuple length literal"),
                );
            }
            let length_type = if constituents.len() == 1 {
                constituents[0]
            } else {
                self.literal_union_type_prepared(&constituents, None, &mut prepared)
                    .expect("preflighted tuple length union")
            };
            (length_type, constituents)
        };
        assert!(self.set_value_symbol_links(
            length_symbol,
            ValueSymbolLinks {
                resolved_type: Some(length_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            self.insert_symbol(declared_members, EscapedName::source(LENGTH), length_symbol,),
            Some(None),
        );

        let target = self
            .alloc_tuple_type(ObjectFlags::REFERENCE | ObjectFlags::TUPLE, None, metadata)
            .expect("preflighted tuple target shell is valid");
        let this_type = self
            .alloc_type_parameter(None)
            .expect("preflighted tuple this type is valid");
        all_type_parameters.push(this_type);
        instantiations.insert(type_list_key(&resolved_type_arguments), target);
        assert!(self.initialize_tuple_target(
            target,
            resolved_type_arguments,
            all_type_parameters,
            this_type,
            declared_members,
            TypeCacheState::Allocated(instantiations),
        ));

        let result = if arity == 0 {
            target
        } else {
            let propagating_flags =
                concrete_arguments
                    .iter()
                    .fold(ObjectFlags::NONE, |flags, type_| {
                        flags
                            | self
                                .type_payload(*type_)
                                .map_or(ObjectFlags::NONE, |record| {
                                    record.object_flags() & ObjectFlags::PROPAGATING_FLAGS
                                })
                    });
            let reference = self
                .alloc_type_reference(propagating_flags, None)
                .expect("preflighted tuple reference is valid");
            assert!(self.set_object_target_and_mapper(reference, Some(target), None));
            let instance_key = type_list_key(&concrete_arguments);
            assert!(self.set_type_reference_resolution(
                reference,
                None,
                Some(std::mem::take(&mut concrete_arguments)),
            ));
            assert_eq!(
                self.insert_object_instantiation(target, instance_key, reference),
                Some(reference),
            );
            reference
        };

        assert!(self.publish_canonical_tuple_target(
            key,
            CanonicalTupleTargetProvenance {
                target,
                type_parameters: provenance_type_parameters,
                this_type,
                declared_members,
                element_symbols,
                length_symbol,
                length_type,
                length_constituents,
            },
        ));
        if arity == 0 && !request.readonly {
            assert!(
                self.publish_canonical_empty_tuple_type(CanonicalEmptyTupleProvenance {
                    type_: target,
                    this_type,
                    declared_members,
                    length_symbol,
                },)
            );
        }
        debug_assert_eq!(self.validate_canonical_tuple_target(target), Ok(()));
        Ok(result)
    }

    fn create_canonical_tuple_instance(
        &mut self,
        target: TypeId,
        element_types: &[TypeId],
    ) -> Result<TypeId, TupleTypeError> {
        if element_types.is_empty() {
            return Ok(target);
        }
        let key = type_list_key(element_types);
        let existing = match self.type_payload(target).map(TypeRecord::data) {
            Some(TypeData::Tuple(tuple)) => {
                let TypeCacheState::Allocated(instantiations) =
                    &tuple.interface.reference.object.instantiations
                else {
                    return Err(TupleTypeError::InvalidTargetCache(target));
                };
                instantiations.get(&key).copied()
            }
            _ => return Err(TupleTypeError::InvalidTargetCache(target)),
        };
        if let Some(instance) = existing {
            self.validate_canonical_tuple_instance(target, instance, element_types)?;
            return Ok(instance);
        }

        let arguments = clone_with_capacity(element_types)?;
        if !self.try_reserve_types(1) || !self.try_reserve_object_instantiations(target, 1) {
            return Err(TupleTypeError::Capacity);
        }
        let propagating_flags = element_types
            .iter()
            .fold(ObjectFlags::NONE, |flags, type_| {
                flags
                    | self
                        .type_payload(*type_)
                        .map_or(ObjectFlags::NONE, |record| {
                            record.object_flags() & ObjectFlags::PROPAGATING_FLAGS
                        })
            });
        let reference = self
            .alloc_type_reference(propagating_flags, None)
            .expect("validated tuple instance arguments are valid");
        assert!(self.set_object_target_and_mapper(reference, Some(target), None));
        assert!(self.set_type_reference_resolution(reference, None, Some(arguments)));
        assert_eq!(
            self.insert_object_instantiation(target, key, reference),
            Some(reference),
        );
        debug_assert_eq!(
            self.validate_canonical_tuple_instance(target, reference, element_types),
            Ok(()),
        );
        Ok(reference)
    }

    /// Extracts a validated tuple shape without allocating or repairing any
    /// cache entry. Canonical arrays produced by sole-rest collapse return
    /// `Ok(None)` because they are not tuples.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(super) fn canonical_tuple_shape(
        &self,
        type_: TypeId,
    ) -> Result<Option<TupleShape<'_>>, TupleTypeError> {
        let Some(record) = self.type_payload(type_) else {
            return Ok(None);
        };
        let target = match record.data() {
            TypeData::Tuple(_) => type_,
            TypeData::TypeReference(reference) => {
                let Some(target) = reference.object.target else {
                    return Ok(None);
                };
                if !matches!(
                    self.type_payload(target).map(TypeRecord::data),
                    Some(TypeData::Tuple(_))
                ) {
                    return Ok(None);
                }
                target
            }
            _ => return Ok(None),
        };
        self.validate_canonical_tuple_target(target)?;
        let target_record = self
            .type_payload(target)
            .ok_or(TupleTypeError::InvalidTargetCache(target))?;
        let TypeData::Tuple(tuple) = target_record.data() else {
            return Err(TupleTypeError::InvalidTargetCache(target));
        };
        let element_types = if type_ == target {
            tuple
                .interface
                .reference
                .resolved_type_arguments
                .as_deref()
                .ok_or(TupleTypeError::InvalidTargetCache(target))?
        } else {
            let TypeData::TypeReference(reference) = record.data() else {
                unreachable!("non-target tuple identity was validated as a reference")
            };
            let arguments = reference.resolved_type_arguments.as_deref().ok_or(
                TupleTypeError::InvalidInstantiationCache {
                    target,
                    instance: type_,
                },
            )?;
            self.validate_canonical_tuple_instance(target, type_, arguments)?;
            arguments
        };
        Ok(Some(TupleShape {
            type_,
            target,
            element_types,
            element_infos: tuple.metadata.element_infos(),
            min_length: tuple.metadata.min_length(),
            fixed_length: tuple.metadata.fixed_length(),
            combined_flags: tuple.metadata.combined_flags(),
            readonly: tuple.metadata.is_readonly(),
        }))
    }
}

impl CanonicalTypeMapperStore {
    #[allow(clippy::too_many_lines)]
    fn validate_canonical_tuple_target(&self, target: TypeId) -> Result<(), TupleTypeError> {
        let invalid = || TupleTypeError::InvalidTargetCache(target);
        let Some((key, provenance)) = self.canonical_tuple_target_for_type(target) else {
            return Err(invalid());
        };
        if provenance.target != target
            || key.element_infos.iter().any(|info| {
                info.labeled_declaration()
                    .is_some_and(|node| !self.contains_node_ref(node))
            })
        {
            return Err(invalid());
        }
        let record = self.type_payload(target).ok_or_else(invalid)?;
        let TypeData::Tuple(tuple) = record.data() else {
            return Err(invalid());
        };
        let interface = &tuple.interface;
        let reference = &interface.reference;
        let object = &reference.object;
        let metadata = &tuple.metadata;

        let mut expected_minimum = 0usize;
        let mut expected_fixed = key.element_infos.len();
        let mut expected_combined = ElementFlags::NONE;
        for (index, info) in key.element_infos.iter().enumerate() {
            let flags = info.flags();
            if flags.intersects(ElementFlags::REQUIRED | ElementFlags::VARIADIC) {
                expected_minimum += 1;
            }
            expected_combined |= flags;
            if expected_fixed == key.element_infos.len()
                && expected_combined.intersects(ElementFlags::VARIABLE)
            {
                expected_fixed = index;
            }
        }

        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != (ObjectFlags::REFERENCE | ObjectFlags::TUPLE)
            || record.symbol().is_some()
            || record.alias().is_some()
            || object.structured != StructuredTypeData::default()
            || object.target != Some(target)
            || object.mapper.is_some()
            || reference.node.is_some()
            || reference.resolved_type_arguments.as_deref()
                != Some(provenance.type_parameters.as_slice())
            || interface.outer_type_parameter_count != 0
            || interface.base_types_resolved
            || interface.resolved_base_constructor_type.is_some()
            || interface.resolved_base_types.is_some()
            || !interface.declared_members_resolved
            || interface.declared_members != Some(provenance.declared_members)
            || interface.declared_call_signatures.is_some()
            || interface.declared_construct_signatures.is_some()
            || interface.declared_index_infos.is_some()
            || metadata.element_infos() != key.element_infos.as_slice()
            || metadata.min_length() != expected_minimum
            || metadata.fixed_length() != expected_fixed
            || metadata.combined_flags() != expected_combined
            || metadata.is_readonly() != key.readonly
            || provenance.type_parameters.len() != key.element_infos.len()
            || provenance.element_symbols.len() != expected_fixed
        {
            return Err(invalid());
        }

        let Some(all_type_parameters) = interface.all_type_parameters.as_deref() else {
            return Err(invalid());
        };
        if all_type_parameters.len() != provenance.type_parameters.len() + 1
            || &all_type_parameters[..provenance.type_parameters.len()]
                != provenance.type_parameters.as_slice()
            || all_type_parameters.last().copied() != Some(provenance.this_type)
            || interface.this_type != Some(provenance.this_type)
        {
            return Err(invalid());
        }
        for parameter in &provenance.type_parameters {
            let Some(parameter_record) = self.type_payload(*parameter) else {
                return Err(invalid());
            };
            if parameter_record.flags() != TypeFlags::TYPE_PARAMETER
                || !parameter_record.object_flags().is_empty()
                || parameter_record.symbol().is_some()
                || parameter_record.alias().is_some()
                || !matches!(
                    parameter_record.data(),
                    TypeData::TypeParameter(data) if data == &TypeParameterData::default()
                )
            {
                return Err(invalid());
            }
        }
        let this_record = self
            .type_payload(provenance.this_type)
            .ok_or_else(invalid)?;
        if this_record.flags() != TypeFlags::TYPE_PARAMETER
            || !this_record.object_flags().is_empty()
            || this_record.symbol().is_some()
            || this_record.alias().is_some()
            || !matches!(
                this_record.data(),
                TypeData::TypeParameter(data)
                    if data == &(TypeParameterData {
                        constrained: ConstrainedTypeData::default(),
                        constraint: Some(target),
                        target: None,
                        mapper: None,
                        is_this_type: true,
                        resolved_default_type: None,
                    })
            )
        {
            return Err(invalid());
        }

        let members = self
            .symbol_table(provenance.declared_members)
            .ok_or_else(invalid)?;
        if members.len() != expected_fixed + 1 {
            return Err(invalid());
        }
        for (index, symbol) in provenance.element_symbols.iter().copied().enumerate() {
            let name = index.to_string();
            if members.get_source(&name) != Some(symbol)
                || !self.valid_tuple_property_symbol(
                    symbol,
                    &name,
                    SymbolFlags::PROPERTY
                        | if key.element_infos[index].flags() == ElementFlags::OPTIONAL {
                            SymbolFlags::OPTIONAL
                        } else {
                            SymbolFlags::NONE
                        },
                    if key.readonly {
                        CheckFlags::READONLY
                    } else {
                        CheckFlags::NONE
                    },
                    provenance.type_parameters[index],
                )
            {
                return Err(invalid());
            }
        }
        if members.get_source(LENGTH) != Some(provenance.length_symbol)
            || !self.valid_tuple_property_symbol(
                provenance.length_symbol,
                LENGTH,
                SymbolFlags::PROPERTY,
                if key.readonly {
                    CheckFlags::READONLY
                } else {
                    CheckFlags::NONE
                },
                provenance.length_type,
            )
            || !self.valid_tuple_length_type(
                metadata,
                provenance.length_type,
                &provenance.length_constituents,
            )
        {
            return Err(invalid());
        }

        let TypeCacheState::Allocated(instantiations) = &object.instantiations else {
            return Err(invalid());
        };
        let identity_key = type_list_key(&provenance.type_parameters);
        if instantiations.get(&identity_key) != Some(&target) {
            return Err(invalid());
        }
        for (key, instance) in instantiations {
            if *instance == target {
                if *key != identity_key {
                    return Err(invalid());
                }
                continue;
            }
            let Some(TypeData::TypeReference(reference)) =
                self.type_payload(*instance).map(TypeRecord::data)
            else {
                return Err(TupleTypeError::InvalidInstantiationCache {
                    target,
                    instance: *instance,
                });
            };
            let Some(arguments) = reference.resolved_type_arguments.as_deref() else {
                return Err(TupleTypeError::InvalidInstantiationCache {
                    target,
                    instance: *instance,
                });
            };
            if *key != type_list_key(arguments) {
                return Err(TupleTypeError::InvalidInstantiationCache {
                    target,
                    instance: *instance,
                });
            }
            self.validate_canonical_tuple_instance(target, *instance, arguments)?;
        }
        Ok(())
    }

    fn valid_tuple_property_symbol(
        &self,
        symbol: ts_binder::SemanticSymbolId,
        name: &str,
        flags: SymbolFlags,
        check_flags: CheckFlags,
        resolved_type: TypeId,
    ) -> bool {
        let Some(record) = self.symbol(symbol) else {
            return false;
        };
        self.get_merged_symbol(symbol) == Some(symbol)
            && record.flags() == (flags | SymbolFlags::TRANSIENT)
            && record.check_flags() == check_flags
            && record.name().as_bytes() == name.as_bytes()
            && record.declarations().is_none()
            && record.value_declaration().is_none()
            && record.members().is_none()
            && record.exports().is_none()
            && record.parent().is_none()
            && record.export_symbol().is_none()
            && self.value_symbol_links(symbol)
                == Some(&ValueSymbolLinks {
                    resolved_type: Some(resolved_type),
                    ..ValueSymbolLinks::default()
                })
    }

    fn valid_tuple_length_type(
        &self,
        metadata: &TupleMetadata,
        length_type: TypeId,
        constituents: &[TypeId],
    ) -> bool {
        let Some(bootstrap) = self.intrinsic_bootstrap() else {
            return false;
        };
        if self
            .validate_cached_union_result(length_type, None)
            .is_err()
        {
            return false;
        }
        if metadata.combined_flags().intersects(ElementFlags::VARIABLE) {
            return constituents.is_empty() && length_type == bootstrap.number_type;
        }
        let arity = metadata.element_infos().len();
        let expected_count = arity - metadata.min_length() + 1;
        if constituents.len() != expected_count {
            return false;
        }
        for (offset, constituent) in constituents.iter().copied().enumerate() {
            let Ok(value) = checked_number(metadata.min_length() + offset) else {
                return false;
            };
            if bootstrap.cached_number_literal_type(value) != Some(constituent)
                || !matches!(
                    self.type_payload(constituent).map(TypeRecord::data),
                    Some(TypeData::Literal(data))
                        if data.value == LiteralValue::Number(value)
                            && data.regular_type == constituent
                )
            {
                return false;
            }
        }
        if constituents.len() == 1 {
            return length_type == constituents[0];
        }
        matches!(
            self.type_payload(length_type).map(TypeRecord::data),
            Some(TypeData::Union(data))
                if data.union.types.len() == constituents.len()
                    && constituents
                        .iter()
                        .all(|constituent| data.union.types.contains(constituent))
        )
    }

    fn validate_canonical_tuple_instance(
        &self,
        target: TypeId,
        instance: TypeId,
        expected_arguments: &[TypeId],
    ) -> Result<(), TupleTypeError> {
        let invalid = || TupleTypeError::InvalidInstantiationCache { target, instance };
        let target_record = self.type_payload(target).ok_or_else(invalid)?;
        let TypeData::Tuple(tuple) = target_record.data() else {
            return Err(invalid());
        };
        if tuple.metadata.element_infos().len() != expected_arguments.len()
            || expected_arguments
                .iter()
                .any(|argument| self.type_payload(*argument).is_none())
        {
            return Err(invalid());
        }
        let record = self.type_payload(instance).ok_or_else(invalid)?;
        let TypeData::TypeReference(reference) = record.data() else {
            return Err(invalid());
        };
        let propagating_flags =
            expected_arguments
                .iter()
                .fold(ObjectFlags::NONE, |flags, argument| {
                    flags
                        | self
                            .type_payload(*argument)
                            .map_or(ObjectFlags::NONE, |record| {
                                record.object_flags() & ObjectFlags::PROPAGATING_FLAGS
                            })
                });
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != (ObjectFlags::REFERENCE | propagating_flags)
            || record.symbol().is_some()
            || record.alias().is_some()
            || reference.object.structured != StructuredTypeData::default()
            || reference.object.target != Some(target)
            || reference.object.mapper.is_some()
            || reference.object.instantiations != TypeCacheState::Unallocated
            || reference.node.is_some()
            || reference.resolved_type_arguments.as_deref() != Some(expected_arguments)
        {
            return Err(invalid());
        }
        let TypeCacheState::Allocated(instantiations) =
            &tuple.interface.reference.object.instantiations
        else {
            return Err(invalid());
        };
        if instantiations.get(&type_list_key(expected_arguments)) != Some(&instance) {
            return Err(invalid());
        }
        Ok(())
    }

    #[cfg(test)]
    fn reserve_tuple_construction_for_test(
        &mut self,
        additional_types: usize,
        additional_symbols: usize,
        additional_tables: usize,
        additional_targets: usize,
    ) -> bool {
        self.try_reserve_canonical_tuple_targets(additional_targets)
            && self.try_reserve_types(additional_types)
            && self.try_reserve_checker_symbol_allocations(additional_symbols, additional_tables)
    }
}

/// A mutable empty-tuple request rejected before publishing a new cache entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EmptyTupleTypeError {
    BootstrapUninitialized,
    InvalidCache(TypeId),
    Capacity,
}

impl std::fmt::Display for EmptyTupleTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BootstrapUninitialized => {
                formatter.write_str("empty tuple type requires intrinsic checker bootstrap")
            }
            Self::InvalidCache(type_) => {
                write!(formatter, "empty tuple cache entry {type_:?} is invalid")
            }
            Self::Capacity => formatter.write_str("empty tuple type capacity was exhausted"),
        }
    }
}

impl std::error::Error for EmptyTupleTypeError {}

impl CanonicalTypeMapperStore {
    /// Creates or reuses the exact mutable `[]` target returned by pinned
    /// `createTupleTypeEx([])`.
    ///
    /// A warm request validates the complete recursive graph before returning
    /// its stable identity. A poisoned or foreign cache entry is never
    /// replaced implicitly.
    pub(super) fn create_canonical_empty_tuple_type(
        &mut self,
    ) -> Result<TypeId, EmptyTupleTypeError> {
        if let Some(cached) = self.canonical_empty_tuple_type_cache() {
            self.validate_canonical_empty_tuple_type(cached)?;
            return Ok(cached);
        }
        let tuple = self
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&[], &[], false))
            .map_err(|error| match error {
                TupleTypeError::BootstrapUninitialized => {
                    EmptyTupleTypeError::BootstrapUninitialized
                }
                TupleTypeError::Capacity => EmptyTupleTypeError::Capacity,
                TupleTypeError::InvalidTargetCache(type_)
                | TupleTypeError::InvalidInstantiationCache { target: type_, .. } => {
                    EmptyTupleTypeError::InvalidCache(type_)
                }
                _ => EmptyTupleTypeError::InvalidCache(
                    self.canonical_empty_tuple_type_cache().unwrap_or_else(|| {
                        self.intrinsic_bootstrap()
                            .expect("bootstrap failure was handled above")
                            .zero_type
                    }),
                ),
            })?;
        self.validate_canonical_empty_tuple_type(tuple)?;
        Ok(tuple)
    }

    /// Validates one identity as the store's exact cached mutable empty tuple.
    ///
    /// This read-only boundary is shared by warm construction and canonical
    /// display, so neither consumer can accidentally accept a tuple-shaped
    /// forgery without cache ownership.
    pub(super) fn validate_canonical_empty_tuple_type(
        &self,
        type_: TypeId,
    ) -> Result<(), EmptyTupleTypeError> {
        let invalid = || EmptyTupleTypeError::InvalidCache(type_);
        let Some(provenance) = self.canonical_empty_tuple_provenance() else {
            return Err(invalid());
        };
        if provenance.type_ != type_ {
            return Err(invalid());
        }
        let empty_key = CanonicalTupleTargetKey {
            element_infos: Vec::new(),
            readonly: false,
        };
        if self
            .canonical_tuple_target(&empty_key)
            .is_none_or(|cached| cached.target != type_)
            || self.validate_canonical_tuple_target(type_).is_err()
        {
            return Err(invalid());
        }
        let zero_type = self
            .intrinsic_bootstrap()
            .ok_or(EmptyTupleTypeError::BootstrapUninitialized)?
            .zero_type;
        let record = self.type_payload(type_).ok_or_else(invalid)?;
        let TypeData::Tuple(tuple) = record.data() else {
            return Err(invalid());
        };
        let interface = &tuple.interface;
        let reference = &interface.reference;
        let object = &reference.object;
        if record.flags() != TypeFlags::OBJECT
            || record.object_flags() != (ObjectFlags::REFERENCE | ObjectFlags::TUPLE)
            || record.symbol().is_some()
            || record.alias().is_some()
            || object.structured != StructuredTypeData::default()
            || object.target != Some(type_)
            || object.mapper.is_some()
            || reference.node.is_some()
            || reference.resolved_type_arguments.as_deref() != Some(&[])
            || interface.outer_type_parameter_count != 0
            || interface.base_types_resolved
            || interface.resolved_base_constructor_type.is_some()
            || interface.resolved_base_types.is_some()
            || !interface.declared_members_resolved
            || interface.declared_call_signatures.is_some()
            || interface.declared_construct_signatures.is_some()
            || interface.declared_index_infos.is_some()
            || !tuple.metadata.element_infos().is_empty()
            || tuple.metadata.min_length() != 0
            || tuple.metadata.fixed_length() != 0
            || tuple.metadata.combined_flags() != ElementFlags::NONE
            || tuple.metadata.is_readonly()
        {
            return Err(invalid());
        }

        let Some([this_type]) = interface.all_type_parameters.as_deref() else {
            return Err(invalid());
        };
        if interface.this_type != Some(*this_type) || provenance.this_type != *this_type {
            return Err(invalid());
        }
        let TypeCacheState::Allocated(instantiations) = &object.instantiations else {
            return Err(invalid());
        };
        if instantiations.len() != 1 || instantiations.get(&type_list_key(&[])) != Some(&type_) {
            return Err(invalid());
        }
        let this_record = self.type_payload(*this_type).ok_or_else(invalid)?;
        let TypeData::TypeParameter(this_data) = this_record.data() else {
            return Err(invalid());
        };
        if this_record.flags() != TypeFlags::TYPE_PARAMETER
            || !this_record.object_flags().is_empty()
            || this_record.symbol().is_some()
            || this_record.alias().is_some()
            || this_data
                != &(TypeParameterData {
                    constrained: ConstrainedTypeData::default(),
                    constraint: Some(type_),
                    target: None,
                    mapper: None,
                    is_this_type: true,
                    resolved_default_type: None,
                })
        {
            return Err(invalid());
        }

        let declared_members = interface.declared_members.ok_or_else(invalid)?;
        if declared_members != provenance.declared_members {
            return Err(invalid());
        }
        let members = self.symbol_table(declared_members).ok_or_else(invalid)?;
        let length = members.get_source(LENGTH).ok_or_else(invalid)?;
        if members.len() != 1 || length != provenance.length_symbol {
            return Err(invalid());
        }
        let length_symbol = self.symbol(length).ok_or_else(invalid)?;
        if self.get_merged_symbol(length) != Some(length)
            || length_symbol.flags() != (SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
            || length_symbol.check_flags() != CheckFlags::NONE
            || length_symbol.name().as_bytes() != LENGTH.as_bytes()
            || length_symbol.declarations().is_some()
            || length_symbol.value_declaration().is_some()
            || length_symbol.members().is_some()
            || length_symbol.exports().is_some()
            || length_symbol.parent().is_some()
            || length_symbol.export_symbol().is_some()
            || self.value_symbol_links(length)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(zero_type),
                    ..ValueSymbolLinks::default()
                })
        {
            return Err(invalid());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, TypeDisplayUnavailable, bootstrap::UnionReduction,
        formatter::type_to_string, type_records::TypeRecord,
    };
    use crate::semantic::{SemanticStore, mapper::TypeMapper};
    use ts_ast::{FileId, NodeRef, SyntaxKind};
    use ts_binder::AstScope;
    use ts_parser::parse_source_file;

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    fn initialized() -> TestStore {
        let mut store = TestStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn observable_state(
        store: &TestStore,
    ) -> (usize, usize, usize, [usize; 26], Option<TypeId>, usize) {
        (
            store.type_len(),
            store.symbol_store().checker_created_symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
            store.canonical_empty_tuple_type_cache(),
            store.canonical_tuple_target_len(),
        )
    }

    #[test]
    fn mutable_empty_tuple_graph_is_exact_stable_and_displayable() {
        let mut store = initialized();
        let before = observable_state(&store);
        let tuple = store.create_canonical_empty_tuple_type().unwrap();
        assert_eq!(store.validate_canonical_empty_tuple_type(tuple), Ok(()));
        assert_eq!(type_to_string(&store, tuple).unwrap(), "[]");

        let cold = observable_state(&store);
        assert_eq!(
            cold.0,
            before.0 + 2,
            "tuple target plus synthetic this type"
        );
        assert_eq!(cold.1, before.1 + 1, "synthetic length property");
        assert_eq!(cold.2, before.2 + 1, "declared member table");
        assert_eq!(cold.3[10], before.3[10] + 1, "length value links");
        assert_eq!(cold.4, Some(tuple));
        assert_eq!(cold.5, before.5 + 1, "general tuple target cache");

        assert_eq!(store.create_canonical_empty_tuple_type(), Ok(tuple));
        assert_eq!(observable_state(&store), cold);
    }

    #[test]
    fn readonly_and_mutable_empty_tuples_have_distinct_order_independent_targets() {
        for readonly_first in [false, true] {
            let mut store = initialized();
            let readonly = || CanonicalTupleTypeRequest::new(&[], &[], true);
            let mutable = || CanonicalTupleTypeRequest::new(&[], &[], false);

            let (mutable_tuple, readonly_tuple) = if readonly_first {
                let readonly_tuple = store.create_canonical_tuple_type(readonly()).unwrap();
                let mutable_tuple = store.create_canonical_tuple_type(mutable()).unwrap();
                (mutable_tuple, readonly_tuple)
            } else {
                let mutable_tuple = store.create_canonical_tuple_type(mutable()).unwrap();
                let readonly_tuple = store.create_canonical_tuple_type(readonly()).unwrap();
                (mutable_tuple, readonly_tuple)
            };

            assert_ne!(mutable_tuple, readonly_tuple);
            assert_eq!(store.canonical_empty_tuple_type_cache(), Some(mutable_tuple));
            assert_eq!(store.create_canonical_empty_tuple_type(), Ok(mutable_tuple));
            assert_eq!(store.create_canonical_tuple_type(mutable()), Ok(mutable_tuple));
            assert_eq!(store.create_canonical_tuple_type(readonly()), Ok(readonly_tuple));
            assert_eq!(type_to_string(&store, mutable_tuple).unwrap(), "[]");
            assert_eq!(type_to_string(&store, readonly_tuple).unwrap(), "readonly []");
        }
    }

    #[test]
    fn bootstrap_foreign_cache_and_graph_poison_are_rejected_read_only() {
        let mut pristine = TestStore::new();
        let pristine_state = observable_state(&pristine);
        assert_eq!(
            pristine.create_canonical_empty_tuple_type(),
            Err(EmptyTupleTypeError::BootstrapUninitialized),
        );
        assert_eq!(observable_state(&pristine), pristine_state);

        let mut replaced = initialized();
        let replaced_tuple = replaced.create_canonical_empty_tuple_type().unwrap();
        let zero = replaced.intrinsic_bootstrap().unwrap().zero_type;
        let replacement_members = replaced.alloc_symbol_table();
        let replacement_length = replaced.alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source(LENGTH),
            CheckFlags::NONE,
        );
        assert!(replaced.set_value_symbol_links(
            replacement_length,
            ValueSymbolLinks {
                resolved_type: Some(zero),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            replaced.insert_symbol(
                replacement_members,
                EscapedName::source(LENGTH),
                replacement_length,
            ),
            Some(None),
        );
        assert!(replaced.set_interface_declared_members(
            replaced_tuple,
            true,
            Some(replacement_members),
            None,
            None,
            None,
        ));
        assert_eq!(
            replaced.validate_canonical_empty_tuple_type(replaced_tuple),
            Err(EmptyTupleTypeError::InvalidCache(replaced_tuple)),
        );

        let mut store = initialized();
        let tuple = store.create_canonical_empty_tuple_type().unwrap();
        let this_type = match store.type_payload(tuple).unwrap().data() {
            TypeData::Tuple(data) => data.interface.this_type.unwrap(),
            _ => unreachable!(),
        };
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        assert!(store.set_resolved_base_constraint(this_type, Some(number)));
        let poisoned_graph = observable_state(&store);
        assert_eq!(
            store.create_canonical_empty_tuple_type(),
            Err(EmptyTupleTypeError::InvalidCache(tuple)),
        );
        assert_eq!(observable_state(&store), poisoned_graph);
        assert_eq!(
            type_to_string(&store, tuple),
            Err(TypeDisplayUnavailable::EmptyTupleType(
                EmptyTupleTypeError::InvalidCache(tuple),
            )),
        );

        let mut foreign = initialized();
        let foreign_tuple = foreign.create_canonical_empty_tuple_type().unwrap();
        assert_eq!(
            store.replace_canonical_empty_tuple_type_for_test(Some(foreign_tuple)),
            Some(tuple),
        );
        let foreign_cache = observable_state(&store);
        assert_eq!(
            store.create_canonical_empty_tuple_type(),
            Err(EmptyTupleTypeError::InvalidCache(foreign_tuple)),
        );
        assert_eq!(observable_state(&store), foreign_cache);
    }

    fn element_info(
        store: &TestStore,
        flags: ElementFlags,
        label: Option<NodeRef>,
    ) -> TupleElementInfo {
        store.create_tuple_element_info(flags, label).unwrap()
    }

    fn labeled_nodes(store: &mut TestStore, file: u32) -> (NodeRef, NodeRef) {
        let parsed = parse_source_file("type A = [value: string]; type B = [value: string];");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(file);
        let scope = AstScope::new(file, &parsed.arena);
        let mut labels = parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::NamedTupleMember)
            .map(|(node, _)| scope.node_ref(node).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(labels.len(), 2);
        assert!(store.register_ast_scope(scope));
        (labels.remove(0), labels.remove(0))
    }

    #[test]
    fn every_supported_flag_sequence_derives_exact_metadata() {
        let mut store = initialized();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let cases = [
            (Vec::new(), 0, 0, ElementFlags::NONE),
            (vec![ElementFlags::REQUIRED], 1, 1, ElementFlags::REQUIRED),
            (vec![ElementFlags::OPTIONAL], 0, 1, ElementFlags::OPTIONAL),
            (
                vec![ElementFlags::REQUIRED, ElementFlags::REQUIRED],
                2,
                2,
                ElementFlags::REQUIRED,
            ),
            (
                vec![ElementFlags::REQUIRED, ElementFlags::OPTIONAL],
                1,
                2,
                ElementFlags::REQUIRED | ElementFlags::OPTIONAL,
            ),
            (
                vec![ElementFlags::OPTIONAL, ElementFlags::OPTIONAL],
                0,
                2,
                ElementFlags::OPTIONAL,
            ),
            (
                vec![ElementFlags::REQUIRED, ElementFlags::REST],
                1,
                1,
                ElementFlags::REQUIRED | ElementFlags::REST,
            ),
            (
                vec![ElementFlags::OPTIONAL, ElementFlags::REST],
                0,
                1,
                ElementFlags::OPTIONAL | ElementFlags::REST,
            ),
            (
                vec![
                    ElementFlags::REQUIRED,
                    ElementFlags::OPTIONAL,
                    ElementFlags::REST,
                ],
                1,
                2,
                ElementFlags::REQUIRED | ElementFlags::OPTIONAL | ElementFlags::REST,
            ),
            (
                vec![
                    ElementFlags::REQUIRED,
                    ElementFlags::REQUIRED,
                    ElementFlags::OPTIONAL,
                    ElementFlags::OPTIONAL,
                    ElementFlags::REST,
                ],
                2,
                4,
                ElementFlags::REQUIRED | ElementFlags::OPTIONAL | ElementFlags::REST,
            ),
        ];
        let before_targets = store.canonical_tuple_target_len();

        for (flags, min_length, fixed_length, combined_flags) in &cases {
            let infos = flags
                .iter()
                .copied()
                .map(|flags| element_info(&store, flags, None))
                .collect::<Vec<_>>();
            let types = vec![number; flags.len()];
            let tuple = store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &infos, false))
                .unwrap();
            let shape = store.canonical_tuple_shape(tuple).unwrap().unwrap();
            assert_eq!(shape.element_types(), types.as_slice());
            assert_eq!(shape.element_infos(), infos.as_slice());
            assert_eq!(shape.min_length(), *min_length);
            assert_eq!(shape.fixed_length(), *fixed_length);
            assert_eq!(shape.combined_flags(), *combined_flags);
            assert_eq!(
                store.validate_canonical_tuple_target(shape.target()),
                Ok(())
            );
        }

        assert_eq!(
            store.canonical_tuple_target_len(),
            before_targets + cases.len(),
        );
    }

    #[test]
    fn required_optional_and_rest_shapes_own_exact_targets_and_instances() {
        let mut store = initialized();
        let (string, number, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.undefined_type,
            )
        };
        let optional_number = store
            .expression_union_type(&[number, undefined], UnionReduction::Literal)
            .unwrap();
        let infos = [
            element_info(&store, ElementFlags::REQUIRED, None),
            element_info(&store, ElementFlags::OPTIONAL, None),
        ];
        let types = [string, optional_number];
        let tuple = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &infos, false))
            .unwrap();
        let shape = store.canonical_tuple_shape(tuple).unwrap().unwrap();
        let target = shape.target();
        assert_ne!(tuple, target);
        assert_eq!(shape.type_(), tuple);
        assert_eq!(shape.element_types(), types);
        assert_eq!(shape.element_infos(), infos);
        assert_eq!(shape.min_length(), 1);
        assert_eq!(shape.fixed_length(), 2);
        assert_eq!(
            shape.combined_flags(),
            ElementFlags::REQUIRED | ElementFlags::OPTIONAL
        );
        assert!(!shape.is_readonly());
        assert_eq!(store.validate_canonical_tuple_target(target), Ok(()));
        assert_eq!(
            store.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &types, &infos, false,
            )),
            Ok(tuple),
        );

        let unresolved_optional_types = [string, number];
        let unresolved_optional = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &unresolved_optional_types,
                &infos,
                false,
            ))
            .unwrap();
        assert_ne!(unresolved_optional, tuple);
        let unresolved_shape = store
            .canonical_tuple_shape(unresolved_optional)
            .unwrap()
            .unwrap();
        assert_eq!(unresolved_shape.target(), target);
        assert_eq!(unresolved_shape.element_types(), unresolved_optional_types);
        assert_eq!(
            unresolved_shape.element_types()[1],
            number,
            "construction consumes optional element types exactly and never adds undefined",
        );

        let target_shape = store.canonical_tuple_shape(target).unwrap().unwrap();
        assert_eq!(target_shape.type_(), target);
        assert_ne!(target_shape.element_types(), types);
        assert_eq!(target_shape.element_types().len(), 2);
        let (_, provenance) = store.canonical_tuple_target_for_type(target).unwrap();
        assert_eq!(provenance.length_constituents.len(), 2);
        assert_ne!(provenance.length_type, provenance.length_constituents[0]);
        let members = store.symbol_table(provenance.declared_members).unwrap();
        let optional_symbol = members.get_source("1").unwrap();
        assert!(
            store
                .symbol(optional_symbol)
                .unwrap()
                .flags()
                .contains(SymbolFlags::OPTIONAL)
        );

        let rest_infos = [
            element_info(&store, ElementFlags::REQUIRED, None),
            element_info(&store, ElementFlags::REST, None),
        ];
        let rest_types = [string, number];
        let rest = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &rest_types,
                &rest_infos,
                false,
            ))
            .unwrap();
        let rest_shape = store.canonical_tuple_shape(rest).unwrap().unwrap();
        assert_eq!(rest_shape.min_length(), 1);
        assert_eq!(rest_shape.fixed_length(), 1);
        assert_eq!(
            rest_shape.combined_flags(),
            ElementFlags::REQUIRED | ElementFlags::REST
        );
        let (_, rest_provenance) = store
            .canonical_tuple_target_for_type(rest_shape.target())
            .unwrap();
        assert!(rest_provenance.length_constituents.is_empty());
        assert_eq!(rest_provenance.length_type, number);
        assert_eq!(
            store
                .symbol_table(rest_provenance.declared_members)
                .unwrap()
                .len(),
            2,
            "only index zero and length are declared after a variable element",
        );
    }

    #[test]
    fn labels_and_readonly_state_participate_in_target_identity() {
        let mut store = initialized();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let (first_label, second_label) = labeled_nodes(&mut store, 931);
        let first_info = [element_info(
            &store,
            ElementFlags::REQUIRED,
            Some(first_label),
        )];
        let second_info = [element_info(
            &store,
            ElementFlags::REQUIRED,
            Some(second_label),
        )];
        let types = [string];

        let first = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &first_info, false))
            .unwrap();
        let first_target = store
            .canonical_tuple_shape(first)
            .unwrap()
            .unwrap()
            .target();
        assert_eq!(
            store.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &types,
                &first_info,
                false,
            )),
            Ok(first),
        );

        let second = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &types,
                &second_info,
                false,
            ))
            .unwrap();
        let second_target = store
            .canonical_tuple_shape(second)
            .unwrap()
            .unwrap()
            .target();
        assert_ne!(first_target, second_target);

        let readonly = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &first_info, true))
            .unwrap();
        let readonly_shape = store.canonical_tuple_shape(readonly).unwrap().unwrap();
        assert!(readonly_shape.is_readonly());
        assert_ne!(readonly_shape.target(), first_target);
        let (_, provenance) = store
            .canonical_tuple_target_for_type(readonly_shape.target())
            .unwrap();
        for symbol in provenance
            .element_symbols
            .iter()
            .copied()
            .chain(std::iter::once(provenance.length_symbol))
        {
            assert_eq!(
                store.symbol(symbol).unwrap().check_flags(),
                CheckFlags::READONLY,
            );
        }
    }

    #[test]
    fn sole_rest_requires_the_authoritative_array_collapse_capability() {
        let mut store = initialized();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let infos = [element_info(&store, ElementFlags::REST, None)];
        let before = observable_state(&store);
        assert_eq!(
            store.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number],
                &infos,
                false,
            )),
            Err(TupleTypeError::ArrayRestCollapseUnavailable),
        );
        assert_eq!(observable_state(&store), before);
    }

    #[test]
    fn invalid_foreign_and_capacity_requests_are_failure_atomic() {
        let mut store = initialized();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let required = element_info(&store, ElementFlags::REQUIRED, None);
        let optional = element_info(&store, ElementFlags::OPTIONAL, None);
        let rest = element_info(&store, ElementFlags::REST, None);
        let variadic = element_info(&store, ElementFlags::VARIADIC, None);
        let before = observable_state(&store);

        assert!(matches!(
            store.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string],
                &[required, optional],
                false,
            )),
            Err(TupleTypeError::ArityMismatch { .. })
        ));
        assert_eq!(observable_state(&store), before);
        assert_eq!(
            store.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string, number],
                &[optional, required],
                false,
            )),
            Err(TupleTypeError::UnsupportedElementOrder { index: 1 }),
        );
        assert_eq!(observable_state(&store), before);
        assert_eq!(
            store.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string, number],
                &[rest, required],
                false,
            )),
            Err(TupleTypeError::UnsupportedElementOrder { index: 0 }),
        );
        assert_eq!(observable_state(&store), before);
        assert_eq!(
            store.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string],
                &[variadic],
                false,
            )),
            Err(TupleTypeError::UnsupportedElementFlags {
                index: 0,
                flags: ElementFlags::VARIADIC,
            }),
        );
        assert_eq!(observable_state(&store), before);

        let mut foreign = initialized();
        let foreign_type = foreign.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            store.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[foreign_type],
                &[required],
                false,
            )),
            Err(TupleTypeError::InvalidElementType {
                index: 0,
                type_: foreign_type,
            }),
        );
        assert_eq!(observable_state(&store), before);

        let (foreign_label, _) = labeled_nodes(&mut foreign, 932);
        let foreign_info = element_info(&foreign, ElementFlags::REQUIRED, Some(foreign_label));
        assert_eq!(
            store.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string],
                &[foreign_info],
                false,
            )),
            Err(TupleTypeError::InvalidElementInfo { index: 0 }),
        );
        assert_eq!(observable_state(&store), before);
    }

    #[test]
    fn every_capacity_preflight_is_failure_atomic() {
        for (additional_types, additional_symbols, additional_tables, additional_targets) in [
            (usize::MAX, 0, 0, 0),
            (0, usize::MAX, 0, 0),
            (0, 0, usize::MAX, 0),
            (0, 0, 0, usize::MAX),
        ] {
            let mut store = initialized();
            let before = observable_state(&store);
            assert!(!store.reserve_tuple_construction_for_test(
                additional_types,
                additional_symbols,
                additional_tables,
                additional_targets,
            ));
            assert_eq!(observable_state(&store), before);
        }
    }

    #[test]
    fn target_instance_and_foreign_cache_poison_are_rejected_read_only() {
        let mut length_poison = initialized();
        let string = length_poison.intrinsic_bootstrap().unwrap().string_type;
        let number = length_poison.intrinsic_bootstrap().unwrap().number_type;
        let infos = [
            element_info(&length_poison, ElementFlags::REQUIRED, None),
            element_info(&length_poison, ElementFlags::OPTIONAL, None),
        ];
        let types = [string, number];
        let instance = length_poison
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &infos, false))
            .unwrap();
        let target = length_poison
            .canonical_tuple_shape(instance)
            .unwrap()
            .unwrap()
            .target();
        let length_type = length_poison
            .canonical_tuple_target_for_type(target)
            .unwrap()
            .1
            .length_type;
        assert!(length_poison.add_type_flags(length_type, TypeFlags::ENUM_LITERAL));
        let poisoned = observable_state(&length_poison);
        assert_eq!(
            length_poison
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &infos, false)),
            Err(TupleTypeError::InvalidTargetCache(target)),
        );
        assert_eq!(observable_state(&length_poison), poisoned);

        let mut target_poison = initialized();
        let string = target_poison.intrinsic_bootstrap().unwrap().string_type;
        let number = target_poison.intrinsic_bootstrap().unwrap().number_type;
        let info = [element_info(&target_poison, ElementFlags::REQUIRED, None)];
        let types = [string];
        let instance = target_poison
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &info, false))
            .unwrap();
        let target = target_poison
            .canonical_tuple_shape(instance)
            .unwrap()
            .unwrap()
            .target();
        let this_type = match target_poison.type_payload(target).unwrap().data() {
            TypeData::Tuple(tuple) => tuple.interface.this_type.unwrap(),
            _ => unreachable!(),
        };
        assert!(target_poison.set_resolved_base_constraint(this_type, Some(number)));
        let poisoned = observable_state(&target_poison);
        assert_eq!(
            target_poison
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &info, false,)),
            Err(TupleTypeError::InvalidTargetCache(target)),
        );
        assert_eq!(observable_state(&target_poison), poisoned);

        let mut instance_poison = initialized();
        let string = instance_poison.intrinsic_bootstrap().unwrap().string_type;
        let number = instance_poison.intrinsic_bootstrap().unwrap().number_type;
        let info = [element_info(&instance_poison, ElementFlags::REQUIRED, None)];
        let types = [string];
        let instance = instance_poison
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &info, false))
            .unwrap();
        let target = instance_poison
            .canonical_tuple_shape(instance)
            .unwrap()
            .unwrap()
            .target();
        assert!(instance_poison.set_type_reference_resolution(instance, None, Some(vec![number]),));
        let poisoned = observable_state(&instance_poison);
        assert_eq!(
            instance_poison
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &info, false,)),
            Err(TupleTypeError::InvalidInstantiationCache { target, instance }),
        );
        assert_eq!(observable_state(&instance_poison), poisoned);

        let mut local = initialized();
        let local_string = local.intrinsic_bootstrap().unwrap().string_type;
        let local_info = [element_info(&local, ElementFlags::REQUIRED, None)];
        let local_types = [local_string];
        let local_instance = local
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &local_types,
                &local_info,
                false,
            ))
            .unwrap();
        let local_target = local
            .canonical_tuple_shape(local_instance)
            .unwrap()
            .unwrap()
            .target();
        let key = CanonicalTupleTargetKey {
            element_infos: local_info.to_vec(),
            readonly: false,
        };
        let mut foreign = initialized();
        let foreign_string = foreign.intrinsic_bootstrap().unwrap().string_type;
        let foreign_info = [element_info(&foreign, ElementFlags::REQUIRED, None)];
        let foreign_instance = foreign
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[foreign_string],
                &foreign_info,
                false,
            ))
            .unwrap();
        let foreign_target = foreign
            .canonical_tuple_shape(foreign_instance)
            .unwrap()
            .unwrap()
            .target();
        assert_eq!(
            local.replace_canonical_tuple_target_for_test(&key, foreign_target),
            Some(local_target),
        );
        let poisoned = observable_state(&local);
        assert_eq!(
            local.create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &local_types,
                &local_info,
                false,
            )),
            Err(TupleTypeError::InvalidTargetCache(foreign_target)),
        );
        assert_eq!(observable_state(&local), poisoned);
    }
}
