//! Canonical direct generic class and interface references.
//!
//! This is the first dependency-closed slice of pinned
//! `getTypeFromClassOrInterfaceReference` and `createTypeReferenceEx`. It
//! accepts an already-resolved top-level class or interface target and an
//! explicit, full-arity argument vector. The target's existing
//! `InterfaceType.instantiations` map remains the sole identity cache.
//!
//! Direct references deliberately retain no mapper. A mapper belongs to the
//! query that later instantiates a node-less reference's arguments or resolves
//! its members; storing one on the shell would instead describe an upstream
//! deferred reference.

use std::collections::HashSet;

use ts_binder::{SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, TypeId,
    array_types::CanonicalArrayTargets,
    declared::{cached_ordinary_type_parameter_owner, malformed_alias_merge, type_list_key},
    instantiate::{
        InstantiationLimits, InstantiationSession, instantiate_type_with_vector_and_session,
    },
    type_records::{CacheHashKey, TypeCacheState, TypeData, TypeRecord, TypeReferenceData},
    types::{ObjectFlags, TypeFlags},
};

/// A malformed or unsupported direct generic reference graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DirectGenericReferenceError {
    InvalidTarget(TypeId),
    NonGenericTarget(TypeId),
    OuterTypeParameters(TypeId),
    TypeArgumentArity {
        target: TypeId,
        expected: usize,
        actual: usize,
    },
    InvalidTypeArgument {
        target: TypeId,
        index: usize,
        type_: TypeId,
    },
    InvalidTypeParameterDefault {
        target: TypeId,
        index: usize,
        type_: TypeId,
    },
    UnsupportedCreationFlags(ObjectFlags),
    InvalidInstantiationCache(TypeId),
    InstantiationCacheHashCollision {
        target: TypeId,
        cached: TypeId,
    },
    InvalidCachedReference {
        target: TypeId,
        reference: TypeId,
    },
    RecursiveReference(TypeId),
    Capacity(TypeId),
}

impl std::fmt::Display for DirectGenericReferenceError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidTarget(target) => {
                write!(formatter, "invalid direct generic target {target:?}")
            }
            Self::NonGenericTarget(target) => {
                write!(formatter, "target {target:?} is not generic")
            }
            Self::OuterTypeParameters(target) => write!(
                formatter,
                "target {target:?} requires outer type-parameter composition"
            ),
            Self::TypeArgumentArity {
                target,
                expected,
                actual,
            } => write!(
                formatter,
                "target {target:?} requires {expected} explicit type arguments, got {actual}"
            ),
            Self::InvalidTypeArgument {
                target,
                index,
                type_,
            } => write!(
                formatter,
                "type argument {index} ({type_:?}) is invalid for target {target:?}"
            ),
            Self::InvalidTypeParameterDefault {
                target,
                index,
                type_,
            } => write!(
                formatter,
                "type parameter default {index} ({type_:?}) is invalid for target {target:?}"
            ),
            Self::UnsupportedCreationFlags(flags) => {
                write!(
                    formatter,
                    "unsupported direct-reference creation flags {flags:?}"
                )
            }
            Self::InvalidInstantiationCache(target) => {
                write!(
                    formatter,
                    "invalid instantiation cache on target {target:?}"
                )
            }
            Self::InstantiationCacheHashCollision { target, cached } => write!(
                formatter,
                "target {target:?} cache key collides with reference {cached:?}"
            ),
            Self::InvalidCachedReference { target, reference } => write!(
                formatter,
                "target {target:?} retains invalid reference {reference:?}"
            ),
            Self::RecursiveReference(reference) => {
                write!(
                    formatter,
                    "reference {reference:?} recursively contains itself"
                )
            }
            Self::Capacity(target) => {
                write!(
                    formatter,
                    "cannot reserve a reference for target {target:?}"
                )
            }
        }
    }
}

impl std::error::Error for DirectGenericReferenceError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectGenericReference {
    pub target: TypeId,
    pub type_arguments: Vec<TypeId>,
}

#[derive(Clone, Debug)]
struct DirectGenericTarget {
    target: TypeId,
    symbol: SemanticSymbolId,
    type_parameters: Vec<TypeId>,
}

fn direct_target_header(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<DirectGenericTarget, DirectGenericReferenceError> {
    let record = store
        .type_payload(target)
        .ok_or(DirectGenericReferenceError::InvalidTarget(target))?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(DirectGenericReferenceError::InvalidTarget(target));
    };
    let Some(type_parameters) = interface.reference.resolved_type_arguments.as_deref() else {
        return Err(DirectGenericReferenceError::NonGenericTarget(target));
    };
    if type_parameters.is_empty() {
        return Err(DirectGenericReferenceError::NonGenericTarget(target));
    }
    if interface.outer_type_parameter_count != 0 {
        return Err(DirectGenericReferenceError::OuterTypeParameters(target));
    }
    let symbol = record
        .symbol()
        .ok_or(DirectGenericReferenceError::InvalidTarget(target))?;
    Ok(DirectGenericTarget {
        target,
        symbol,
        type_parameters: type_parameters.to_vec(),
    })
}

fn validate_direct_target_shell(
    store: &CanonicalTypeMapperStore,
    shape: &DirectGenericTarget,
) -> Result<(), DirectGenericReferenceError> {
    let invalid = || DirectGenericReferenceError::InvalidTarget(shape.target);
    let record = store.type_payload(shape.target).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(invalid());
    };
    let Some(all_type_parameters) = interface.all_type_parameters.as_deref() else {
        return Err(invalid());
    };
    let Some(this_type) = interface.this_type else {
        return Err(invalid());
    };
    let symbol_flags = store
        .symbol(shape.symbol)
        .map(ts_binder::semantic::Symbol::flags)
        .ok_or_else(invalid)?;
    let target_origin = record.object_flags() & ObjectFlags::CLASS_OR_INTERFACE;
    let mutable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::CONTAINS_SPREAD
        | ObjectFlags::OBJECT_REST_TYPE
        | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
        | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
        | ObjectFlags::UNRESOLVED_MEMBERS;
    let allowed_flags = ObjectFlags::CLASS_OR_INTERFACE
        | ObjectFlags::REFERENCE
        | ObjectFlags::PROPAGATING_FLAGS
        | mutable_flags;
    if record.flags() != TypeFlags::OBJECT
        || !matches!(target_origin, ObjectFlags::CLASS | ObjectFlags::INTERFACE)
        || !record.object_flags().contains(ObjectFlags::REFERENCE)
        || !(record.object_flags() & !allowed_flags).is_empty()
        || record.symbol() != Some(shape.symbol)
        || !symbol_flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
        || target_origin == ObjectFlags::CLASS && !symbol_flags.contains(SymbolFlags::CLASS)
        || target_origin == ObjectFlags::INTERFACE && !symbol_flags.contains(SymbolFlags::INTERFACE)
        || malformed_alias_merge(symbol_flags)
        || store
            .declared_type_links(shape.symbol)
            .and_then(|links| links.declared_type)
            != Some(shape.target)
        || record.alias().is_some()
        || interface.outer_type_parameter_count != 0
        || interface.reference.object.target != Some(shape.target)
        || interface.reference.object.mapper.is_some()
        || interface.reference.node.is_some()
        || interface.reference.resolved_type_arguments.as_deref()
            != Some(shape.type_parameters.as_slice())
        || all_type_parameters.len() != shape.type_parameters.len() + 1
        || &all_type_parameters[..shape.type_parameters.len()] != shape.type_parameters.as_slice()
        || all_type_parameters.last().copied() != Some(this_type)
        || shape.type_parameters.contains(&this_type)
        || shape
            .type_parameters
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .len()
            != shape.type_parameters.len()
        || !shape
            .type_parameters
            .iter()
            .all(|parameter| cached_ordinary_type_parameter_owner(store, *parameter).is_some())
    {
        return Err(invalid());
    }

    let Some(this_record) = store.type_payload(this_type) else {
        return Err(invalid());
    };
    let allowed_parameter_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if this_record.flags() != TypeFlags::TYPE_PARAMETER
        || !(this_record.object_flags() == ObjectFlags::NONE
            || this_record.object_flags() == allowed_parameter_flags)
        || this_record.symbol() != Some(shape.symbol)
        || this_record.alias().is_some()
        || !matches!(
            this_record.data(),
            TypeData::TypeParameter(data)
                if data.is_this_type
                    && data.constraint == Some(shape.target)
                    && data.target.is_none()
                    && data.mapper.is_none()
        )
    {
        return Err(invalid());
    }
    Ok(())
}

fn direct_reference_parts(record: &TypeRecord) -> Option<&TypeReferenceData> {
    match record.data() {
        TypeData::TypeReference(reference) => Some(reference),
        TypeData::Interface(interface) => Some(&interface.reference),
        _ => None,
    }
}

fn propagating_flags(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    arguments: &[TypeId],
) -> Result<ObjectFlags, DirectGenericReferenceError> {
    arguments
        .iter()
        .copied()
        .enumerate()
        .try_fold(ObjectFlags::NONE, |flags, (index, argument)| {
            let record = store.type_payload(argument).ok_or(
                DirectGenericReferenceError::InvalidTypeArgument {
                    target,
                    index,
                    type_: argument,
                },
            )?;
            Ok(flags | record.object_flags() & ObjectFlags::PROPAGATING_FLAGS)
        })
}

fn validate_cached_reference_shell(
    store: &CanonicalTypeMapperStore,
    shape: &DirectGenericTarget,
    key: CacheHashKey,
    reference: TypeId,
) -> Result<Vec<TypeId>, DirectGenericReferenceError> {
    if reference == shape.target {
        return if key == type_list_key(&shape.type_parameters) {
            Ok(shape.type_parameters.clone())
        } else {
            Err(DirectGenericReferenceError::InvalidInstantiationCache(
                shape.target,
            ))
        };
    }

    let invalid = || DirectGenericReferenceError::InvalidCachedReference {
        target: shape.target,
        reference,
    };
    let record = store.type_payload(reference).ok_or_else(invalid)?;
    let TypeData::TypeReference(data) = record.data() else {
        return Err(invalid());
    };
    let Some(arguments) = data.resolved_type_arguments.as_deref() else {
        return Err(invalid());
    };
    let expected_propagating = propagating_flags(store, shape.target, arguments)?;
    let mutable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::CONTAINS_SPREAD
        | ObjectFlags::OBJECT_REST_TYPE
        | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
        | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
        | ObjectFlags::UNRESOLVED_MEMBERS;
    let allowed_flags = ObjectFlags::REFERENCE
        | ObjectFlags::FROM_TYPE_NODE
        | ObjectFlags::PROPAGATING_FLAGS
        | mutable_flags;
    if record.flags() != TypeFlags::OBJECT
        || arguments.len() != shape.type_parameters.len()
        || key != type_list_key(arguments)
        || data.object.target != Some(shape.target)
        || data.object.mapper.is_some()
        || data.object.instantiations != TypeCacheState::Unallocated
        || data.node.is_some()
        || record.alias().is_some()
        || record.symbol() != Some(shape.symbol)
        || !record.object_flags().contains(ObjectFlags::REFERENCE)
        || record.object_flags() & ObjectFlags::PROPAGATING_FLAGS != expected_propagating
        || !(record.object_flags() & !allowed_flags).is_empty()
    {
        return Err(invalid());
    }
    Ok(arguments.to_vec())
}

fn validate_reference_argument_graph(
    store: &CanonicalTypeMapperStore,
    reference: TypeId,
    active: &mut Vec<TypeId>,
    validated: &mut HashSet<TypeId>,
) -> Result<(), DirectGenericReferenceError> {
    if validated.contains(&reference) {
        return Ok(());
    }
    if active.contains(&reference) {
        return Err(DirectGenericReferenceError::RecursiveReference(reference));
    }
    let Some(record) = store.type_payload(reference) else {
        return Ok(());
    };
    let constituents = match record.data() {
        TypeData::Union(union) => Some(union.union.types.as_slice()),
        TypeData::Intersection(intersection) => Some(intersection.intersection.types.as_slice()),
        _ => None,
    };
    if let Some(constituents) = constituents {
        active.push(reference);
        for constituent in constituents {
            validate_reference_argument_graph(store, *constituent, active, validated)?;
        }
        let popped = active
            .pop()
            .expect("a composite argument owns one active validation frame");
        debug_assert_eq!(popped, reference);
        validated.insert(reference);
        return Ok(());
    }
    let Some(reference_data) = direct_reference_parts(record) else {
        return Ok(());
    };
    let (target, arguments) = match (
        reference_data.object.target,
        reference_data.resolved_type_arguments.as_deref(),
    ) {
        (Some(target), Some(arguments)) => (target, arguments),
        _ if matches!(record.data(), TypeData::TypeReference(_)) => {
            return Err(DirectGenericReferenceError::InvalidCachedReference {
                target: reference_data.object.target.unwrap_or(reference),
                reference,
            });
        }
        _ => return Ok(()),
    };
    if target == reference {
        // The origin's `(type parameters) -> origin` edge is the legal
        // recursive identity installed by declared-type initialization.
        let shape = direct_target_header(store, target)?;
        validate_direct_target_shell(store, &shape)?;
        return Ok(());
    }
    let shape = match direct_target_header(store, target) {
        Ok(shape) => shape,
        Err(error)
            if matches!(
                store.type_payload(target).map(TypeRecord::data),
                Some(TypeData::Interface(_))
            ) =>
        {
            return Err(error);
        }
        Err(_) => {
            // Tuple and deferred-reference argument families are opaque at
            // this direct class/interface boundary.
            return Ok(());
        }
    };
    validate_direct_target_shell(store, &shape)?;
    let key = type_list_key(arguments);
    let TypeData::Interface(target_data) = store
        .type_payload(target)
        .ok_or(DirectGenericReferenceError::InvalidTarget(target))?
        .data()
    else {
        unreachable!("the direct target shell was just validated")
    };
    let TypeCacheState::Allocated(instantiations) = &target_data.reference.object.instantiations
    else {
        return Err(DirectGenericReferenceError::InvalidInstantiationCache(
            target,
        ));
    };
    if instantiations.get(&key) != Some(&reference) {
        return Err(DirectGenericReferenceError::InvalidCachedReference { target, reference });
    }
    validate_cached_reference_shell(store, &shape, key, reference)?;

    active.push(reference);
    for argument in arguments {
        validate_reference_argument_graph(store, *argument, active, validated)?;
    }
    let popped = active
        .pop()
        .expect("a direct reference owns one active validation frame");
    debug_assert_eq!(popped, reference);
    validated.insert(reference);
    Ok(())
}

fn validate_direct_target_and_cache(
    store: &CanonicalTypeMapperStore,
    shape: &DirectGenericTarget,
) -> Result<(), DirectGenericReferenceError> {
    validate_direct_target_shell(store, shape)?;
    let TypeData::Interface(interface) = store
        .type_payload(shape.target)
        .expect("the direct target shell was just validated")
        .data()
    else {
        unreachable!("the direct target shell was just validated")
    };
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        return Err(DirectGenericReferenceError::InvalidInstantiationCache(
            shape.target,
        ));
    };
    if instantiations.get(&type_list_key(&shape.type_parameters)) != Some(&shape.target) {
        return Err(DirectGenericReferenceError::InvalidInstantiationCache(
            shape.target,
        ));
    }

    let mut validated = HashSet::new();
    for (key, reference) in instantiations {
        validate_cached_reference_shell(store, shape, *key, *reference)?;
        if *reference != shape.target {
            validate_reference_argument_graph(store, *reference, &mut Vec::new(), &mut validated)?;
        }
    }
    Ok(())
}

/// Validates one canonical node-less class/interface reference and returns its
/// exact declared target and ordered argument vector.
pub(super) fn validate_direct_generic_reference(
    store: &CanonicalTypeMapperStore,
    reference: TypeId,
) -> Result<DirectGenericReference, DirectGenericReferenceError> {
    let record = store.type_payload(reference).ok_or(
        DirectGenericReferenceError::InvalidCachedReference {
            target: reference,
            reference,
        },
    )?;
    let data = direct_reference_parts(record).ok_or(
        DirectGenericReferenceError::InvalidCachedReference {
            target: reference,
            reference,
        },
    )?;
    let target = data
        .object
        .target
        .ok_or(DirectGenericReferenceError::InvalidCachedReference {
            target: reference,
            reference,
        })?;
    let arguments = data
        .resolved_type_arguments
        .as_deref()
        .ok_or(DirectGenericReferenceError::InvalidCachedReference { target, reference })?;
    let shape = direct_target_header(store, target)?;
    if arguments.len() != shape.type_parameters.len() {
        return Err(DirectGenericReferenceError::TypeArgumentArity {
            target,
            expected: shape.type_parameters.len(),
            actual: arguments.len(),
        });
    }
    validate_direct_target_and_cache(store, &shape)?;
    let key = type_list_key(arguments);
    let TypeData::Interface(interface) = store
        .type_payload(target)
        .expect("the direct target and cache were just validated")
        .data()
    else {
        unreachable!("the direct target and cache were just validated")
    };
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        unreachable!("the direct target and cache were just validated")
    };
    if instantiations.get(&key) != Some(&reference) {
        return Err(DirectGenericReferenceError::InvalidCachedReference { target, reference });
    }
    let exact = validate_cached_reference_shell(store, &shape, key, reference)?;
    if exact.as_slice() != arguments {
        return Err(DirectGenericReferenceError::InvalidCachedReference { target, reference });
    }
    Ok(DirectGenericReference {
        target,
        type_arguments: arguments.to_vec(),
    })
}

/// Pinned `createTypeReferenceEx` for an already-resolved direct class or
/// interface with an explicit full-arity argument vector.
///
/// The operation validates the complete target-local cache before allocation
/// and commits its cache entry last. Creation does not own or charge an
/// instantiation session.
pub(super) fn create_direct_generic_reference(
    store: &mut CanonicalTypeMapperStore,
    target: TypeId,
    type_arguments: &[TypeId],
    creation_flags: ObjectFlags,
) -> Result<TypeId, DirectGenericReferenceError> {
    if !(creation_flags & !ObjectFlags::FROM_TYPE_NODE).is_empty() {
        return Err(DirectGenericReferenceError::UnsupportedCreationFlags(
            creation_flags,
        ));
    }
    let shape = direct_target_header(store, target)?;
    if type_arguments.len() != shape.type_parameters.len() {
        return Err(DirectGenericReferenceError::TypeArgumentArity {
            target,
            expected: shape.type_parameters.len(),
            actual: type_arguments.len(),
        });
    }
    for (index, type_) in type_arguments.iter().copied().enumerate() {
        if store.type_payload(type_).is_none() {
            return Err(DirectGenericReferenceError::InvalidTypeArgument {
                target,
                index,
                type_,
            });
        }
    }
    validate_direct_target_and_cache(store, &shape)?;
    let mut validated_arguments = HashSet::new();
    for argument in type_arguments {
        validate_reference_argument_graph(
            store,
            *argument,
            &mut Vec::new(),
            &mut validated_arguments,
        )?;
    }

    let key = type_list_key(type_arguments);
    let existing = {
        let TypeData::Interface(interface) = store
            .type_payload(target)
            .expect("the direct target and cache were just validated")
            .data()
        else {
            unreachable!("the direct target and cache were just validated")
        };
        let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
        else {
            unreachable!("the direct target and cache were just validated")
        };
        instantiations.get(&key).copied()
    };
    if let Some(existing) = existing {
        let exact = validate_cached_reference_shell(store, &shape, key, existing)?;
        if exact.as_slice() != type_arguments {
            return Err(
                DirectGenericReferenceError::InstantiationCacheHashCollision {
                    target,
                    cached: existing,
                },
            );
        }
        return Ok(existing);
    }

    let argument_flags = propagating_flags(store, target, type_arguments)?;
    if !store.try_reserve_types(1) || !store.try_reserve_object_instantiations(target, 1) {
        return Err(DirectGenericReferenceError::Capacity(target));
    }
    let reference = store
        .alloc_type_reference(argument_flags | creation_flags, Some(shape.symbol))
        .ok_or(DirectGenericReferenceError::Capacity(target))?;
    assert!(store.set_object_target_and_mapper(reference, Some(target), None));
    assert!(store.set_type_reference_resolution(reference, None, Some(type_arguments.to_vec()),));
    let canonical = store
        .insert_object_instantiation(target, key, reference)
        .expect("the preflighted target accepts its direct reference");
    assert_eq!(
        canonical, reference,
        "the complete direct reference is committed to its cache last"
    );
    debug_assert_eq!(
        validate_direct_generic_reference(store, reference),
        Ok(DirectGenericReference {
            target,
            type_arguments: type_arguments.to_vec(),
        })
    );
    Ok(reference)
}

/// Fills already-resolved trailing defaults before creating one canonical
/// class or interface reference.
///
/// Defaults are evaluated in declaration order with earlier arguments
/// installed and later arguments temporarily mapped to the error type.
pub(super) fn create_direct_generic_reference_with_defaults(
    store: &mut CanonicalTypeMapperStore,
    target: TypeId,
    provided: &[TypeId],
    creation_flags: ObjectFlags,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, DirectGenericReferenceError> {
    let shape = direct_target_header(store, target)?;
    let (no_constraint, circular_constraint, resolving_default, error_type) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(DirectGenericReferenceError::InvalidTarget(target))?;
        (
            bootstrap.no_constraint_type,
            bootstrap.circular_constraint_type,
            bootstrap.resolving_default_type,
            bootstrap.error_type,
        )
    };
    let mut defaults = Vec::new();
    defaults
        .try_reserve_exact(shape.type_parameters.len())
        .map_err(|_| DirectGenericReferenceError::Capacity(target))?;
    let mut minimum = 0;
    for (index, parameter) in shape.type_parameters.iter().copied().enumerate() {
        let TypeData::TypeParameter(data) = store
            .type_payload(parameter)
            .ok_or(DirectGenericReferenceError::InvalidTarget(target))?
            .data()
        else {
            return Err(DirectGenericReferenceError::InvalidTarget(target));
        };
        let default = data
            .resolved_default_type
            .filter(|default| *default != no_constraint);
        if default.is_none() {
            minimum = index + 1;
        }
        defaults.push(default);
    }
    if provided.len() < minimum || provided.len() > shape.type_parameters.len() {
        return Err(DirectGenericReferenceError::TypeArgumentArity {
            target,
            expected: if provided.len() < minimum {
                minimum
            } else {
                shape.type_parameters.len()
            },
            actual: provided.len(),
        });
    }
    for (index, argument) in provided.iter().copied().enumerate() {
        if store.type_payload(argument).is_none() {
            return Err(DirectGenericReferenceError::InvalidTypeArgument {
                target,
                index,
                type_: argument,
            });
        }
    }
    validate_direct_target_and_cache(store, &shape)?;
    for (index, default) in defaults.iter().enumerate().skip(provided.len()) {
        let Some(default) = *default else {
            return Err(DirectGenericReferenceError::TypeArgumentArity {
                target,
                expected: index + 1,
                actual: provided.len(),
            });
        };
        if default == circular_constraint
            || default == resolving_default
            || store.type_payload(default).is_none()
        {
            return Err(DirectGenericReferenceError::InvalidTypeParameterDefault {
                target,
                index,
                type_: default,
            });
        }
        validate_reference_argument_graph(store, default, &mut Vec::new(), &mut HashSet::new())?;
    }

    let mut completed = Vec::new();
    completed
        .try_reserve_exact(shape.type_parameters.len())
        .map_err(|_| DirectGenericReferenceError::Capacity(target))?;
    completed.extend_from_slice(provided);
    completed.resize(shape.type_parameters.len(), error_type);
    for index in provided.len()..shape.type_parameters.len() {
        let default = defaults[index].expect("missing defaults were rejected before mutation");
        let resolved = instantiate_type_with_vector_and_session(
            store,
            default,
            &shape.type_parameters,
            &completed,
            array_targets,
            session,
        )
        .map_err(
            |_| DirectGenericReferenceError::InvalidTypeParameterDefault {
                target,
                index,
                type_: default,
            },
        )?;
        completed[index] = resolved;
    }
    create_direct_generic_reference(store, target, &completed, creation_flags)
}

impl CanonicalTypeMapperStore {
    /// Creates or reuses one node-less, full-arity direct class/interface
    /// reference from the target-owned canonical instantiation cache.
    ///
    /// This context-free adapter deliberately does not grant
    /// `ObjectFlags::FROM_TYPE_NODE`; source type-node queries retain ownership
    /// of that provenance bit.
    ///
    /// # Errors
    ///
    /// Returns [`DirectGenericReferenceError`] for a foreign or malformed
    /// target/cache, invalid arity or argument identity, recursion poison, or
    /// capacity failure.
    pub fn create_direct_generic_reference_type(
        &mut self,
        target: TypeId,
        type_arguments: &[TypeId],
    ) -> Result<TypeId, DirectGenericReferenceError> {
        create_direct_generic_reference(self, target, type_arguments, ObjectFlags::NONE)
    }

    /// Creates or reuses one direct reference after filling canonical cached
    /// trailing type-parameter defaults.
    ///
    /// # Errors
    ///
    /// Returns [`DirectGenericReferenceError`] for invalid arguments, absent
    /// required parameters, malformed defaults, or a poisoned target cache.
    pub fn create_direct_generic_reference_type_with_defaults(
        &mut self,
        target: TypeId,
        type_arguments: &[TypeId],
    ) -> Result<TypeId, DirectGenericReferenceError> {
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        create_direct_generic_reference_with_defaults(
            self,
            target,
            type_arguments,
            ObjectFlags::NONE,
            None,
            &mut session,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{
        DeclaredTypeLinks, IntrinsicBootstrapOptions, SemanticStore,
        instantiate::instantiate_type_with_session, mapper::TypeMapper, type_records::TypeRecord,
    };
    use ts_binder::{CheckFlags, EscapedName, SymbolData};

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn generic_target(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
        origin: ObjectFlags,
        arity: usize,
    ) -> (TypeId, Vec<TypeId>) {
        let symbol = store
            .alloc_symbol(SymbolData::new(
                if origin == ObjectFlags::CLASS {
                    SymbolFlags::CLASS
                } else {
                    SymbolFlags::INTERFACE
                },
                EscapedName::source(name),
            ))
            .unwrap();
        let mut parameters = Vec::new();
        for index in 0..arity {
            let parameter_symbol = store
                .alloc_symbol(SymbolData::new(
                    SymbolFlags::TYPE_PARAMETER,
                    EscapedName::source(format!("T{index}")),
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
            parameters.push(parameter);
        }
        let target = store.alloc_interface_type(origin, Some(symbol)).unwrap();
        assert!(store.set_declared_type_links(
            symbol,
            DeclaredTypeLinks {
                declared_type: Some(target),
                ..DeclaredTypeLinks::default()
            },
        ));
        let this_type = store.alloc_type_parameter(Some(symbol)).unwrap();
        let mut all = parameters.clone();
        all.push(this_type);
        assert!(store.initialize_interface_type_parameters(
            target,
            all,
            0,
            this_type,
            type_list_key(&parameters),
        ));
        (target, parameters)
    }

    #[test]
    fn explicit_full_arity_class_and_interface_references_are_canonical() {
        let mut store = initialized_store();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        for origin in [ObjectFlags::CLASS, ObjectFlags::INTERFACE] {
            let (target, parameters) = generic_target(&mut store, "Pair", origin, 2);
            assert_eq!(
                validate_direct_generic_reference(&store, target),
                Ok(DirectGenericReference {
                    target,
                    type_arguments: parameters.clone(),
                }),
                "the declared parameter vector owns the legal origin identity",
            );
            assert_eq!(
                create_direct_generic_reference(
                    &mut store,
                    target,
                    &[string],
                    ObjectFlags::FROM_TYPE_NODE,
                ),
                Err(DirectGenericReferenceError::TypeArgumentArity {
                    target,
                    expected: 2,
                    actual: 1,
                }),
            );
            let before = store.type_len();
            let before_mappers = store.mapper_len();
            let first = create_direct_generic_reference(
                &mut store,
                target,
                &[string, number],
                ObjectFlags::FROM_TYPE_NODE,
            )
            .unwrap();
            assert_eq!(store.type_len(), before + 1);
            assert_eq!(store.mapper_len(), before_mappers);
            let first_record = store.type_payload(first).unwrap();
            let TypeData::TypeReference(first_reference) = first_record.data() else {
                panic!("a nonidentity direct instantiation is a type reference");
            };
            assert!(
                first_record
                    .object_flags()
                    .contains(ObjectFlags::FROM_TYPE_NODE)
            );
            assert_eq!(first_reference.object.mapper, None);
            assert_eq!(
                first_reference.object.instantiations,
                TypeCacheState::Unallocated
            );
            let warm = create_direct_generic_reference(
                &mut store,
                target,
                &[string, number],
                ObjectFlags::NONE,
            )
            .unwrap();
            assert_eq!(warm, first);
            assert_eq!(store.type_len(), before + 1);
            assert_eq!(store.mapper_len(), before_mappers);
            assert_eq!(
                validate_direct_generic_reference(&store, first),
                Ok(DirectGenericReference {
                    target,
                    type_arguments: vec![string, number],
                }),
            );
            assert_eq!(
                create_direct_generic_reference(&mut store, target, &parameters, ObjectFlags::NONE,),
                Ok(target),
                "the declared type-parameter vector is the origin identity",
            );
        }
    }

    #[test]
    fn direct_references_fill_trailing_and_dependent_defaults_without_mappers() {
        let mut store = initialized_store();
        let (target, parameters) = generic_target(&mut store, "Result", ObjectFlags::INTERFACE, 3);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        assert!(store.set_type_parameter_resolution(
            parameters[1],
            None,
            None,
            None,
            Some(parameters[0]),
        ));
        assert!(
            store.set_type_parameter_resolution(parameters[2], None, None, None, Some(string),)
        );
        let before_mappers = store.mapper_len();

        let reference = store
            .create_direct_generic_reference_type_with_defaults(target, &[number])
            .unwrap();
        assert_eq!(
            validate_direct_generic_reference(&store, reference),
            Ok(DirectGenericReference {
                target,
                type_arguments: vec![number, number, string],
            }),
        );
        assert_eq!(store.mapper_len(), before_mappers);
        assert_eq!(
            store.create_direct_generic_reference_type(target, &[number, number, string]),
            Ok(reference),
        );
        let before_types = store.type_len();
        assert_eq!(
            store.create_direct_generic_reference_type_with_defaults(target, &[number]),
            Ok(reference),
        );
        assert_eq!(store.type_len(), before_types);
    }

    #[test]
    fn invalid_or_circular_defaults_are_rejected_before_reference_publication() {
        let mut store = initialized_store();
        let (target, parameters) = generic_target(&mut store, "Result", ObjectFlags::INTERFACE, 2);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            store.create_direct_generic_reference_type_with_defaults(target, &[string]),
            Err(DirectGenericReferenceError::TypeArgumentArity {
                target,
                expected: 2,
                actual: 1,
            }),
        );

        let circular = store
            .intrinsic_bootstrap()
            .unwrap()
            .circular_constraint_type;
        assert!(store.set_type_parameter_resolution(
            parameters[1],
            None,
            None,
            None,
            Some(circular),
        ));
        let before = (store.type_len(), store.mapper_len());
        assert_eq!(
            store.create_direct_generic_reference_type_with_defaults(target, &[string]),
            Err(DirectGenericReferenceError::InvalidTypeParameterDefault {
                target,
                index: 1,
                type_: circular,
            }),
        );
        assert_eq!((store.type_len(), store.mapper_len()), before);
    }

    #[test]
    fn foreign_arguments_and_targets_fail_without_writes() {
        let mut store = initialized_store();
        let (target, _) = generic_target(&mut store, "Box", ObjectFlags::INTERFACE, 1);
        let foreign = initialized_store();
        let foreign_string = foreign.intrinsic_bootstrap().unwrap().string_type;
        let before = store.type_len();
        assert_eq!(
            create_direct_generic_reference(
                &mut store,
                target,
                &[foreign_string],
                ObjectFlags::NONE,
            ),
            Err(DirectGenericReferenceError::InvalidTypeArgument {
                target,
                index: 0,
                type_: foreign_string,
            }),
        );
        assert_eq!(
            create_direct_generic_reference(&mut store, foreign_string, &[], ObjectFlags::NONE,),
            Err(DirectGenericReferenceError::InvalidTarget(foreign_string)),
        );
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn poisoned_mapper_and_cache_key_are_rejected_before_allocation() {
        let mut store = initialized_store();
        let (target, parameters) = generic_target(&mut store, "Box", ObjectFlags::INTERFACE, 1);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let symbol = store.type_payload(target).unwrap().symbol();
        let poison = store
            .alloc_type_reference(ObjectFlags::NONE, symbol)
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameters[0], string).unwrap();
        assert!(store.set_object_target_and_mapper(poison, Some(target), Some(mapper)));
        assert!(store.set_type_reference_resolution(poison, None, Some(vec![string])));
        assert!(store.try_reserve_object_instantiations(target, 1));
        assert_eq!(
            store.insert_object_instantiation(target, type_list_key(&[string]), poison),
            Some(poison),
        );
        let before = store.type_len();
        assert_eq!(
            create_direct_generic_reference(&mut store, target, &[], ObjectFlags::NONE,),
            Err(DirectGenericReferenceError::TypeArgumentArity {
                target,
                expected: 1,
                actual: 0,
            }),
            "arity rejection precedes an unrelated poisoned-cache scan",
        );
        assert_eq!(
            create_direct_generic_reference(&mut store, target, &[string], ObjectFlags::NONE,),
            Err(DirectGenericReferenceError::InvalidCachedReference {
                target,
                reference: poison,
            }),
        );
        assert_eq!(store.type_len(), before);

        assert!(store.set_object_target_and_mapper(poison, Some(target), None));
        assert!(store.set_type_reference_resolution(poison, None, Some(vec![parameters[0]]),));
        assert_eq!(
            create_direct_generic_reference(&mut store, target, &[string], ObjectFlags::NONE,),
            Err(DirectGenericReferenceError::InvalidCachedReference {
                target,
                reference: poison,
            }),
            "the retained key must match the exact argument vector",
        );
    }

    #[test]
    fn poisoned_nested_reference_mapper_is_rejected_before_outer_publication() {
        let mut store = initialized_store();
        let (outer, _) = generic_target(&mut store, "Wrapper", ObjectFlags::INTERFACE, 1);
        let (inner, parameters) = generic_target(&mut store, "Box", ObjectFlags::INTERFACE, 1);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let nested =
            create_direct_generic_reference(&mut store, inner, &[string], ObjectFlags::NONE)
                .unwrap();
        let mapper = store.new_simple_type_mapper(parameters[0], string).unwrap();
        assert!(store.set_object_target_and_mapper(nested, Some(inner), Some(mapper)));
        let before = (store.type_len(), store.mapper_len());

        assert_eq!(
            create_direct_generic_reference(&mut store, outer, &[nested], ObjectFlags::NONE),
            Err(DirectGenericReferenceError::InvalidCachedReference {
                target: inner,
                reference: nested,
            }),
        );
        assert_eq!((store.type_len(), store.mapper_len()), before);
        let TypeData::Interface(target) = store.type_payload(outer).unwrap().data() else {
            panic!("the outer generic target must retain its canonical cache")
        };
        let TypeCacheState::Allocated(cache) = &target.reference.object.instantiations else {
            panic!("the outer generic target must own its instantiation cache")
        };
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn poisoned_references_inside_union_arguments_are_rejected_before_publication() {
        let mut store = initialized_store();
        let (outer, _) = generic_target(&mut store, "Wrapper", ObjectFlags::INTERFACE, 1);
        let (inner, parameters) = generic_target(&mut store, "Box", ObjectFlags::INTERFACE, 1);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let nested =
            create_direct_generic_reference(&mut store, inner, &[string], ObjectFlags::NONE)
                .unwrap();
        let mapper = store.new_simple_type_mapper(parameters[0], number).unwrap();
        assert!(store.set_object_target_and_mapper(nested, Some(inner), Some(mapper)));
        let argument = store
            .alloc_union_type(ObjectFlags::NONE, vec![nested, string])
            .unwrap();
        let before = store.type_len();

        assert_eq!(
            create_direct_generic_reference(&mut store, outer, &[argument], ObjectFlags::NONE),
            Err(DirectGenericReferenceError::InvalidCachedReference {
                target: inner,
                reference: nested,
            }),
        );
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn malformed_nested_reference_and_origin_fail_without_outer_allocation() {
        let mut store = initialized_store();
        let (outer, _) = generic_target(&mut store, "Wrapper", ObjectFlags::INTERFACE, 1);
        let orphan = store.alloc_type_reference(ObjectFlags::NONE, None).unwrap();
        let before = store.type_len();

        assert_eq!(
            create_direct_generic_reference(&mut store, outer, &[orphan], ObjectFlags::NONE),
            Err(DirectGenericReferenceError::InvalidCachedReference {
                target: orphan,
                reference: orphan,
            }),
        );
        assert_eq!(store.type_len(), before);

        let (inner, parameters) = generic_target(&mut store, "Inner", ObjectFlags::INTERFACE, 1);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let mapper = store.new_simple_type_mapper(parameters[0], string).unwrap();
        let this_type = match store.type_payload(inner).unwrap().data() {
            TypeData::Interface(interface) => interface.this_type.unwrap(),
            _ => panic!("the nested generic target must be an interface"),
        };
        assert!(store.set_type_parameter_resolution(
            this_type,
            Some(inner),
            None,
            Some(mapper),
            None,
        ));
        let before = store.type_len();

        assert_eq!(
            create_direct_generic_reference(&mut store, outer, &[inner], ObjectFlags::NONE),
            Err(DirectGenericReferenceError::InvalidTarget(inner)),
        );
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn target_symbol_kind_must_match_its_class_or_interface_origin() {
        let mut store = initialized_store();
        let (target, _) = generic_target(&mut store, "Box", ObjectFlags::INTERFACE, 1);
        let owner = store.type_payload(target).unwrap().symbol().unwrap();
        assert!(store.set_symbol_flags(owner, SymbolFlags::CLASS, CheckFlags::NONE));
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let before = store.type_len();

        assert_eq!(
            create_direct_generic_reference(&mut store, target, &[string], ObjectFlags::NONE),
            Err(DirectGenericReferenceError::InvalidTarget(target)),
        );
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn recursive_poison_is_rejected_without_unbounded_validation() {
        let mut store = initialized_store();
        let (target, _) = generic_target(&mut store, "Node", ObjectFlags::INTERFACE, 1);
        let symbol = store.type_payload(target).unwrap().symbol();
        let poison = store
            .alloc_type_reference(ObjectFlags::NONE, symbol)
            .unwrap();
        assert!(store.set_object_target_and_mapper(poison, Some(target), None));
        assert!(store.set_type_reference_resolution(poison, None, Some(vec![poison])));
        assert!(store.try_reserve_object_instantiations(target, 1));
        assert_eq!(
            store.insert_object_instantiation(target, type_list_key(&[poison]), poison),
            Some(poison),
        );

        assert_eq!(
            validate_direct_generic_reference(&store, poison),
            Err(DirectGenericReferenceError::RecursiveReference(poison)),
        );
    }

    #[test]
    fn instantiation_maps_existing_reference_arguments_with_session_accounting() {
        let mut store = initialized_store();
        let (target, parameters) = generic_target(&mut store, "Box", ObjectFlags::INTERFACE, 1);
        let (string, error_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.error_type)
        };
        let mapper = store.new_simple_type_mapper(parameters[0], string).unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let instantiated_reference =
            instantiate_type_with_session(&mut store, target, mapper, None, &mut session).unwrap();
        assert_eq!(session.query_count(), 2);
        assert_eq!(
            validate_direct_generic_reference(&store, instantiated_reference),
            Ok(DirectGenericReference {
                target,
                type_arguments: vec![string],
            }),
        );
        let warm_types = store.type_len();
        session.reset_query();
        assert_eq!(
            instantiate_type_with_session(&mut store, target, mapper, None, &mut session),
            Ok(instantiated_reference),
        );
        assert_eq!(session.query_count(), 2);
        assert_eq!(store.type_len(), warm_types);

        let identity_mapper = store.new_simple_type_mapper(string, error_type).unwrap();
        let before = session.query_count();
        assert_eq!(
            instantiate_type_with_session(
                &mut store,
                instantiated_reference,
                identity_mapper,
                None,
                &mut session,
            ),
            Ok(instantiated_reference),
        );
        assert_eq!(
            session.query_count(),
            before,
            "a concrete direct reference cannot contain mapped variables",
        );
    }

    #[test]
    fn recovering_limit_retains_the_outer_generic_reference() {
        let mut store = initialized_store();
        let (target, parameters) = generic_target(&mut store, "Box", ObjectFlags::CLASS, 1);
        let (string, error_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.error_type)
        };
        let mapper = store.new_simple_type_mapper(parameters[0], string).unwrap();
        let mut session = InstantiationSession::new_recovering(
            &store,
            InstantiationLimits {
                max_depth: 1,
                max_count: 10,
            },
            error_type,
        )
        .unwrap();
        let mark = session.limit_event_mark();
        let recovered =
            instantiate_type_with_session(&mut store, target, mapper, None, &mut session).unwrap();
        assert_eq!(
            validate_direct_generic_reference(&store, recovered),
            Ok(DirectGenericReference {
                target,
                type_arguments: vec![error_type],
            }),
        );
        assert_eq!(session.query_count(), 1);
        assert!(session.limit_event_occurred_since(mark));
    }
}
