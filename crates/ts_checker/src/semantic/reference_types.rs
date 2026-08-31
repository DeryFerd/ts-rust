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

use ts_ast::SyntaxKind;
use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, TypeId,
    array_types::CanonicalArrayTargets,
    declared::{
        cached_class_type, cached_ordinary_type_parameter_owner, malformed_alias_merge,
        type_list_key,
    },
    instantiate::{
        InstantiationLimits, InstantiationSession, instantiate_type_with_vector_and_session,
    },
    store::SourceNodeParent,
    tuple_types::TupleTypeError,
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

/// Private module interfaces have binder ownership but no global or export entry.
fn source_local_interface_owner_is_exact(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
) -> bool {
    let Some(record) = store.symbol(owner) else {
        return false;
    };
    if record.flags() != SymbolFlags::INTERFACE
        || store.source_symbol_flags(owner) != Some(SymbolFlags::INTERFACE)
        || record.check_flags() != CheckFlags::NONE
        || record.parent().is_some()
        || store.get_parent_of_symbol(owner).is_some()
        || record.value_declaration().is_some()
        || record.exports().is_some()
        || record.export_symbol().is_some()
        || !store.source_symbol_declarations_match(owner)
    {
        return false;
    }
    let Some(declarations) = record.declarations().filter(|nodes| !nodes.is_empty()) else {
        return false;
    };
    let mut source = None;
    for &declaration in declarations {
        let Some(SourceNodeParent::Parent(root)) = store.source_node_parent(declaration) else {
            return false;
        };
        if store.source_node_kind(declaration) != Some(SyntaxKind::InterfaceDeclaration)
            || store.source_node_is_exported(declaration) != Some(false)
            || store.source_declaration_symbol(declaration) != Some(owner)
            || store.symbol_store().source_binding_symbols(declaration) != Some([Some(owner), None])
            || store.source_node_kind(root) != Some(SyntaxKind::SourceFile)
            || !store.source_is_typescript_external_module(root)
            || source.is_some_and(|source| source != root)
        {
            return false;
        }
        source = Some(root);
    }
    let Some(source) = source else {
        return false;
    };
    let Some(module) = store.source_declaration_symbol(source) else {
        return false;
    };
    store.symbol_store().source_binding_symbols(source) == Some([Some(module), None])
        && store.source_symbol_declarations_match(module)
        && store.source_symbol_flags(module) == Some(SymbolFlags::VALUE_MODULE)
        && store.get_merged_symbol(module) == Some(module)
        && store.symbol(module).is_some_and(|record| {
            record.flags() == SymbolFlags::VALUE_MODULE
                && record.check_flags() == CheckFlags::NONE
                && record.parent().is_none()
                && record.export_symbol().is_none()
                && record.declarations() == Some(std::slice::from_ref(&source))
        })
}

pub(super) fn validate_nongeneric_interface_argument_origin(
    store: &CanonicalTypeMapperStore,
    argument: TypeId,
) -> Result<(), DirectGenericReferenceError> {
    let invalid = || DirectGenericReferenceError::InvalidTarget(argument);
    let record = store.type_payload(argument).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(invalid());
    };
    let owner = record.symbol().ok_or_else(invalid)?;
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    let declarations = owner_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or_else(invalid)?;
    let Some(this_type) = interface.this_type else {
        return Err(invalid());
    };
    let mutable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::CONTAINS_SPREAD
        | ObjectFlags::OBJECT_REST_TYPE
        | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
        | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
        | ObjectFlags::UNRESOLVED_MEMBERS;
    let allowed_flags = ObjectFlags::INTERFACE
        | ObjectFlags::REFERENCE
        | ObjectFlags::PROPAGATING_FLAGS
        | mutable_flags;
    let allowed_symbol_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK
            != (ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
        || !(record.object_flags() & !allowed_flags).is_empty()
        || record.alias().is_some()
        || !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record.flags().without(allowed_symbol_flags) != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(argument)
        || interface.outer_type_parameter_count != 0
        || interface.all_type_parameters.as_deref() != Some(std::slice::from_ref(&this_type))
        || interface.reference.object.target != Some(argument)
        || interface.reference.object.mapper.is_some()
        || interface.reference.node.is_some()
        || interface.reference.resolved_type_arguments.as_deref() != Some(&[])
    {
        return Err(invalid());
    }

    let mixed_owner =
        if super::object_members::source_interface_uses_legacy_single_script_value_owner(
            store, owner,
        ) {
            None
        } else {
            store
                .source_global_interface_value_owner(owner)
                .map_err(|_| invalid())?
        };
    if mixed_owner
        .as_ref()
        .is_some_and(|proof| proof.declarations() != declarations)
    {
        return Err(invalid());
    }
    let mut seen = HashSet::with_capacity(declarations.len());
    let mut has_interface = false;
    let mut value_declaration = None;
    for &declaration in declarations {
        if !seen.insert(declaration) || !store.contains_node_ref(declaration) {
            return Err(invalid());
        }
        match store.source_node_kind(declaration) {
            Some(SyntaxKind::InterfaceDeclaration) => {
                let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(declaration)
                else {
                    return Err(invalid());
                };
                if !matches!(
                    store.source_node_kind(parent),
                    Some(SyntaxKind::SourceFile | SyntaxKind::ModuleBlock)
                ) {
                    return Err(invalid());
                }
                has_interface = true;
            }
            Some(SyntaxKind::VariableDeclaration)
                if mixed_owner
                    .as_ref()
                    .is_some_and(|proof| proof.variables().contains(&declaration)) =>
            {
                value_declaration = mixed_owner.as_ref().map(|proof| proof.value_declaration());
            }
            Some(SyntaxKind::VariableDeclaration)
                if value_declaration.replace(declaration).is_none() => {}
            _ => return Err(invalid()),
        }
    }
    if !has_interface
        || owner_record.value_declaration() != value_declaration
        || owner_record
            .flags()
            .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
            != value_declaration.is_some()
    {
        return Err(invalid());
    }

    let authoritative = match store.get_parent_of_symbol(owner) {
        Some(parent) => store
            .symbol(parent)
            .filter(|parent| parent.flags().intersects(SymbolFlags::MODULE))
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(owner_record.name()))
            .and_then(|symbol| store.get_merged_symbol(symbol)),
        None => store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get(owner_record.name()))
            .and_then(|symbol| store.get_merged_symbol(symbol)),
    };
    if authoritative != Some(owner) && !source_local_interface_owner_is_exact(store, owner) {
        return Err(invalid());
    }

    let this_record = store.type_payload(this_type).ok_or_else(invalid)?;
    let allowed_parameter_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if this_record.flags() != TypeFlags::TYPE_PARAMETER
        || !(this_record.object_flags() == ObjectFlags::NONE
            || this_record.object_flags() == allowed_parameter_flags)
        || this_record.symbol() != Some(owner)
        || this_record.alias().is_some()
        || !matches!(
            this_record.data(),
            TypeData::TypeParameter(data)
                if data.is_this_type
                    && data.constraint == Some(argument)
                    && data.target.is_none()
                    && data.mapper.is_none()
        )
    {
        return Err(invalid());
    }

    match &interface.reference.object.instantiations {
        TypeCacheState::Allocated(cache)
            if cache.len() == 1 && cache.get(&type_list_key(&[])) == Some(&argument) =>
        {
            Ok(())
        }
        _ => Err(DirectGenericReferenceError::InvalidInstantiationCache(
            argument,
        )),
    }
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
    let tuple_target = match record.data() {
        TypeData::Tuple(_) => Some(reference),
        TypeData::TypeReference(data) => data.object.target.filter(|target| {
            matches!(
                store.type_payload(*target).map(TypeRecord::data),
                Some(TypeData::Tuple(_))
            )
        }),
        _ => None,
    };
    if let Some(target) = tuple_target {
        let shape = store
            .canonical_tuple_shape(reference)
            .map_err(|error| match error {
                TupleTypeError::InvalidTargetCache(target) => {
                    DirectGenericReferenceError::InvalidTarget(target)
                }
                TupleTypeError::InvalidInstantiationCache { target, instance } => {
                    DirectGenericReferenceError::InvalidCachedReference {
                        target,
                        reference: instance,
                    }
                }
                _ => DirectGenericReferenceError::InvalidCachedReference { target, reference },
            })?
            .ok_or(DirectGenericReferenceError::InvalidCachedReference { target, reference })?;
        active.push(reference);
        for argument in shape.element_types() {
            validate_reference_argument_graph(store, *argument, active, validated)?;
        }
        let popped = active
            .pop()
            .expect("a tuple argument owns one active validation frame");
        debug_assert_eq!(popped, reference);
        validated.insert(reference);
        return Ok(());
    }
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
        if arguments.is_empty() && matches!(record.data(), TypeData::Interface(_)) {
            if record.object_flags().contains(ObjectFlags::INTERFACE) {
                validate_nongeneric_interface_argument_origin(store, reference)?;
                validated.insert(reference);
                return Ok(());
            }
            if record.object_flags().contains(ObjectFlags::CLASS) {
                let owner = record
                    .symbol()
                    .filter(|owner| {
                        store
                            .symbol(*owner)
                            .is_some_and(|owner| owner.flags().contains(SymbolFlags::CLASS))
                    })
                    .ok_or(DirectGenericReferenceError::InvalidTarget(reference))?;
                if cached_class_type(store, owner)
                    .map_err(|_| DirectGenericReferenceError::InvalidTarget(reference))?
                    != Some(reference)
                {
                    return Err(DirectGenericReferenceError::InvalidTarget(reference));
                }
                validated.insert(reference);
                return Ok(());
            }
        }
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
            // Deferred-reference argument families remain opaque at this
            // direct class/interface boundary.
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
        if store.class_instance_super_view(*reference).is_some() {
            let invalid = || DirectGenericReferenceError::InvalidCachedReference {
                target: shape.target,
                reference: *reference,
            };
            let arguments = super::classes::source_class_super_reference_cache_entry(
                store,
                shape.target,
                *reference,
            )
            .ok_or_else(invalid)?;
            if *key != type_list_key(&arguments) {
                return Err(invalid());
            }
            let mut active = vec![*reference];
            for argument in arguments {
                validate_reference_argument_graph(store, argument, &mut active, &mut validated)?;
            }
            continue;
        }
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
    /// Returns the canonical `keyof any` constraint used by `Record` and
    /// other built-in mapped aliases.
    #[must_use]
    pub fn canonical_property_key_type(&self) -> Option<TypeId> {
        let bootstrap = self.intrinsic_bootstrap()?;
        let property_keys = bootstrap.string_number_symbol_type;
        let record = self.type_payload(property_keys)?;
        let TypeData::Union(union) = record.data() else {
            return None;
        };
        (union.union.types.len() == 3
            && union.union.types.contains(&bootstrap.string_type)
            && union.union.types.contains(&bootstrap.number_type)
            && union.union.types.contains(&bootstrap.es_symbol_type)
            && self
                .validate_cached_union_result(property_keys, None)
                .is_ok())
        .then_some(property_keys)
    }

    /// Checks whether a type satisfies the canonical property-key domain
    /// without allocating checker records or changing relation caches.
    #[must_use]
    pub fn is_valid_property_key_type(&self, type_: TypeId) -> bool {
        property_key_type_is_valid(self, type_, &mut HashSet::new())
    }

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

fn property_key_type_is_valid(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    active: &mut HashSet<TypeId>,
) -> bool {
    if !active.insert(type_) {
        return false;
    }
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let result = if record.flags().intersects(
        TypeFlags::ANY
            | TypeFlags::NEVER
            | TypeFlags::STRING_LIKE
            | TypeFlags::NUMBER_LIKE
            | TypeFlags::ES_SYMBOL_LIKE,
    ) {
        true
    } else {
        match record.data() {
            TypeData::Union(union) => union
                .union
                .types
                .iter()
                .all(|candidate| property_key_type_is_valid(store, *candidate, active)),
            TypeData::Intersection(intersection) => intersection
                .intersection
                .types
                .iter()
                .any(|candidate| property_key_type_is_valid(store, *candidate, active)),
            TypeData::TypeParameter(parameter) => parameter
                .constraint
                .filter(|constraint| {
                    store.intrinsic_bootstrap().is_none_or(|bootstrap| {
                        *constraint != bootstrap.no_constraint_type
                            && *constraint != bootstrap.circular_constraint_type
                    })
                })
                .is_some_and(|constraint| property_key_type_is_valid(store, constraint, active)),
            TypeData::Index(index) => store.intrinsic_bootstrap().is_some_and(|bootstrap| {
                index.target == bootstrap.any_type || index.target == bootstrap.never_type
            }),
            _ => false,
        }
    };
    active.remove(&type_);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeHost, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, SemanticStore, instantiate::instantiate_type_with_session,
        mapper::TypeMapper, production::GlobalMergeCompletion, signatures::ElementFlags,
        tuple_types::CanonicalTupleTypeRequest, type_records::TypeRecord,
    };
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, CheckFlags, EscapedName, SymbolData,
    };
    use ts_parser::{ParseResult, parse_source_file};

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn tuple_array_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/reference-tuples.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
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

    fn bound_nongeneric_this_argument() -> (CanonicalTypeMapperStore, TypeId, SemanticSymbolId) {
        let parsed = parse_source_file(concat!(
            "interface Element { self: this; } ",
            "interface HTMLElement extends Element {} ",
            "interface HTMLDivElement extends HTMLElement { ",
            "addEventListener(listener: (this: HTMLDivElement) => void): void; ",
            "} declare var HTMLDivElement: unknown;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(9_401);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source("\"/lib.dom.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    true,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let interface_declaration = |expected: &str| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::InterfaceDeclaration(interface) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                        return None;
                    };
                    (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap()
        };
        let declaration = interface_declaration("HTMLDivElement");
        assert_eq!(
            bound.contains_this(interface_declaration("Element")),
            Some(true)
        );
        assert_eq!(bound.contains_this(declaration), Some(false));
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let symbols = store
            .symbol_table(bound.locals(bound.source_file()).unwrap())
            .unwrap()
            .iter()
            .map(|(_, symbol)| symbol)
            .collect::<Vec<_>>();
        for symbol in symbols {
            store.merge_global_symbol(globals, symbol).unwrap();
        }
        let owner = store
            .get_merged_symbol(bound.symbol(declaration).unwrap())
            .unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let argument = store.get_declared_type_of_symbol(&host, owner).unwrap();
        (store, argument, owner)
    }

    fn source_interface_context<'a>(
        sources: &[(&'a ParseResult, FileId, CanonicalModuleState)],
    ) -> CanonicalCheckerContext<'a> {
        let mut binder = CanonicalBinder::new();
        for &(parsed, file, module) in sources {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/interface-{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        module,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            sources
                .iter()
                .map(|(parsed, file, _)| (*file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn source_interface_node(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name)?.data
                else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap()
    }

    fn reference_store_counts(store: &CanonicalTypeMapperStore) -> [usize; 5] {
        [
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.signature_len(),
            store.symbol_store().symbol_table_len(),
        ]
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the real mixed owner and each damage/restore pair together.
    fn mixed_global_interface_origins_keep_all_variables_and_the_real_this_type() {
        let library = parse_source_file(concat!(
            "interface Packet { self: this; library: number }\n",
            "declare var Packet: { marker: number };\n",
            "interface Other { self: this }\n",
        ));
        let augmentation = parse_source_file(concat!(
            "export {}; declare global {\n",
            "interface Packet { added: string }\n",
            "var Packet: { marker: number };\n",
            "}\n",
        ));
        let library_file = FileId::new(203_187);
        let augmentation_file = FileId::new(203_188);
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, default_library, module) in [
            (
                library_file,
                &library,
                "\"/lib/lib.packet-origin.d.ts\"",
                true,
                CanonicalModuleState::Script,
            ),
            (
                augmentation_file,
                &augmentation,
                "\"/types/packet-origin.d.ts\"",
                false,
                CanonicalModuleState::External,
            ),
        ] {
            assert!(parsed.diagnostics.is_empty());
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        default_library,
                        module,
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
                (library_file, &library.arena),
                (augmentation_file, &augmentation.arena),
            ],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let [owner, other] = ["Packet", "Other"].map(|name| {
            let store = context.store();
            store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .unwrap()
                .get_source(name)
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap()
        });
        let library_bound = context.file(library_file).unwrap().1.clone();
        let augmentation_bound = context.file(augmentation_file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&augmentation.arena, &augmentation_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let store = context.store_mut_for_test();
        let proof = store
            .source_global_interface_value_owner(owner)
            .unwrap()
            .unwrap();
        let declarations = proof.declarations().to_vec();
        let variables = proof.variables().to_vec();
        assert_eq!(variables.len(), 2);
        let selected = proof.value_declaration();
        assert_eq!(selected, variables[0]);
        let annotations = variables
            .iter()
            .map(|declaration| store.source_direct_type_annotation(*declaration).unwrap())
            .collect::<Vec<_>>();
        let argument = store.get_declared_type_of_symbol(&host, owner).unwrap();
        store.get_declared_type_of_symbol(&host, other).unwrap();
        let TypeData::Interface(interface) = store.type_payload(argument).unwrap().data() else {
            panic!("the mixed owner keeps its real interface identity")
        };
        let this_type = interface.this_type.unwrap();
        assert_eq!(interface.reference.object.target, Some(argument));
        assert_eq!(
            validate_nongeneric_interface_argument_origin(store, argument),
            Ok(())
        );
        let snapshot = |store: &CanonicalTypeMapperStore| {
            (
                reference_store_counts(store),
                store.checker_link_allocated_lengths(),
                store
                    .symbol(owner)
                    .unwrap()
                    .declarations()
                    .map(<[_]>::to_vec),
                store.symbol(owner).unwrap().value_declaration(),
                store.type_payload(argument).map(|record| {
                    let TypeData::Interface(data) = record.data() else {
                        panic!("the declared owner keeps its interface record");
                    };
                    (
                        record.id(),
                        record.flags(),
                        record.object_flags(),
                        record.symbol(),
                        record.alias(),
                        data.clone(),
                    )
                }),
                store.type_payload(this_type).map(|record| {
                    let TypeData::TypeParameter(data) = record.data() else {
                        panic!("the this type keeps its type-parameter record");
                    };
                    (
                        record.id(),
                        record.flags(),
                        record.object_flags(),
                        record.symbol(),
                        record.alias(),
                        data.clone(),
                    )
                }),
                annotations
                    .iter()
                    .map(|node| store.type_node_links(*node).cloned())
                    .collect::<Vec<_>>(),
            )
        };
        for damage in 0..3 {
            match damage {
                0 => assert!(
                    store.set_symbol_declarations(
                        owner,
                        Some(
                            declarations
                                .iter()
                                .copied()
                                .filter(|declaration| *declaration != variables[1])
                                .collect()
                        ),
                        Some(selected),
                    )
                ),
                1 => assert!(store.set_symbol_declarations(
                    owner,
                    Some(declarations.clone()),
                    Some(variables[1]),
                )),
                2 => assert!(store.set_type_symbol(this_type, Some(other))),
                _ => unreachable!(),
            }
            assert!(
                !super::super::object_members::source_interface_uses_legacy_single_script_value_owner(
                    store, owner,
                )
            );
            let damaged = snapshot(store);
            for _ in 0..2 {
                assert_eq!(
                    validate_nongeneric_interface_argument_origin(store, argument),
                    Err(DirectGenericReferenceError::InvalidTarget(argument))
                );
                assert_eq!(snapshot(store), damaged);
            }
            assert!(store.set_symbol_declarations(
                owner,
                Some(declarations.clone()),
                Some(selected)
            ));
            assert!(store.set_type_symbol(this_type, Some(owner)));
            let restored = snapshot(store);
            assert_eq!(
                validate_nongeneric_interface_argument_origin(store, argument),
                Ok(())
            );
            assert_eq!(snapshot(store), restored);
            assert!(
                annotations
                    .iter()
                    .all(|node| store.type_node_links(*node).is_none())
            );
            assert!(store.value_symbol_links(owner).is_none());
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn nongeneric_origin_keeps_the_original_single_script_variable_route() {
        let parsed =
            parse_source_file("interface Legacy { self: this } declare var Legacy: number;");
        let file = FileId::new(203_189);
        let mut context =
            source_interface_context(&[(&parsed, file, CanonicalModuleState::Script)]);
        let declaration = source_interface_node(&parsed, file, "Legacy");
        let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let owner = context.store().get_merged_symbol(raw).unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let store = context.store_mut_for_test();
        assert!(
            super::super::object_members::source_interface_uses_legacy_single_script_value_owner(
                store, owner,
            )
        );
        assert!(store.source_global_interface_value_owner(owner).is_err());
        let argument = store.get_declared_type_of_symbol(&host, owner).unwrap();
        let annotation = store
            .symbol(owner)
            .unwrap()
            .value_declaration()
            .and_then(|declaration| store.source_direct_type_annotation(declaration))
            .unwrap();
        let warm = (
            reference_store_counts(store),
            store.checker_link_allocated_lengths(),
            store.type_payload(argument).map(|record| {
                let TypeData::Interface(data) = record.data() else {
                    panic!("the declared owner keeps its interface record");
                };
                (
                    record.id(),
                    record.flags(),
                    record.object_flags(),
                    record.symbol(),
                    record.alias(),
                    data.clone(),
                )
            }),
        );
        for _ in 0..2 {
            assert_eq!(
                validate_nongeneric_interface_argument_origin(store, argument),
                Ok(())
            );
            assert_eq!(
                (
                    reference_store_counts(store),
                    store.checker_link_allocated_lengths(),
                    store.type_payload(argument).map(|record| {
                        let TypeData::Interface(data) = record.data() else {
                            panic!("the declared owner keeps its interface record");
                        };
                        (
                            record.id(),
                            record.flags(),
                            record.object_flags(),
                            record.symbol(),
                            record.alias(),
                            data.clone(),
                        )
                    })
                ),
                warm
            );
            assert!(store.type_node_links(annotation).is_none());
            assert!(store.value_symbol_links(owner).is_none());
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One real base cache checks valid views, damage, and ordinary arity.
    fn source_class_super_rows_keep_ordinary_references_and_exact_receiver_endpoints() {
        let parsed = parse_source_file(concat!(
            "class Base<T> { value: T; constructor(value: T) { this.value = value; } } ",
            "class TextBox extends Base<string> { constructor(value: string) { super(value); } } ",
            "class NumberBox extends Base<number> { constructor(value: number) { super(value); } } ",
            "declare const ordinary: Base<string>;",
        ));
        let file = FileId::new(9_426);
        let mut context = tuple_array_context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let bound = context.file(file).unwrap().1.clone();
        let class = |name| {
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::ClassDeclaration(data) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) =
                        &parsed.arena.get(data.name?).unwrap().data
                    else {
                        return None;
                    };
                    (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let owner = bound.symbol(declaration).unwrap();
            let instance = context
                .store()
                .declared_type_links(owner)
                .unwrap()
                .declared_type
                .unwrap();
            let TypeData::Interface(data) = context.store().type_payload(instance).unwrap().data()
            else {
                panic!("the parsed class keeps its actual origin")
            };
            (instance, data.this_type.unwrap())
        };
        let (base, _) = class("Base");
        let (text, text_this) = class("TextBox");
        let (numeric, numeric_this) = class("NumberBox");
        let annotation = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(data) = &record.data else {
                    return None;
                };
                data.type_
                    .map(|node| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let ordinary = context.get_type_from_type_node(annotation).unwrap();
        let store = context.store_mut_for_test();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let text_view = store
            .class_instance_super_view_for_instance(text)
            .unwrap()
            .receiver_type();
        let numeric_view = store
            .class_instance_super_view_for_instance(numeric)
            .unwrap()
            .receiver_type();
        assert_ne!(text_view, numeric_view);
        assert_eq!(
            super::super::classes::source_class_super_reference_cache_entry(store, base, text_view),
            Some(vec![string, text_this]),
        );
        assert_eq!(
            super::super::classes::source_class_super_reference_cache_entry(
                store,
                base,
                numeric_view
            ),
            Some(vec![number, numeric_this]),
        );
        let expected = DirectGenericReference {
            target: base,
            type_arguments: vec![string],
        };
        let warm = reference_store_counts(store);
        for _ in 0..2 {
            assert_eq!(
                validate_direct_generic_reference(store, ordinary),
                Ok(expected.clone())
            );
            assert_eq!(
                create_direct_generic_reference(store, base, &[string], ObjectFlags::NONE),
                Ok(ordinary),
            );
            assert_eq!(
                create_direct_generic_reference(
                    store,
                    base,
                    &[string, text_this],
                    ObjectFlags::NONE
                ),
                Err(DirectGenericReferenceError::TypeArgumentArity {
                    target: base,
                    expected: 1,
                    actual: 2
                }),
            );
            assert_eq!(reference_store_counts(store), warm);
        }
        let mapper = store
            .new_simple_type_mapper(text_this, numeric_this)
            .unwrap();
        for damage in 0..3 {
            match damage {
                0 => assert!(store.set_type_reference_resolution(
                    text_view,
                    None,
                    Some(vec![string, numeric_this])
                )),
                1 => assert!(store.set_type_parameter_resolution(
                    text_this,
                    Some(text),
                    None,
                    Some(mapper),
                    None
                )),
                2 => assert!(store.set_object_target_and_mapper(text_view, Some(numeric), None)),
                _ => unreachable!(),
            }
            let damaged = reference_store_counts(store);
            for _ in 0..2 {
                assert_eq!(
                    super::super::classes::source_class_super_reference_cache_entry(
                        store, base, text_view
                    ),
                    None,
                );
                assert_eq!(
                    validate_direct_generic_reference(store, ordinary),
                    Err(DirectGenericReferenceError::InvalidCachedReference {
                        target: base,
                        reference: text_view
                    }),
                );
                assert_eq!(reference_store_counts(store), damaged);
            }
            assert!(store.set_type_reference_resolution(
                text_view,
                None,
                Some(vec![string, text_this])
            ));
            assert!(store.set_type_parameter_resolution(text_this, Some(text), None, None, None));
            assert!(store.set_object_target_and_mapper(text_view, Some(base), None));
            assert_eq!(
                validate_direct_generic_reference(store, ordinary),
                Ok(expected.clone())
            );
        }
        let wrong_receiver_key = type_list_key(&[string, numeric_this]);
        assert!(store.try_reserve_object_instantiations(base, 1));
        assert_eq!(
            store.insert_object_instantiation(base, wrong_receiver_key, text_view),
            Some(text_view)
        );
        // The original view is still valid. Only the extra row has the wrong full key.
        assert_eq!(
            super::super::classes::source_class_super_reference_cache_entry(store, base, text_view),
            Some(vec![string, text_this]),
        );
        let damaged = reference_store_counts(store);
        for _ in 0..2 {
            assert_eq!(
                validate_direct_generic_reference(store, ordinary),
                Err(DirectGenericReferenceError::InvalidCachedReference {
                    target: base,
                    reference: text_view
                }),
            );
            assert_eq!(reference_store_counts(store), damaged);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Two real modules keep separate headers through full query replay.
    fn source_local_this_interfaces_keep_distinct_owners_and_warm_queries() {
        let first = parse_source_file(concat!(
            "export {}; interface Base<T> { value: T; tag: string } ",
            "interface Local extends Base<number> {} interface Wrapper<T> {} ",
            "type Result = Wrapper<Local>;",
        ));
        let second = parse_source_file(concat!(
            "export {}; interface Base<T> { value: T } interface Base<T> { tag: string } ",
            "interface Local extends Base<number> {} interface Wrapper<T> {} ",
            "type Result = Wrapper<Local>;",
        ));
        let sources = [
            (&first, FileId::new(9_410), CanonicalModuleState::External),
            (&second, FileId::new(9_411), CanonicalModuleState::External),
        ];
        let mut context = source_interface_context(&sources);
        let mut results = Vec::new();
        for (parsed, file, _) in sources {
            let declaration = source_interface_node(parsed, file, "Local");
            let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
            assert_eq!(context.store().symbol(owner).unwrap().parent(), None);
            assert_eq!(
                context
                    .store()
                    .symbol_store()
                    .source_binding_symbols(declaration),
                Some([Some(owner), None])
            );
            let globals = context.store().intrinsic_bootstrap().unwrap().globals;
            assert!(
                context
                    .store()
                    .symbol_table(globals)
                    .unwrap()
                    .get_source("Local")
                    .is_none()
            );
            let argument = context.get_declared_type_of_symbol(owner).unwrap();
            assert_eq!(
                validate_nongeneric_interface_argument_origin(context.store(), argument),
                Ok(())
            );
            let TypeData::Interface(header) =
                context.store().type_payload(argument).unwrap().data()
            else {
                unreachable!()
            };
            let header = header.clone();
            let this_type = header.this_type.unwrap();
            assert_eq!(
                header.all_type_parameters.as_deref(),
                Some(&[this_type][..])
            );
            assert_eq!(
                header.reference.resolved_type_arguments.as_deref(),
                Some(&[][..])
            );
            assert_eq!(header.reference.object.target, Some(argument));
            assert!(header.base_types_resolved && header.declared_members_resolved);
            let [base] = header.resolved_base_types.as_deref().unwrap() else {
                unreachable!()
            };
            let base_reference = validate_direct_generic_reference(context.store(), *base).unwrap();
            assert_eq!(
                base_reference.type_arguments,
                [context.store().intrinsic_bootstrap().unwrap().number_type]
            );
            let base_owner = context
                .file(file)
                .unwrap()
                .1
                .symbol(source_interface_node(parsed, file, "Base"))
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .type_payload(base_reference.target)
                    .unwrap()
                    .symbol(),
                Some(base_owner)
            );
            assert_eq!(
                context.store().type_payload(this_type).unwrap().symbol(),
                Some(owner)
            );
            assert!(
                matches!(context.store().type_payload(this_type).unwrap().data(), TypeData::TypeParameter(data) if data.is_this_type && data.constraint == Some(argument))
            );
            let body = parsed
                .arena
                .iter()
                .find_map(|(_, record)| match &record.data {
                    NodeData::TypeAliasDeclaration(alias) => {
                        Some(NodeRef::new(parsed.arena.id(), file, alias.type_))
                    }
                    _ => None,
                })
                .unwrap();
            let result = context.get_type_from_type_node(body).unwrap();
            assert_eq!(
                validate_direct_generic_reference(context.store(), result)
                    .unwrap()
                    .type_arguments,
                [argument]
            );
            let snapshot = reference_store_counts(context.store());
            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(argument));
            assert_eq!(context.get_type_from_type_node(body), Ok(result));
            assert_eq!(reference_store_counts(context.store()), snapshot);
            assert_eq!(
                context.store().type_payload(argument).unwrap().data(),
                &TypeData::Interface(header)
            );
            results.push((owner, argument, this_type, result));
        }
        assert_ne!(results[0].0, results[1].0);
        assert_ne!(results[0].1, results[1].1);
        assert_ne!(results[0].2, results[1].2);
        assert_ne!(results[0].3, results[1].3);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each damaged owner or header is rejected before reference publication.
    fn source_local_this_interface_origins_reject_owner_and_header_damage() {
        for damage in 0..7 {
            let parsed = parse_source_file(concat!(
                "export {}; interface Base<T> {} interface Local extends Base<number> {} ",
                "interface Local {} interface Wrapper<T> {}",
            ));
            let other = parse_source_file("export {}; interface Local { self: this; }");
            let file = FileId::new(9_412);
            let other_file = FileId::new(9_413);
            let sources = [
                (&parsed, file, CanonicalModuleState::External),
                (&other, other_file, CanonicalModuleState::External),
            ];
            let mut context = source_interface_context(&sources);
            let owner = context
                .file(file)
                .unwrap()
                .1
                .symbol(source_interface_node(&parsed, file, "Local"))
                .unwrap();
            let other_node = source_interface_node(&other, other_file, "Local");
            let other_owner = context
                .file(other_file)
                .unwrap()
                .1
                .symbol(other_node)
                .unwrap();
            let wrapper = context
                .file(file)
                .unwrap()
                .1
                .symbol(source_interface_node(&parsed, file, "Wrapper"))
                .unwrap();
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let store = context.store_mut_for_test();
            let argument = store.get_declared_type_of_symbol(&host, owner).unwrap();
            let target = store.get_declared_type_of_symbol(&host, wrapper).unwrap();
            assert_eq!(
                validate_nongeneric_interface_argument_origin(store, argument),
                Ok(())
            );
            let declarations = store
                .symbol(owner)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            assert_eq!(declarations.len(), 2);
            let TypeData::Interface(header) = store.type_payload(argument).unwrap().data() else {
                unreachable!()
            };
            let this_type = header.this_type.unwrap();
            let module = bound.symbol(bound.source_file()).unwrap();
            let string = store.intrinsic_bootstrap().unwrap().string_type;
            match damage {
                0 => {
                    assert!(store.set_symbol_declarations(owner, Some(vec![other_node]), None));
                }
                1 => {
                    assert!(store.set_symbol_declarations(
                        owner,
                        Some(vec![declarations[0]]),
                        None
                    ));
                }
                2 => {
                    assert!(store.set_symbol_flags(
                        module,
                        SymbolFlags::NAMESPACE_MODULE,
                        CheckFlags::NONE
                    ));
                }
                3 => {
                    assert!(store.set_symbol_flags(
                        owner,
                        SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
                        CheckFlags::NONE
                    ));
                }
                4 => {
                    assert!(!store.set_type_parameter_resolution(
                        this_type,
                        Some(string),
                        None,
                        None,
                        None
                    ));
                    assert!(store.set_type_parameter_resolution(
                        this_type,
                        Some(argument),
                        Some(string),
                        None,
                        None
                    ));
                }
                5 => {
                    let extra = store
                        .alloc_type_reference(ObjectFlags::NONE, Some(owner))
                        .unwrap();
                    assert!(store.set_object_target_and_mapper(extra, Some(argument), None));
                    assert!(store.set_type_reference_resolution(extra, None, Some(Vec::new())));
                    assert!(store.try_reserve_object_instantiations(argument, 1));
                    assert_eq!(
                        store.insert_object_instantiation(
                            argument,
                            type_list_key(&[string]),
                            extra
                        ),
                        Some(extra)
                    );
                }
                6 => {
                    assert!(store.set_type_symbol(this_type, Some(other_owner)));
                }
                _ => unreachable!(),
            }
            let expected = if damage == 5 {
                DirectGenericReferenceError::InvalidInstantiationCache(argument)
            } else {
                DirectGenericReferenceError::InvalidTarget(argument)
            };
            let snapshot = reference_store_counts(store);
            assert_eq!(
                validate_nongeneric_interface_argument_origin(store, argument),
                Err(expected.clone()),
                "damage {damage}"
            );
            assert_eq!(
                create_direct_generic_reference(store, target, &[argument], ObjectFlags::NONE),
                Err(expected),
                "damage {damage}"
            );
            assert_eq!(reference_store_counts(store), snapshot);
        }
    }

    #[test]
    fn source_local_origin_proof_does_not_replace_global_or_namespace_authority() {
        for namespace in [false, true] {
            let parsed = parse_source_file(if namespace {
                "export {}; namespace Scope { export interface Base<T> {} export interface Local extends Base<number> {} }"
            } else {
                "interface Base<T> {} interface Local extends Base<number> {}"
            });
            let file = FileId::new(9_414);
            let sources = [(
                &parsed,
                file,
                if namespace {
                    CanonicalModuleState::External
                } else {
                    CanonicalModuleState::Script
                },
            )];
            let mut context = source_interface_context(&sources);
            let declaration = source_interface_node(&parsed, file, "Local");
            let bound = context.file(file).unwrap().1.clone();
            let owner = context
                .store()
                .get_merged_symbol(bound.symbol(declaration).unwrap())
                .unwrap();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let store = context.store_mut_for_test();
            let argument = store.get_declared_type_of_symbol(&host, owner).unwrap();
            assert_eq!(store.symbol(owner).unwrap().flags(), SymbolFlags::INTERFACE);
            assert_eq!(
                validate_nongeneric_interface_argument_origin(store, argument),
                Ok(())
            );
            assert!(!source_local_interface_owner_is_exact(store, owner));
            let table = if namespace {
                store
                    .symbol(store.get_parent_of_symbol(owner).unwrap())
                    .unwrap()
                    .exports()
                    .unwrap()
            } else {
                store.intrinsic_bootstrap().unwrap().globals
            };
            let foreign = store
                .alloc_symbol(SymbolData::new(
                    SymbolFlags::INTERFACE,
                    EscapedName::source("Local"),
                ))
                .unwrap();
            assert_eq!(
                store.insert_symbol(table, EscapedName::source("Local"), foreign),
                Some(Some(owner))
            );
            let snapshot = reference_store_counts(store);
            assert_eq!(
                validate_nongeneric_interface_argument_origin(store, argument),
                Err(DirectGenericReferenceError::InvalidTarget(argument))
            );
            assert_eq!(reference_store_counts(store), snapshot);
            assert_eq!(
                store.insert_symbol(table, EscapedName::source("Local"), owner),
                Some(Some(foreign))
            );
            assert_eq!(
                validate_nongeneric_interface_argument_origin(store, argument),
                Ok(())
            );
            assert_eq!(reference_store_counts(store), snapshot);
        }
    }

    #[test]
    fn nongeneric_this_interface_is_a_canonical_generic_argument() {
        let (mut store, argument, owner) = bound_nongeneric_this_argument();
        let (outer, _) = generic_target(&mut store, "HTMLAttributes", ObjectFlags::INTERFACE, 1);
        let argument_record = store.type_payload(argument).unwrap();
        let TypeData::Interface(argument_data) = argument_record.data() else {
            panic!("the DOM argument must retain its declared interface origin")
        };
        assert_eq!(
            argument_record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK,
            ObjectFlags::INTERFACE | ObjectFlags::REFERENCE
        );
        assert_eq!(argument_data.reference.object.target, Some(argument));
        assert_eq!(
            argument_data.reference.resolved_type_arguments.as_deref(),
            Some(&[][..])
        );
        assert_eq!(argument_record.symbol(), Some(owner));
        assert_eq!(
            store.symbol(owner).unwrap().flags(),
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        );

        let cold_types = store.type_len();
        let reference = create_direct_generic_reference(
            &mut store,
            outer,
            &[argument],
            ObjectFlags::FROM_TYPE_NODE,
        )
        .unwrap();
        assert_eq!(store.type_len(), cold_types + 1);
        assert_eq!(
            validate_direct_generic_reference(&store, reference),
            Ok(DirectGenericReference {
                target: outer,
                type_arguments: vec![argument],
            })
        );
        assert_eq!(
            validate_direct_generic_reference(&store, argument),
            Err(DirectGenericReferenceError::NonGenericTarget(argument))
        );
        assert_eq!(
            create_direct_generic_reference(&mut store, argument, &[], ObjectFlags::NONE),
            Err(DirectGenericReferenceError::NonGenericTarget(argument))
        );

        let warm = (store.type_len(), store.mapper_len(), store.symbol_len());
        assert_eq!(
            create_direct_generic_reference(&mut store, outer, &[argument], ObjectFlags::NONE),
            Ok(reference)
        );
        assert_eq!(
            (store.type_len(), store.mapper_len(), store.symbol_len()),
            warm
        );
    }

    #[test]
    fn nongeneric_class_arguments_reuse_authenticated_origins_and_reject_poison() {
        let parsed = parse_source_file("class Payload {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = tuple_array_context(&parsed, FileId::new(9_402));
        let owner = context
            .store()
            .intrinsic_bootstrap()
            .and_then(|bootstrap| context.store().symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Payload"))
            .unwrap();
        let argument = context.get_declared_type_of_symbol(owner).unwrap();
        let (target, _) = generic_target(
            context.store_mut_for_test(),
            "Wrapper",
            ObjectFlags::INTERFACE,
            1,
        );
        let reference = create_direct_generic_reference(
            context.store_mut_for_test(),
            target,
            &[argument],
            ObjectFlags::FROM_TYPE_NODE,
        )
        .unwrap();
        assert_eq!(
            validate_direct_generic_reference(context.store(), reference),
            Ok(DirectGenericReference {
                target,
                type_arguments: vec![argument],
            }),
        );
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
        );
        assert_eq!(
            create_direct_generic_reference(
                context.store_mut_for_test(),
                target,
                &[argument],
                ObjectFlags::NONE,
            ),
            Ok(reference),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
            ),
            warm,
        );

        assert!(context.store_mut_for_test().set_symbol_flags(
            owner,
            SymbolFlags::INTERFACE,
            CheckFlags::NONE,
        ));
        assert_eq!(
            create_direct_generic_reference(
                context.store_mut_for_test(),
                target,
                &[argument],
                ObjectFlags::NONE,
            ),
            Err(DirectGenericReferenceError::InvalidTarget(argument)),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
            ),
            warm,
        );
    }

    #[test]
    fn nongeneric_this_interface_arguments_reject_forged_owner_and_cache_state() {
        for corruption in 0..5 {
            let (mut store, argument, owner) = bound_nongeneric_this_argument();
            let (outer, outer_parameters) =
                generic_target(&mut store, "HTMLAttributes", ObjectFlags::INTERFACE, 1);
            let string = store.intrinsic_bootstrap().unwrap().string_type;
            match corruption {
                0 => {
                    assert!(store.set_symbol_flags(owner, SymbolFlags::CLASS, CheckFlags::NONE));
                }
                1 => {
                    assert!(store.set_symbol_declarations(owner, None, None));
                }
                2 => {
                    let this_type = match store.type_payload(argument).unwrap().data() {
                        TypeData::Interface(interface) => interface.this_type.unwrap(),
                        _ => unreachable!("the fixture produces an interface origin"),
                    };
                    let mapper = store
                        .new_simple_type_mapper(outer_parameters[0], string)
                        .unwrap();
                    assert!(store.set_type_parameter_resolution(
                        this_type,
                        Some(argument),
                        None,
                        Some(mapper),
                        None,
                    ));
                }
                3 => {
                    let forged = store
                        .alloc_type_reference(ObjectFlags::NONE, Some(owner))
                        .unwrap();
                    assert!(store.set_object_target_and_mapper(forged, Some(argument), None));
                    assert!(store.set_type_reference_resolution(forged, None, Some(Vec::new())));
                    assert!(store.try_reserve_object_instantiations(argument, 1));
                    assert_eq!(
                        store.insert_object_instantiation(
                            argument,
                            type_list_key(&[string]),
                            forged,
                        ),
                        Some(forged)
                    );
                }
                4 => {
                    let forged = store
                        .alloc_symbol(SymbolData::new(
                            SymbolFlags::INTERFACE,
                            EscapedName::source("HTMLDivElement"),
                        ))
                        .unwrap();
                    let globals = store.intrinsic_bootstrap().unwrap().globals;
                    assert_eq!(
                        store
                            .insert_symbol(globals, EscapedName::source("HTMLDivElement"), forged,),
                        Some(Some(owner))
                    );
                }
                _ => unreachable!("the corruption matrix has five entries"),
            }
            let before = (store.type_len(), store.mapper_len(), store.symbol_len());
            let result =
                create_direct_generic_reference(&mut store, outer, &[argument], ObjectFlags::NONE);
            assert!(
                matches!(
                    result,
                    Err(
                        DirectGenericReferenceError::InvalidTarget(target)
                            | DirectGenericReferenceError::InvalidInstantiationCache(target)
                    )
                        if target == argument
                ),
                "corruption {corruption}: {result:?}"
            );
            assert_eq!(
                (store.type_len(), store.mapper_len(), store.symbol_len()),
                before,
                "corruption {corruption} published an outer reference"
            );
        }
    }

    #[test]
    fn synthetic_nongeneric_self_reference_cannot_masquerade_as_bound_interface() {
        let mut store = initialized_store();
        let (argument, parameters) =
            generic_target(&mut store, "Synthetic", ObjectFlags::INTERFACE, 0);
        assert!(parameters.is_empty());
        let (outer, _) = generic_target(&mut store, "Wrapper", ObjectFlags::INTERFACE, 1);
        let before = (store.type_len(), store.mapper_len(), store.symbol_len());

        assert_eq!(
            create_direct_generic_reference(&mut store, outer, &[argument], ObjectFlags::NONE),
            Err(DirectGenericReferenceError::InvalidTarget(argument))
        );
        assert_eq!(
            (store.type_len(), store.mapper_len(), store.symbol_len()),
            before
        );
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
    fn generic_references_authenticate_mutable_and_readonly_tuple_literal_arguments() {
        for (index, readonly) in [false, true].into_iter().enumerate() {
            let parsed = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context =
                tuple_array_context(&parsed, FileId::new(9_420 + u32::try_from(index).unwrap()));
            let global_types = context.global_types().clone();
            let store = context.store_mut_for_test();
            let (outer, _) = generic_target(store, "Wrapper", ObjectFlags::INTERFACE, 1);
            let (string, number) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.number_type)
            };
            let infos = [
                store
                    .create_tuple_element_info(ElementFlags::REQUIRED, None)
                    .unwrap(),
                store
                    .create_tuple_element_info(ElementFlags::REQUIRED, None)
                    .unwrap(),
            ];
            let tuple = store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    &[string, number],
                    &infos,
                    readonly,
                ))
                .unwrap();
            let literal = store
                .create_array_literal_type(&global_types, tuple)
                .unwrap();
            let empty = store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&[], &[], readonly))
                .unwrap();
            let empty_literal = store
                .create_array_literal_type(&global_types, empty)
                .unwrap();

            for argument in [tuple, literal, empty, empty_literal] {
                let shape = store.canonical_tuple_shape(argument).unwrap().unwrap();
                assert_eq!(shape.is_readonly(), readonly);
                let reference = create_direct_generic_reference(
                    store,
                    outer,
                    &[argument],
                    ObjectFlags::FROM_TYPE_NODE,
                )
                .unwrap();
                assert_eq!(
                    validate_direct_generic_reference(store, reference),
                    Ok(DirectGenericReference {
                        target: outer,
                        type_arguments: vec![argument],
                    })
                );
                let warm = (
                    store.type_len(),
                    store.mapper_len(),
                    store.symbol_len(),
                    store.relation_state_snapshot(),
                );
                assert_eq!(
                    create_direct_generic_reference(store, outer, &[argument], ObjectFlags::NONE),
                    Ok(reference)
                );
                assert_eq!(
                    (
                        store.type_len(),
                        store.mapper_len(),
                        store.symbol_len(),
                        store.relation_state_snapshot(),
                    ),
                    warm
                );
            }
        }
    }

    #[test]
    fn malformed_tuple_argument_graphs_do_not_publish_outer_references() {
        for corruption in 0..4 {
            let parsed = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context = tuple_array_context(
                &parsed,
                FileId::new(9_430 + u32::try_from(corruption).unwrap()),
            );
            let global_types = context.global_types().clone();
            let store = context.store_mut_for_test();
            let (outer, _) = generic_target(store, "Wrapper", ObjectFlags::INTERFACE, 1);
            let (string, number) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.number_type)
            };
            let info = store
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap();
            let tuple = store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    &[string],
                    &[info],
                    true,
                ))
                .unwrap();
            let literal = store
                .create_array_literal_type(&global_types, tuple)
                .unwrap();
            let target = store
                .canonical_tuple_shape(tuple)
                .unwrap()
                .unwrap()
                .target();
            let (argument, expected) = match corruption {
                0 => {
                    let this_type = match store.type_payload(target).unwrap().data() {
                        TypeData::Tuple(tuple) => tuple.interface.this_type.unwrap(),
                        _ => unreachable!("tuple references retain tuple targets"),
                    };
                    assert!(store.set_resolved_base_constraint(this_type, Some(number)));
                    (tuple, DirectGenericReferenceError::InvalidTarget(target))
                }
                1 => {
                    assert!(store.set_type_reference_resolution(tuple, None, Some(vec![number])));
                    (
                        tuple,
                        DirectGenericReferenceError::InvalidCachedReference {
                            target,
                            reference: tuple,
                        },
                    )
                }
                2 => {
                    assert!(store.set_type_reference_resolution(literal, None, Some(vec![number])));
                    (
                        literal,
                        DirectGenericReferenceError::InvalidCachedReference {
                            target,
                            reference: literal,
                        },
                    )
                }
                3 => {
                    assert_eq!(
                        store
                            .derived_types
                            .array_literal_types
                            .insert(tuple, number),
                        Some(literal)
                    );
                    (
                        literal,
                        DirectGenericReferenceError::InvalidCachedReference {
                            target,
                            reference: literal,
                        },
                    )
                }
                _ => unreachable!("the tuple corruption matrix has four entries"),
            };
            let before = (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.relation_state_snapshot(),
            );

            assert_eq!(
                create_direct_generic_reference(store, outer, &[argument], ObjectFlags::NONE),
                Err(expected),
                "corruption {corruption}",
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.mapper_len(),
                    store.symbol_len(),
                    store.symbol_store().symbol_table_len(),
                    store.relation_state_snapshot(),
                ),
                before,
                "corruption {corruption} published an outer reference",
            );
        }
    }

    #[test]
    fn tuple_arguments_revalidate_nested_generic_reference_caches() {
        let mut store = initialized_store();
        let (outer, _) = generic_target(&mut store, "Wrapper", ObjectFlags::INTERFACE, 1);
        let (inner, parameters) = generic_target(&mut store, "Inner", ObjectFlags::INTERFACE, 1);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let nested =
            create_direct_generic_reference(&mut store, inner, &[string], ObjectFlags::NONE)
                .unwrap();
        let info = store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let tuple = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&[nested], &[info], true))
            .unwrap();
        let reference =
            create_direct_generic_reference(&mut store, outer, &[tuple], ObjectFlags::NONE)
                .unwrap();
        assert_eq!(
            validate_direct_generic_reference(&store, reference),
            Ok(DirectGenericReference {
                target: outer,
                type_arguments: vec![tuple],
            })
        );

        let mapper = store.new_simple_type_mapper(parameters[0], number).unwrap();
        assert!(store.set_object_target_and_mapper(nested, Some(inner), Some(mapper)));
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            create_direct_generic_reference(&mut store, outer, &[tuple], ObjectFlags::NONE),
            Err(DirectGenericReferenceError::InvalidCachedReference {
                target: inner,
                reference: nested,
            })
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.relation_state_snapshot(),
            ),
            before
        );
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
    fn canonical_property_key_constraint_accepts_record_key_families() {
        let mut store = initialized_store();
        let (keys, any, string, number, symbol, boolean, bigint, unknown, never) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_number_symbol_type,
                bootstrap.any_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.es_symbol_type,
                bootstrap.boolean_type,
                bootstrap.bigint_type,
                bootstrap.unknown_type,
                bootstrap.never_type,
            )
        };
        let unicode = store
            .regular_string_literal_type("i\u{307}spanyol".to_owned())
            .unwrap();
        let union = store.literal_union_type(&[unicode, number], None).unwrap();
        let parameter = store.alloc_type_parameter(None).unwrap();
        assert!(store.set_type_parameter_resolution(parameter, Some(keys), None, None, None));
        let keyof_any = store
            .alloc_index_type(any, crate::semantic::signatures::IndexFlags::NONE)
            .unwrap();
        let keyof_unknown = store
            .alloc_index_type(unknown, crate::semantic::signatures::IndexFlags::NONE)
            .unwrap();

        assert_eq!(store.canonical_property_key_type(), Some(keys));
        for valid in [
            keys, any, string, number, symbol, unicode, union, parameter, never, keyof_any,
        ] {
            assert!(store.is_valid_property_key_type(valid));
        }
        for invalid in [boolean, bigint, unknown, keyof_unknown] {
            assert!(!store.is_valid_property_key_type(invalid));
        }
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
