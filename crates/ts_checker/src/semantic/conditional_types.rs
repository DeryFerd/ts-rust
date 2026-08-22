//! Canonical conditional-type roots, distribution, and bounded inference.
//!
//! This module follows `getTypeFromConditionalTypeNode`, `getConditionalType`,
//! and `getConditionalTypeInstantiation` in the pinned TypeScript Go checker.
//! Syntax planning and branch resolution remain with the type-node owner.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeRef, SyntaxKind};
use xxhash_rust::xxh3::Xxh3;

use super::{
    CanonicalGlobalTypes, ConditionalRootId, RelationUnavailable, SemanticSymbolId, SignatureId,
    TypeAliasId, TypeId, TypeMapperId,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    constraints::{self, ConstraintError},
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession, canonical_anonymous_union,
        instantiate_type_with_session, instantiate_type_with_vector_and_session,
    },
    mapper::CanonicalTypeMapperStore,
    signatures::{ElementFlags, Signature, TupleElementInfo},
    store::SourceNodeParent,
    template_types::TemplateTypeError,
    tuple_types::{CanonicalTupleTypeRequest, TupleTypeError},
    type_records::{
        CacheHashKey, ConditionalTypeData, LiteralValue, TypeCacheState, TypeData, TypeRecord,
    },
    types::TypeFlags,
};

/// Upstream stops an aliased conditional tail-recursion chain at this count.
pub(super) const CONDITIONAL_TAIL_RECURSION_LIMIT: usize = 1_000;

/// The resolved branches supplied by the type-node query owner.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConditionalTypeBranches {
    pub true_type: TypeId,
    pub false_type: TypeId,
}

/// Fully validated inputs needed to create one canonical conditional root.
#[derive(Clone, Copy, Debug)]
pub(super) struct ConditionalTypeRequest<'a> {
    pub node: NodeRef,
    pub check_type: TypeId,
    pub extends_type: TypeId,
    pub branches: ConditionalTypeBranches,
    pub infer_type_parameters: &'a [TypeId],
    pub outer_type_parameters: &'a [TypeId],
    pub alias: Option<TypeAliasId>,
}

/// Inputs for one conditional-root instantiation.
#[derive(Clone, Copy, Debug)]
pub(super) struct ConditionalTypeInstantiation<'a> {
    pub conditional_type: TypeId,
    pub type_arguments: &'a [TypeId],
    pub branches: ConditionalTypeBranches,
    pub alias: Option<TypeAliasId>,
    pub for_constraint: bool,
}

/// Missing dependencies, invalid canonical records, or bounded evaluation.
#[derive(Debug, PartialEq)]
pub(super) enum ConditionalTypeError {
    MissingBootstrap,
    InvalidNode(NodeRef),
    InvalidType(TypeId),
    InvalidTypeParameter(TypeId),
    DuplicateTypeParameter(TypeId),
    InvalidAlias(TypeAliasId),
    InvalidRoot(ConditionalRootId),
    InvalidConditional(TypeId),
    InvalidMapper(TypeMapperId),
    InvalidInstantiationArity { expected: usize, actual: usize },
    InvalidInstantiationCache(ConditionalRootId),
    InvalidTypeNodeCache(NodeRef),
    InvalidConditionalResolution(TypeId),
    InvalidSignature(SignatureId),
    UnsupportedInference { source: TypeId, target: TypeId },
    TailRecursionLimit { count: usize, limit: usize },
    Instantiation(InstantiationError),
    Constraint(Box<ConstraintError>),
    Relation(RelationUnavailable),
    Template(TemplateTypeError),
    Tuple(TupleTypeError),
    Union(LiteralTypeCacheError),
}

impl std::fmt::Display for ConditionalTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingBootstrap => {
                formatter.write_str("conditional types require intrinsic checker bootstrap")
            }
            Self::InvalidNode(node) => write!(formatter, "invalid conditional node {node:?}"),
            Self::InvalidType(type_) => write!(formatter, "invalid conditional type {type_:?}"),
            Self::InvalidTypeParameter(type_) => {
                write!(formatter, "invalid conditional type parameter {type_:?}")
            }
            Self::DuplicateTypeParameter(type_) => {
                write!(formatter, "duplicate conditional type parameter {type_:?}")
            }
            Self::InvalidAlias(alias) => write!(formatter, "invalid conditional alias {alias:?}"),
            Self::InvalidRoot(root) => write!(formatter, "invalid conditional root {root:?}"),
            Self::InvalidConditional(type_) => {
                write!(formatter, "type {type_:?} is not a valid conditional")
            }
            Self::InvalidMapper(mapper) => {
                write!(formatter, "invalid conditional type mapper {mapper:?}")
            }
            Self::InvalidInstantiationArity { expected, actual } => write!(
                formatter,
                "conditional instantiation expects {expected} arguments, received {actual}"
            ),
            Self::InvalidInstantiationCache(root) => {
                write!(formatter, "conditional root {root:?} has an invalid cache")
            }
            Self::InvalidTypeNodeCache(node) => {
                write!(formatter, "conditional node {node:?} has an invalid cache")
            }
            Self::InvalidConditionalResolution(type_) => {
                write!(
                    formatter,
                    "conditional type {type_:?} has invalid resolution caches"
                )
            }
            Self::InvalidSignature(signature) => {
                write!(
                    formatter,
                    "conditional inference requires signature {signature:?}"
                )
            }
            Self::UnsupportedInference { source, target } => write!(
                formatter,
                "conditional inference from {source:?} to {target:?} is not supported"
            ),
            Self::TailRecursionLimit { count, limit } => write!(
                formatter,
                "conditional tail recursion count {count} reached limit {limit}"
            ),
            Self::Instantiation(error) => error.fmt(formatter),
            Self::Constraint(error) => error.fmt(formatter),
            Self::Relation(error) => error.fmt(formatter),
            Self::Template(error) => error.fmt(formatter),
            Self::Tuple(error) => error.fmt(formatter),
            Self::Union(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ConditionalTypeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Instantiation(error) => Some(error),
            Self::Constraint(error) => Some(error.as_ref()),
            Self::Relation(error) => Some(error),
            Self::Template(error) => Some(error),
            Self::Tuple(error) => Some(error),
            Self::Union(error) => Some(error),
            _ => None,
        }
    }
}

impl From<InstantiationError> for ConditionalTypeError {
    fn from(error: InstantiationError) -> Self {
        Self::Instantiation(error)
    }
}

impl From<RelationUnavailable> for ConditionalTypeError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<ConstraintError> for ConditionalTypeError {
    fn from(error: ConstraintError) -> Self {
        Self::Constraint(Box::new(error))
    }
}

impl From<TemplateTypeError> for ConditionalTypeError {
    fn from(error: TemplateTypeError) -> Self {
        Self::Template(error)
    }
}

impl From<TupleTypeError> for ConditionalTypeError {
    fn from(error: TupleTypeError) -> Self {
        Self::Tuple(error)
    }
}

impl From<LiteralTypeCacheError> for ConditionalTypeError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Union(error)
    }
}

/// Creates the root even when a concrete conditional immediately resolves.
pub(super) fn get_type_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    request: ConditionalTypeRequest<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<TypeId, ConditionalTypeError> {
    validate_request(store, request)?;
    if let Some(cached) = store
        .type_node_links(request.node)
        .and_then(|links| links.resolved_type)
    {
        return validate_cached_conditional(store, request, cached);
    }

    let distributive = matches!(
        store.type_payload(request.check_type).map(TypeRecord::data),
        Some(TypeData::TypeParameter(_))
    );
    let root = store
        .alloc_conditional_root(
            request.node,
            request.check_type,
            request.extends_type,
            distributive,
            (!request.infer_type_parameters.is_empty())
                .then(|| request.infer_type_parameters.to_vec()),
            (!request.outer_type_parameters.is_empty())
                .then(|| request.outer_type_parameters.to_vec()),
            request.alias,
        )
        .ok_or(ConditionalTypeError::InvalidNode(request.node))?;

    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let result = evaluate_conditional(
        store,
        root,
        request.branches,
        &[],
        &[],
        global_types,
        false,
        &mut session,
        0,
    )?;

    if !request.outer_type_parameters.is_empty() {
        let key = conditional_type_key(store, request.outer_type_parameters, None, false)?;
        if !store.set_conditional_root_instantiations(
            root,
            TypeCacheState::Allocated(HashMap::from([(key, result)])),
        ) {
            return Err(ConditionalTypeError::InvalidInstantiationCache(root));
        }
    }

    let mut links = store
        .type_node_links(request.node)
        .cloned()
        .unwrap_or_default();
    links.resolved_type = Some(result);
    if !store.set_type_node_links(request.node, links) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
    }
    Ok(result)
}

/// Instantiates a deferred root and distributes a naked parameter over unions.
pub(super) fn get_conditional_type_instantiation(
    store: &mut CanonicalTypeMapperStore,
    request: ConditionalTypeInstantiation<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    get_conditional_type_instantiation_with_tail_count(store, request, global_types, session, 0)
}

/// Resolves the true branch only when its canonical lazy cache is requested.
pub(super) fn get_true_type_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    resolve_conditional_branch(
        store,
        conditional,
        branches,
        ConditionalBranchKind::True,
        global_types,
        session,
    )
}

/// Resolves the false branch only when its canonical lazy cache is requested.
pub(super) fn get_false_type_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    resolve_conditional_branch(
        store,
        conditional,
        branches,
        ConditionalBranchKind::False,
        global_types,
        session,
    )
}

/// Resolves the true branch through the inference mapper when one exists.
pub(super) fn get_inferred_true_type_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    if conditional_snapshot(store, conditional)?
        .combined_mapper
        .is_none()
    {
        let resolved = get_true_type_from_conditional_type(
            store,
            conditional,
            branches,
            global_types,
            session,
        )?;
        let mut data = conditional_snapshot(store, conditional)?;
        if data.resolved_inferred_true_type != Some(resolved) {
            data.resolved_inferred_true_type = Some(resolved);
            publish_conditional_snapshot(store, conditional, &data)?;
        }
        return Ok(resolved);
    }
    resolve_conditional_branch(
        store,
        conditional,
        branches,
        ConditionalBranchKind::InferredTrue,
        global_types,
        session,
    )
}

/// Computes the pinned default constraint, excluding a single `any` branch.
pub(super) fn get_default_constraint_of_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    let data = conditional_snapshot(store, conditional)?;
    if let Some(cached) = data.resolved_default_constraint {
        validate_owned_type(store, cached)?;
        return Ok(cached);
    }

    let mut owned_session = InstantiationSession::new(InstantiationLimits::default());
    let session = session.unwrap_or(&mut owned_session);
    let true_type = get_inferred_true_type_from_conditional_type(
        store,
        conditional,
        branches,
        global_types,
        Some(session),
    )?;
    let false_type = get_false_type_from_conditional_type(
        store,
        conditional,
        branches,
        global_types,
        Some(session),
    )?;
    let result = if type_flags(store, true_type)?.intersects(TypeFlags::ANY) {
        false_type
    } else if type_flags(store, false_type)?.intersects(TypeFlags::ANY) {
        true_type
    } else {
        union_result(store, &[true_type, false_type], global_types)?
    };
    let mut data = conditional_snapshot(store, conditional)?;
    data.resolved_default_constraint = Some(result);
    publish_conditional_snapshot(store, conditional, &data)?;
    Ok(result)
}

/// Instantiates a distributive conditional with its checked parameter's constraint.
pub(super) fn get_constraint_of_distributive_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    let data = conditional_snapshot(store, conditional)?;
    let no_constraint = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?
        .no_constraint_type;
    if let Some(cached) = data.resolved_constraint_of_distributive {
        validate_owned_type(store, cached)?;
        return Ok((cached != no_constraint).then_some(cached));
    }

    let (distributive, root_check, parameters) = {
        let root = store
            .conditional_root(data.root)
            .ok_or(ConditionalTypeError::InvalidRoot(data.root))?;
        (
            root.is_distributive(),
            root.check_type(),
            root.outer_type_parameters().unwrap_or_default().to_vec(),
        )
    };
    let mut result = None;
    if distributive {
        let constraint = match constraints::get_constraint_of_type(store, data.check_type) {
            Ok(constraint) => constraint,
            Err(ConstraintError::UnresolvedTypeParameter(type_)) if type_ == data.check_type => {
                None
            }
            Err(error) => return Err(error.into()),
        };
        if let Some(constraint) = constraint
            && constraint != data.check_type
        {
            let mut owned_session = InstantiationSession::new(InstantiationLimits::default());
            let session = session.unwrap_or(&mut owned_session);
            let mut arguments = Vec::with_capacity(parameters.len());
            for parameter in parameters {
                let argument = if parameter == root_check {
                    constraint
                } else {
                    map_type_with_stored_mapper(
                        store,
                        parameter,
                        data.mapper,
                        global_types,
                        session,
                    )?
                };
                arguments.push(argument);
            }
            let instantiated = get_conditional_type_instantiation(
                store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &arguments,
                    branches,
                    alias: None,
                    for_constraint: true,
                },
                global_types,
                Some(session),
            )?;
            if !is_never(store, instantiated)? {
                result = Some(instantiated);
            }
        }
    }

    let mut data = conditional_snapshot(store, conditional)?;
    data.resolved_constraint_of_distributive = Some(result.unwrap_or(no_constraint));
    publish_conditional_snapshot(store, conditional, &data)?;
    Ok(result)
}

/// Uses the distributive constraint first, then the pinned default constraint.
pub(super) fn get_constraint_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    let mut owned_session = InstantiationSession::new(InstantiationLimits::default());
    let session = session.unwrap_or(&mut owned_session);
    if let Some(distributive) = get_constraint_of_distributive_conditional_type(
        store,
        conditional,
        branches,
        global_types,
        Some(session),
    )? {
        return Ok(distributive);
    }
    get_default_constraint_of_conditional_type(
        store,
        conditional,
        branches,
        global_types,
        Some(session),
    )
}

/// Returns resolved branch identities without forcing an unavailable syntax query.
pub(super) fn cached_conditional_branches(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> Result<Option<ConditionalTypeBranches>, ConditionalTypeError> {
    let data = conditional_snapshot(store, conditional)?;
    let Some(true_type) = data.resolved_inferred_true_type.or(data.resolved_true_type) else {
        return Ok(None);
    };
    let Some(false_type) = data.resolved_false_type else {
        return Ok(None);
    };
    let branches = ConditionalTypeBranches {
        true_type,
        false_type,
    };
    validate_branch_types(store, branches)?;
    Ok(Some(branches))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConditionalBranchKind {
    True,
    False,
    InferredTrue,
}

fn resolve_conditional_branch(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    branch: ConditionalBranchKind,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    validate_branch_types(store, branches)?;
    let data = conditional_snapshot(store, conditional)?;
    let (cached, source, mapper) = match branch {
        ConditionalBranchKind::True => (data.resolved_true_type, branches.true_type, data.mapper),
        ConditionalBranchKind::False => {
            (data.resolved_false_type, branches.false_type, data.mapper)
        }
        ConditionalBranchKind::InferredTrue => (
            data.resolved_inferred_true_type,
            branches.true_type,
            data.combined_mapper.or(data.mapper),
        ),
    };
    if let Some(cached) = cached {
        validate_owned_type(store, cached)?;
        return Ok(cached);
    }

    let mut owned_session = InstantiationSession::new(InstantiationLimits::default());
    let session = session.unwrap_or(&mut owned_session);
    let resolved = map_type_with_stored_mapper(store, source, mapper, global_types, session)?;
    let mut data = conditional_snapshot(store, conditional)?;
    match branch {
        ConditionalBranchKind::True => data.resolved_true_type = Some(resolved),
        ConditionalBranchKind::False => data.resolved_false_type = Some(resolved),
        ConditionalBranchKind::InferredTrue => {
            data.resolved_inferred_true_type = Some(resolved);
            if data.combined_mapper.is_none() {
                data.resolved_true_type = Some(resolved);
            }
        }
    }
    publish_conditional_snapshot(store, conditional, &data)?;
    Ok(resolved)
}

fn conditional_snapshot(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> Result<ConditionalTypeData, ConditionalTypeError> {
    match store.type_payload(conditional).map(TypeRecord::data) {
        Some(TypeData::Conditional(data)) => Ok(data.clone()),
        _ => Err(ConditionalTypeError::InvalidConditional(conditional)),
    }
}

fn publish_conditional_snapshot(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    data: &ConditionalTypeData,
) -> Result<(), ConditionalTypeError> {
    if store.set_conditional_resolution(
        conditional,
        data.resolved_true_type,
        data.resolved_false_type,
        data.resolved_inferred_true_type,
        data.resolved_default_constraint,
        data.resolved_constraint_of_distributive,
        data.mapper,
        data.combined_mapper,
    ) {
        Ok(())
    } else {
        Err(ConditionalTypeError::InvalidConditionalResolution(
            conditional,
        ))
    }
}

fn get_conditional_type_instantiation_with_tail_count(
    store: &mut CanonicalTypeMapperStore,
    request: ConditionalTypeInstantiation<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
    tail_count: usize,
) -> Result<TypeId, ConditionalTypeError> {
    if tail_count >= CONDITIONAL_TAIL_RECURSION_LIMIT {
        return Err(ConditionalTypeError::TailRecursionLimit {
            count: tail_count,
            limit: CONDITIONAL_TAIL_RECURSION_LIMIT,
        });
    }
    validate_branch_types(store, request.branches)?;
    if let Some(alias) = request.alias
        && store.type_alias(alias).is_none()
    {
        return Err(ConditionalTypeError::InvalidAlias(alias));
    }

    let (root, existing_mapper) = match store
        .type_payload(request.conditional_type)
        .map(TypeRecord::data)
    {
        Some(TypeData::Conditional(data)) => (data.root, data.mapper),
        _ => {
            return Err(ConditionalTypeError::InvalidConditional(
                request.conditional_type,
            ));
        }
    };
    if let Some(mapper) = existing_mapper
        && store.mapper_payload(mapper).is_none()
    {
        return Err(ConditionalTypeError::InvalidMapper(mapper));
    }
    let (outer_parameters, check_type, distributive, cached_values) = {
        let root_record = store
            .conditional_root(root)
            .ok_or(ConditionalTypeError::InvalidRoot(root))?;
        let parameters = root_record
            .outer_type_parameters()
            .unwrap_or_default()
            .to_vec();
        let cache = match root_record.instantiations() {
            TypeCacheState::Allocated(cache) if !parameters.is_empty() => cache.clone(),
            TypeCacheState::Unallocated if parameters.is_empty() => HashMap::new(),
            _ => return Err(ConditionalTypeError::InvalidInstantiationCache(root)),
        };
        (
            parameters,
            root_record.check_type(),
            root_record.is_distributive(),
            cache,
        )
    };
    if outer_parameters.is_empty() {
        if !request.type_arguments.is_empty() {
            return Err(ConditionalTypeError::InvalidInstantiationArity {
                expected: 0,
                actual: request.type_arguments.len(),
            });
        }
        return Ok(request.conditional_type);
    }
    if outer_parameters.len() != request.type_arguments.len() {
        return Err(ConditionalTypeError::InvalidInstantiationArity {
            expected: outer_parameters.len(),
            actual: request.type_arguments.len(),
        });
    }
    for argument in request.type_arguments {
        validate_owned_type(store, *argument)?;
    }

    let key = conditional_type_key(
        store,
        request.type_arguments,
        request.alias,
        request.for_constraint,
    )?;
    if let Some(cached) = cached_values.get(&key).copied() {
        validate_cached_instantiation(
            store,
            root,
            cached,
            &outer_parameters,
            request.type_arguments,
        )?;
        return Ok(cached);
    }

    let mut owned_session = InstantiationSession::new(InstantiationLimits::default());
    let session = session.unwrap_or(&mut owned_session);
    let mapped_check = map_type(
        store,
        check_type,
        &outer_parameters,
        request.type_arguments,
        global_types,
        session,
    )?;

    let result = if distributive && mapped_check != check_type {
        match store.type_payload(mapped_check).map(TypeRecord::data) {
            Some(TypeData::Union(union)) => {
                let constituents = union.union.types.clone();
                let Some(check_index) = outer_parameters
                    .iter()
                    .position(|parameter| *parameter == check_type)
                else {
                    return Err(ConditionalTypeError::InvalidRoot(root));
                };
                let mut results = Vec::with_capacity(constituents.len());
                for constituent in constituents {
                    let mut arguments = request.type_arguments.to_vec();
                    arguments[check_index] = constituent;
                    results.push(evaluate_conditional(
                        store,
                        root,
                        request.branches,
                        &outer_parameters,
                        &arguments,
                        global_types,
                        request.for_constraint,
                        session,
                        tail_count,
                    )?);
                }
                union_result(store, &results, global_types)?
            }
            Some(_) if is_never(store, mapped_check)? => mapped_check,
            Some(_) => evaluate_conditional(
                store,
                root,
                request.branches,
                &outer_parameters,
                request.type_arguments,
                global_types,
                request.for_constraint,
                session,
                tail_count,
            )?,
            None => return Err(ConditionalTypeError::InvalidType(mapped_check)),
        }
    } else {
        evaluate_conditional(
            store,
            root,
            request.branches,
            &outer_parameters,
            request.type_arguments,
            global_types,
            request.for_constraint,
            session,
            tail_count,
        )?
    };

    let mut cache = match store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?
        .instantiations()
    {
        TypeCacheState::Allocated(cache) => cache.clone(),
        TypeCacheState::Unallocated => {
            return Err(ConditionalTypeError::InvalidInstantiationCache(root));
        }
    };
    if let Some(previous) = cache.insert(key, result)
        && previous != result
    {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    if !store.set_conditional_root_instantiations(root, TypeCacheState::Allocated(cache)) {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    Ok(result)
}

#[allow(clippy::too_many_arguments)] // Mirrors the upstream conditional evaluation inputs.
fn evaluate_conditional(
    store: &mut CanonicalTypeMapperStore,
    root: ConditionalRootId,
    branches: ConditionalTypeBranches,
    mapped_parameters: &[TypeId],
    type_arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    for_constraint: bool,
    session: &mut InstantiationSession,
    tail_count: usize,
) -> Result<TypeId, ConditionalTypeError> {
    if tail_count >= CONDITIONAL_TAIL_RECURSION_LIMIT {
        return Err(ConditionalTypeError::TailRecursionLimit {
            count: tail_count,
            limit: CONDITIONAL_TAIL_RECURSION_LIMIT,
        });
    }
    let (root_check, root_extends, infer_parameters) = {
        let record = store
            .conditional_root(root)
            .ok_or(ConditionalTypeError::InvalidRoot(root))?;
        (
            record.check_type(),
            record.extends_type(),
            record.infer_type_parameters().unwrap_or_default().to_vec(),
        )
    };
    let check_type = map_type(
        store,
        root_check,
        mapped_parameters,
        type_arguments,
        global_types,
        session,
    )?;
    let extends_type = map_type(
        store,
        root_extends,
        mapped_parameters,
        type_arguments,
        global_types,
        session,
    )?;

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    if check_type == bootstrap.error_type || extends_type == bootstrap.error_type {
        return Ok(bootstrap.error_type);
    }
    if check_type == bootstrap.wildcard_type || extends_type == bootstrap.wildcard_type {
        return Ok(bootstrap.wildcard_type);
    }

    if contains_type_parameter(store, check_type, &HashSet::new())? {
        return deferred_conditional(
            store,
            root,
            check_type,
            extends_type,
            mapped_parameters,
            type_arguments,
        );
    }

    let mut combined_parameters = mapped_parameters.to_vec();
    let mut combined_arguments = type_arguments.to_vec();
    let mut inference_matched = false;
    if !infer_parameters.is_empty() {
        let mut candidates = vec![Vec::new(); infer_parameters.len()];
        let matched = infer_from_types(
            store,
            check_type,
            extends_type,
            &infer_parameters,
            &mut candidates,
            global_types,
        )?;
        if !matched {
            return map_type(
                store,
                branches.false_type,
                mapped_parameters,
                type_arguments,
                global_types,
                session,
            );
        }
        inference_matched = true;
        let unknown_type = store
            .intrinsic_bootstrap()
            .ok_or(ConditionalTypeError::MissingBootstrap)?
            .unknown_type;
        for (parameter, candidates) in infer_parameters.iter().zip(candidates) {
            let inferred = if candidates.is_empty() {
                unknown_type
            } else {
                union_result(store, &candidates, global_types)?
            };
            if !inferred_candidate_satisfies_constraint(
                store,
                *parameter,
                inferred,
                &combined_parameters,
                &combined_arguments,
                global_types,
                session,
            )? {
                return map_type(
                    store,
                    branches.false_type,
                    mapped_parameters,
                    type_arguments,
                    global_types,
                    session,
                );
            }
            combined_parameters.push(*parameter);
            combined_arguments.push(inferred);
        }
    }
    let inferred_extends = map_type(
        store,
        root_extends,
        &combined_parameters,
        &combined_arguments,
        global_types,
        session,
    )?;
    if contains_type_parameter(store, inferred_extends, &HashSet::new())? {
        return deferred_conditional(
            store,
            root,
            check_type,
            extends_type,
            mapped_parameters,
            type_arguments,
        );
    }

    let check_flags = type_flags(store, check_type)?;
    let extends_flags = type_flags(store, inferred_extends)?;
    let is_any = check_flags.intersects(TypeFlags::ANY);
    let extends_any_or_unknown = extends_flags.intersects(TypeFlags::ANY_OR_UNKNOWN);
    let inference_proves_assignability =
        inference_matched && is_structural_inference_target(store, extends_type)?;
    let assignable = extends_any_or_unknown
        || inference_proves_assignability
        || is_assignable(store, check_type, inferred_extends, global_types)?;

    if is_any && !extends_any_or_unknown {
        let when_true = map_type(
            store,
            branches.true_type,
            &combined_parameters,
            &combined_arguments,
            global_types,
            session,
        )?;
        let when_false = map_type(
            store,
            branches.false_type,
            mapped_parameters,
            type_arguments,
            global_types,
            session,
        )?;
        return union_result(store, &[when_true, when_false], global_types);
    }

    if !assignable && for_constraint && !is_never(store, inferred_extends)? {
        let reverse = is_assignable(store, inferred_extends, check_type, global_types)?;
        if reverse {
            let when_true = map_type(
                store,
                branches.true_type,
                &combined_parameters,
                &combined_arguments,
                global_types,
                session,
            )?;
            let when_false = map_type(
                store,
                branches.false_type,
                mapped_parameters,
                type_arguments,
                global_types,
                session,
            )?;
            return union_result(store, &[when_true, when_false], global_types);
        }
    }

    if assignable {
        if let Some(result) = evaluate_conditional_tail(
            store,
            root,
            branches.true_type,
            branches,
            &combined_parameters,
            &combined_arguments,
            global_types,
            for_constraint,
            session,
            tail_count,
        )? {
            return Ok(result);
        }
        map_type(
            store,
            branches.true_type,
            &combined_parameters,
            &combined_arguments,
            global_types,
            session,
        )
    } else {
        if let Some(result) = evaluate_conditional_tail(
            store,
            root,
            branches.false_type,
            branches,
            mapped_parameters,
            type_arguments,
            global_types,
            for_constraint,
            session,
            tail_count,
        )? {
            return Ok(result);
        }
        map_type(
            store,
            branches.false_type,
            mapped_parameters,
            type_arguments,
            global_types,
            session,
        )
    }
}

#[allow(clippy::too_many_arguments)] // Tail recursion retains the current root and active mapper.
fn evaluate_conditional_tail(
    store: &mut CanonicalTypeMapperStore,
    current_root: ConditionalRootId,
    branch: TypeId,
    current_branches: ConditionalTypeBranches,
    mapped_parameters: &[TypeId],
    type_arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    for_constraint: bool,
    session: &mut InstantiationSession,
    tail_count: usize,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    let Some(TypeData::Conditional(conditional)) = store.type_payload(branch).map(TypeRecord::data)
    else {
        return Ok(None);
    };
    let next_root = conditional.root;
    let nested_mapper = conditional.mapper;
    if mapped_parameters.is_empty() && nested_mapper.is_none() {
        return Ok(None);
    }
    let (parameters, check_type, distributive, aliased) = {
        let root = store
            .conditional_root(next_root)
            .ok_or(ConditionalTypeError::InvalidRoot(next_root))?;
        (
            root.outer_type_parameters().unwrap_or_default().to_vec(),
            root.check_type(),
            root.is_distributive(),
            root.alias().is_some() || conditional_node_has_alias_owner(store, root.node()),
        )
    };
    if parameters.is_empty() {
        return Ok(None);
    }

    let mut arguments = Vec::with_capacity(parameters.len());
    for parameter in &parameters {
        let nested =
            map_type_with_stored_mapper(store, *parameter, nested_mapper, global_types, session)?;
        arguments.push(map_type(
            store,
            nested,
            mapped_parameters,
            type_arguments,
            global_types,
            session,
        )?);
    }
    if distributive {
        let mapped_check = map_type(
            store,
            check_type,
            &parameters,
            &arguments,
            global_types,
            session,
        )?;
        if mapped_check != check_type
            && type_flags(store, mapped_check)?.intersects(TypeFlags::UNION | TypeFlags::NEVER)
        {
            return Ok(None);
        }
    }

    let branches = if next_root == current_root {
        current_branches
    } else if let Some(branches) = cached_conditional_branches(store, branch)? {
        branches
    } else {
        return Ok(None);
    };
    if next_root == current_root
        && parameters.as_slice() == mapped_parameters
        && arguments.as_slice() == type_arguments
        && branches == current_branches
    {
        if !aliased {
            return Ok(None);
        }
        let mut count = tail_count;
        while count < CONDITIONAL_TAIL_RECURSION_LIMIT {
            count += 1;
        }
        return Err(ConditionalTypeError::TailRecursionLimit {
            count,
            limit: CONDITIONAL_TAIL_RECURSION_LIMIT,
        });
    }

    let next_count = tail_count + usize::from(aliased);
    get_conditional_type_instantiation_with_tail_count(
        store,
        ConditionalTypeInstantiation {
            conditional_type: branch,
            type_arguments: &arguments,
            branches,
            alias: None,
            for_constraint,
        },
        global_types,
        Some(session),
        next_count,
    )
    .map(Some)
}

fn conditional_node_has_alias_owner(store: &CanonicalTypeMapperStore, mut node: NodeRef) -> bool {
    loop {
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(node) else {
            return false;
        };
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType) => node = parent,
            Some(SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration) => {
                return true;
            }
            _ => return false,
        }
    }
}

fn deferred_conditional(
    store: &mut CanonicalTypeMapperStore,
    root: ConditionalRootId,
    check_type: TypeId,
    extends_type: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
) -> Result<TypeId, ConditionalTypeError> {
    let mapper = if parameters.is_empty() || parameters == arguments {
        None
    } else {
        Some(
            store
                .new_type_mapper(parameters.to_vec(), arguments.to_vec())
                .ok_or(ConditionalTypeError::InvalidInstantiationCache(root))?,
        )
    };
    store
        .alloc_conditional_type(root, check_type, extends_type, mapper, None)
        .ok_or(ConditionalTypeError::InvalidRoot(root))
}

fn validate_request(
    store: &CanonicalTypeMapperStore,
    request: ConditionalTypeRequest<'_>,
) -> Result<(), ConditionalTypeError> {
    if !store.contains_node_ref(request.node) {
        return Err(ConditionalTypeError::InvalidNode(request.node));
    }
    validate_owned_type(store, request.check_type)?;
    validate_owned_type(store, request.extends_type)?;
    validate_branch_types(store, request.branches)?;
    if let Some(alias) = request.alias
        && store.type_alias(alias).is_none()
    {
        return Err(ConditionalTypeError::InvalidAlias(alias));
    }
    let mut seen = HashSet::new();
    for parameter in request
        .outer_type_parameters
        .iter()
        .chain(request.infer_type_parameters)
    {
        if !matches!(
            store.type_payload(*parameter).map(TypeRecord::data),
            Some(TypeData::TypeParameter(_))
        ) {
            return Err(ConditionalTypeError::InvalidTypeParameter(*parameter));
        }
        if !seen.insert(*parameter) {
            return Err(ConditionalTypeError::DuplicateTypeParameter(*parameter));
        }
    }
    Ok(())
}

fn validate_cached_conditional(
    store: &CanonicalTypeMapperStore,
    request: ConditionalTypeRequest<'_>,
    cached: TypeId,
) -> Result<TypeId, ConditionalTypeError> {
    let record = store
        .type_payload(cached)
        .ok_or(ConditionalTypeError::InvalidTypeNodeCache(request.node))?;
    if let TypeData::Conditional(data) = record.data() {
        let root = store
            .conditional_root(data.root)
            .ok_or(ConditionalTypeError::InvalidTypeNodeCache(request.node))?;
        if root.node() != request.node
            || root.check_type() != request.check_type
            || root.extends_type() != request.extends_type
            || root.infer_type_parameters().unwrap_or_default() != request.infer_type_parameters
            || root.outer_type_parameters().unwrap_or_default() != request.outer_type_parameters
            || root.alias() != request.alias
            || data.check_type != request.check_type
            || data.extends_type != request.extends_type
        {
            return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
        }
    }
    Ok(cached)
}

fn validate_cached_instantiation(
    store: &CanonicalTypeMapperStore,
    root: ConditionalRootId,
    cached: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
) -> Result<(), ConditionalTypeError> {
    let record = store
        .type_payload(cached)
        .ok_or(ConditionalTypeError::InvalidInstantiationCache(root))?;
    if let TypeData::Conditional(data) = record.data() {
        if data.root != root {
            return Err(ConditionalTypeError::InvalidInstantiationCache(root));
        }
        if let Some(mapper) = data.mapper
            && store.type_mapper_has_exact_endpoints(mapper, parameters, arguments) != Some(true)
        {
            return Err(ConditionalTypeError::InvalidInstantiationCache(root));
        }
    }
    Ok(())
}

fn validate_owned_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<(), ConditionalTypeError> {
    store
        .type_payload(type_)
        .map(|_| ())
        .ok_or(ConditionalTypeError::InvalidType(type_))
}

fn validate_branch_types(
    store: &CanonicalTypeMapperStore,
    branches: ConditionalTypeBranches,
) -> Result<(), ConditionalTypeError> {
    validate_owned_type(store, branches.true_type)?;
    validate_owned_type(store, branches.false_type)
}

fn conditional_type_key(
    store: &mut CanonicalTypeMapperStore,
    type_arguments: &[TypeId],
    alias: Option<TypeAliasId>,
    for_constraint: bool,
) -> Result<CacheHashKey, ConditionalTypeError> {
    let mut hasher = Xxh3::new();
    write_type_list(&mut hasher, type_arguments);
    if let Some(alias) = alias {
        let (symbol, arguments) = {
            let record = store
                .type_alias(alias)
                .ok_or(ConditionalTypeError::InvalidAlias(alias))?;
            (
                record
                    .symbol()
                    .ok_or(ConditionalTypeError::InvalidAlias(alias))?,
                record.type_arguments().unwrap_or_default().to_vec(),
            )
        };
        let symbol = store
            .global_symbol_id(symbol)
            .ok_or(ConditionalTypeError::InvalidAlias(alias))?;
        hasher.update(&[1]);
        hasher.update(&symbol.to_le_bytes());
        write_type_list(&mut hasher, &arguments);
    } else {
        hasher.update(&[0]);
    }
    if for_constraint {
        hasher.update(b"!");
    }
    Ok(CacheHashKey::new(hasher.digest128()))
}

fn write_type_list(hasher: &mut Xxh3, types: &[TypeId]) {
    hasher.update(
        &u64::try_from(types.len())
            .expect("conditional type-list length must fit the upstream encoding")
            .to_le_bytes(),
    );
    for type_ in types {
        hasher.update(&type_.get().to_le_bytes());
    }
}

#[derive(Clone, Debug)]
struct InferenceTupleShape {
    element_types: Vec<TypeId>,
    element_infos: Vec<TupleElementInfo>,
    min_length: usize,
    readonly: bool,
}

fn inference_tuple_shape(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<InferenceTupleShape>, ConditionalTypeError> {
    let Some(shape) = store.canonical_tuple_shape(type_)? else {
        return Ok(None);
    };
    Ok(Some(InferenceTupleShape {
        element_types: shape.element_types().to_vec(),
        element_infos: shape.element_infos().to_vec(),
        min_length: shape.min_length(),
        readonly: shape.is_readonly(),
    }))
}

fn is_structural_inference_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<bool, ConditionalTypeError> {
    if inference_tuple_shape(store, target)?.is_some() {
        return Ok(true);
    }
    let record = store
        .type_payload(target)
        .ok_or(ConditionalTypeError::InvalidType(target))?;
    Ok(record.data().structured().is_some_and(|structured| {
        structured
            .properties
            .as_ref()
            .is_some_and(|properties| !properties.is_empty())
            || structured
                .signatures
                .as_ref()
                .is_some_and(|signatures| !signatures.is_empty())
    }))
}

fn map_type(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
) -> Result<TypeId, ConditionalTypeError> {
    validate_owned_type(store, type_)?;
    if parameters.is_empty()
        || !contains_mapped_type_parameter(store, type_, parameters, &mut HashSet::new())?
    {
        return Ok(type_);
    }

    if let Some(tuple) = inference_tuple_shape(store, type_)? {
        let mut substituted = Vec::with_capacity(tuple.element_types.len());
        for element in tuple.element_types {
            substituted.push(map_type(
                store,
                element,
                parameters,
                arguments,
                global_types,
                session,
            )?);
        }
        let mut request =
            CanonicalTupleTypeRequest::new(&substituted, &tuple.element_infos, tuple.readonly);
        if let Some(global_types) = global_types {
            request =
                request.with_array_targets(CanonicalArrayTargets::from_global_types(global_types));
        }
        return store
            .create_canonical_tuple_type(request)
            .map_err(Into::into);
    }

    let template = match store.type_payload(type_).map(TypeRecord::data) {
        Some(TypeData::TemplateLiteral(template)) => {
            Some((template.texts.clone(), template.types.clone()))
        }
        _ => None,
    };
    if let Some((texts, types)) = template {
        let mut mapped = Vec::with_capacity(types.len());
        for placeholder in types {
            mapped.push(map_type(
                store,
                placeholder,
                parameters,
                arguments,
                global_types,
                session,
            )?);
        }
        return store
            .get_template_literal_type(&texts, &mapped)
            .map_err(Into::into);
    }

    let array_targets = global_types.map(CanonicalArrayTargets::from_global_types);
    instantiate_type_with_vector_and_session(
        store,
        type_,
        parameters,
        arguments,
        array_targets,
        session,
    )
    .map_err(Into::into)
}

fn map_type_with_stored_mapper(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: Option<TypeMapperId>,
    global_types: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
) -> Result<TypeId, ConditionalTypeError> {
    validate_owned_type(store, type_)?;
    let Some(mapper) = mapper else {
        return Ok(type_);
    };
    if store.mapper_payload(mapper).is_none() {
        return Err(ConditionalTypeError::InvalidMapper(mapper));
    }
    if let Some(tuple) = inference_tuple_shape(store, type_)? {
        let mut substituted = Vec::with_capacity(tuple.element_types.len());
        for element in tuple.element_types {
            substituted.push(map_type_with_stored_mapper(
                store,
                element,
                Some(mapper),
                global_types,
                session,
            )?);
        }
        let mut request =
            CanonicalTupleTypeRequest::new(&substituted, &tuple.element_infos, tuple.readonly);
        if let Some(global_types) = global_types {
            request =
                request.with_array_targets(CanonicalArrayTargets::from_global_types(global_types));
        }
        return store
            .create_canonical_tuple_type(request)
            .map_err(Into::into);
    }
    let template = match store.type_payload(type_).map(TypeRecord::data) {
        Some(TypeData::TemplateLiteral(template)) => {
            Some((template.texts.clone(), template.types.clone()))
        }
        _ => None,
    };
    if let Some((texts, types)) = template {
        let mut substituted = Vec::with_capacity(types.len());
        for placeholder in types {
            substituted.push(map_type_with_stored_mapper(
                store,
                placeholder,
                Some(mapper),
                global_types,
                session,
            )?);
        }
        return store
            .get_template_literal_type(&texts, &substituted)
            .map_err(Into::into);
    }
    instantiate_type_with_session(
        store,
        type_,
        mapper,
        global_types.map(CanonicalArrayTargets::from_global_types),
        session,
    )
    .map_err(Into::into)
}

fn contains_mapped_type_parameter(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    parameters: &[TypeId],
    visiting: &mut HashSet<TypeId>,
) -> Result<bool, ConditionalTypeError> {
    if !visiting.insert(type_) {
        return Ok(false);
    }
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    let result = match record.data() {
        TypeData::TypeParameter(_) => parameters.contains(&type_),
        TypeData::Union(union) => union.union.types.iter().try_fold(false, |found, item| {
            Ok::<_, ConditionalTypeError>(
                found || contains_mapped_type_parameter(store, *item, parameters, visiting)?,
            )
        })?,
        TypeData::Intersection(intersection) => {
            intersection
                .intersection
                .types
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found
                            || contains_mapped_type_parameter(store, *item, parameters, visiting)?,
                    )
                })?
        }
        TypeData::TypeReference(reference) => reference
            .resolved_type_arguments
            .as_deref()
            .unwrap_or_default()
            .iter()
            .try_fold(false, |found, item| {
                Ok::<_, ConditionalTypeError>(
                    found || contains_mapped_type_parameter(store, *item, parameters, visiting)?,
                )
            })?,
        TypeData::Interface(interface) => interface
            .reference
            .resolved_type_arguments
            .as_deref()
            .unwrap_or_default()
            .iter()
            .try_fold(false, |found, item| {
                Ok::<_, ConditionalTypeError>(
                    found || contains_mapped_type_parameter(store, *item, parameters, visiting)?,
                )
            })?,
        TypeData::Tuple(tuple) => tuple
            .interface
            .reference
            .resolved_type_arguments
            .as_deref()
            .unwrap_or_default()
            .iter()
            .try_fold(false, |found, item| {
                Ok::<_, ConditionalTypeError>(
                    found || contains_mapped_type_parameter(store, *item, parameters, visiting)?,
                )
            })?,
        TypeData::Conditional(conditional) => {
            contains_mapped_type_parameter(store, conditional.check_type, parameters, visiting)?
                || contains_mapped_type_parameter(
                    store,
                    conditional.extends_type,
                    parameters,
                    visiting,
                )?
        }
        TypeData::TemplateLiteral(template) => {
            template
                .types
                .iter()
                .try_fold(false, |found, placeholder| {
                    Ok::<_, ConditionalTypeError>(
                        found
                            || contains_mapped_type_parameter(
                                store,
                                *placeholder,
                                parameters,
                                visiting,
                            )?,
                    )
                })?
        }
        _ => false,
    };
    visiting.remove(&type_);
    Ok(result)
}

fn contains_type_parameter(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    excluded: &HashSet<TypeId>,
) -> Result<bool, ConditionalTypeError> {
    fn visit(
        store: &CanonicalTypeMapperStore,
        type_: TypeId,
        excluded: &HashSet<TypeId>,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<bool, ConditionalTypeError> {
        if !visiting.insert(type_) {
            return Ok(false);
        }
        let record = store
            .type_payload(type_)
            .ok_or(ConditionalTypeError::InvalidType(type_))?;
        let result = match record.data() {
            TypeData::TypeParameter(_) => !excluded.contains(&type_),
            TypeData::Union(union) => union.union.types.iter().try_fold(false, |found, item| {
                Ok::<_, ConditionalTypeError>(found || visit(store, *item, excluded, visiting)?)
            })?,
            TypeData::Intersection(intersection) => intersection
                .intersection
                .types
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(found || visit(store, *item, excluded, visiting)?)
                })?,
            TypeData::TypeReference(reference) => reference
                .resolved_type_arguments
                .as_deref()
                .unwrap_or_default()
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(found || visit(store, *item, excluded, visiting)?)
                })?,
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_deref()
                .unwrap_or_default()
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(found || visit(store, *item, excluded, visiting)?)
                })?,
            TypeData::Tuple(tuple) => tuple
                .interface
                .reference
                .resolved_type_arguments
                .as_deref()
                .unwrap_or_default()
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(found || visit(store, *item, excluded, visiting)?)
                })?,
            TypeData::Conditional(_) => true,
            TypeData::TemplateLiteral(template) => {
                template.types.iter().try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(found || visit(store, *item, excluded, visiting)?)
                })?
            }
            _ => false,
        };
        visiting.remove(&type_);
        Ok(result)
    }

    visit(store, type_, excluded, &mut HashSet::new())
}

fn infer_from_types(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    parameters: &[TypeId],
    candidates: &mut [Vec<TypeId>],
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<bool, ConditionalTypeError> {
    if let Some(index) = parameters.iter().position(|parameter| *parameter == target) {
        if !candidates[index].contains(&source) {
            candidates[index].push(source);
        }
        return Ok(true);
    }

    let source_tuple = inference_tuple_shape(store, source)?;
    let target_tuple = inference_tuple_shape(store, target)?;
    if let (Some(source_tuple), Some(target_tuple)) = (source_tuple, target_tuple) {
        return infer_from_tuple_types(
            store,
            &source_tuple,
            &target_tuple,
            parameters,
            candidates,
            global_types,
        );
    }

    let source_record = store
        .type_payload(source)
        .ok_or(ConditionalTypeError::InvalidType(source))?;
    let target_record = store
        .type_payload(target)
        .ok_or(ConditionalTypeError::InvalidType(target))?;
    if let TypeData::TemplateLiteral(target_template) = target_record.data() {
        let target_texts = target_template.texts.clone();
        let target_types = target_template.types.clone();
        let (source_texts, source_types) = match source_record.data() {
            TypeData::Literal(literal) => match &literal.value {
                LiteralValue::String(value) => (vec![value.clone()], Vec::new()),
                _ => return Ok(false),
            },
            TypeData::TemplateLiteral(template) => (template.texts.clone(), template.types.clone()),
            _ => return Ok(false),
        };
        let Some(matches) = infer_template_literal_matches(
            store,
            &source_texts,
            &source_types,
            &target_texts,
            &target_types,
        )?
        else {
            return Ok(false);
        };
        for (source, target) in matches.into_iter().zip(target_types) {
            let candidate = template_inference_candidate(store, source, target, parameters)?;
            if !infer_from_types(
                store,
                candidate,
                target,
                parameters,
                candidates,
                global_types,
            )? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if let (TypeData::TypeReference(source_ref), TypeData::TypeReference(target_ref)) =
        (source_record.data(), target_record.data())
    {
        if source_ref.object.target != target_ref.object.target {
            return Ok(false);
        }
        let source_arguments = source_ref
            .resolved_type_arguments
            .as_ref()
            .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?
            .clone();
        let target_arguments = target_ref
            .resolved_type_arguments
            .as_ref()
            .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?
            .clone();
        if source_arguments.len() != target_arguments.len() {
            return Ok(false);
        }
        for (source, target) in source_arguments.into_iter().zip(target_arguments) {
            if !infer_from_types(store, source, target, parameters, candidates, global_types)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }

    if source_record.data().structured().is_some() && target_record.data().structured().is_some() {
        return infer_from_structured_types(
            store,
            source,
            target,
            parameters,
            candidates,
            global_types,
        );
    }
    if contains_type_parameter(store, target, &HashSet::new())? {
        Err(ConditionalTypeError::UnsupportedInference { source, target })
    } else {
        is_assignable(store, source, target, global_types)
    }
}

fn infer_from_tuple_types(
    store: &mut CanonicalTypeMapperStore,
    source: &InferenceTupleShape,
    target: &InferenceTupleShape,
    parameters: &[TypeId],
    candidates: &mut [Vec<TypeId>],
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<bool, ConditionalTypeError> {
    let variable_indices = target
        .element_infos
        .iter()
        .enumerate()
        .filter_map(|(index, info)| {
            info.flags()
                .intersects(ElementFlags::VARIABLE)
                .then_some(index)
        })
        .collect::<Vec<_>>();
    if variable_indices.len() > 1 {
        return Ok(false);
    }

    let source_len = source.element_types.len();
    let target_len = target.element_types.len();
    if source_len < target.min_length {
        return Ok(false);
    }
    let Some(variable) = variable_indices.first().copied() else {
        if source_len > target_len {
            return Ok(false);
        }
        for (source, target) in source.element_types.iter().zip(&target.element_types) {
            if !infer_from_types(
                store,
                *source,
                *target,
                parameters,
                candidates,
                global_types,
            )? {
                return Ok(false);
            }
        }
        return Ok(true);
    };

    let suffix_len = target_len - variable - 1;
    if source_len < variable + suffix_len {
        return Ok(false);
    }
    for index in 0..variable {
        if !infer_from_types(
            store,
            source.element_types[index],
            target.element_types[index],
            parameters,
            candidates,
            global_types,
        )? {
            return Ok(false);
        }
    }
    for index in 0..suffix_len {
        let source_index = source_len - suffix_len + index;
        let target_index = variable + 1 + index;
        if !infer_from_types(
            store,
            source.element_types[source_index],
            target.element_types[target_index],
            parameters,
            candidates,
            global_types,
        )? {
            return Ok(false);
        }
    }

    let end = source_len - suffix_len;
    let middle_types = &source.element_types[variable..end];
    if target.element_infos[variable]
        .flags()
        .intersects(ElementFlags::VARIADIC)
    {
        let middle_infos = &source.element_infos[variable..end];
        let mut request = CanonicalTupleTypeRequest::new(middle_types, middle_infos, false);
        if let Some(global_types) = global_types {
            request =
                request.with_array_targets(CanonicalArrayTargets::from_global_types(global_types));
        }
        let middle = store.create_canonical_tuple_type(request)?;
        return infer_from_types(
            store,
            middle,
            target.element_types[variable],
            parameters,
            candidates,
            global_types,
        );
    }
    for element in middle_types {
        if !infer_from_types(
            store,
            *element,
            target.element_types[variable],
            parameters,
            candidates,
            global_types,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[derive(Clone, Debug)]
struct StructuredInferenceShape {
    properties: Vec<SemanticSymbolId>,
    call_signatures: Vec<SignatureId>,
    construct_signatures: Vec<SignatureId>,
}

fn structured_inference_shape(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<StructuredInferenceShape, ConditionalTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    let structured = record
        .data()
        .structured()
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    let signatures = structured.signatures.as_deref().unwrap_or_default();
    if structured.call_signature_count > signatures.len() {
        return Err(ConditionalTypeError::UnsupportedInference {
            source: type_,
            target: type_,
        });
    }
    Ok(StructuredInferenceShape {
        properties: structured.properties.clone().unwrap_or_default(),
        call_signatures: signatures[..structured.call_signature_count].to_vec(),
        construct_signatures: signatures[structured.call_signature_count..].to_vec(),
    })
}

fn infer_from_structured_types(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    parameters: &[TypeId],
    candidates: &mut [Vec<TypeId>],
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<bool, ConditionalTypeError> {
    let source_shape = structured_inference_shape(store, source)?;
    let target_shape = structured_inference_shape(store, target)?;
    if target_shape.properties.is_empty()
        && target_shape.call_signatures.is_empty()
        && target_shape.construct_signatures.is_empty()
    {
        return is_assignable(store, source, target, global_types);
    }

    for target_property in target_shape.properties {
        let target_name = store
            .symbol(target_property)
            .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?
            .name()
            .to_owned();
        let Some(source_property) = source_shape.properties.iter().copied().find(|property| {
            store
                .symbol(*property)
                .is_some_and(|record| record.name() == target_name.as_ref())
        }) else {
            return Ok(false);
        };
        let source_type = store
            .value_symbol_links(source_property)
            .and_then(|links| links.resolved_type)
            .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?;
        let target_type = store
            .value_symbol_links(target_property)
            .and_then(|links| links.resolved_type)
            .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?;
        if !infer_from_types(
            store,
            source_type,
            target_type,
            parameters,
            candidates,
            global_types,
        )? {
            return Ok(false);
        }
    }

    for (sources, targets) in [
        (
            source_shape.call_signatures.as_slice(),
            target_shape.call_signatures.as_slice(),
        ),
        (
            source_shape.construct_signatures.as_slice(),
            target_shape.construct_signatures.as_slice(),
        ),
    ] {
        if targets.is_empty() {
            continue;
        }
        if sources.is_empty() {
            return Ok(false);
        }
        for (index, target_signature) in targets.iter().copied().enumerate() {
            let source_index = sources.len().saturating_sub(targets.len()) + index;
            let source_signature = sources[source_index.min(sources.len() - 1)];
            let source_return = store
                .signature(source_signature)
                .and_then(Signature::resolved_return_type)
                .ok_or(ConditionalTypeError::InvalidSignature(source_signature))?;
            let target_return = store
                .signature(target_signature)
                .and_then(Signature::resolved_return_type)
                .ok_or(ConditionalTypeError::InvalidSignature(target_signature))?;
            if !infer_from_types(
                store,
                source_return,
                target_return,
                parameters,
                candidates,
                global_types,
            )? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

fn template_inference_candidate(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    parameters: &[TypeId],
) -> Result<TypeId, ConditionalTypeError> {
    if !parameters.contains(&target) {
        return Ok(source);
    }
    let value = match store.type_payload(source).map(TypeRecord::data) {
        Some(TypeData::Literal(literal)) => match &literal.value {
            LiteralValue::String(value) => value.clone(),
            _ => return Ok(source),
        },
        Some(_) => return Ok(source),
        None => return Err(ConditionalTypeError::InvalidType(source)),
    };
    let constraint = match store.type_payload(target).map(TypeRecord::data) {
        Some(TypeData::TypeParameter(parameter)) => parameter.constraint,
        _ => return Ok(source),
    };
    let Some(constraint) = constraint else {
        return Ok(source);
    };
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    if constraint == bootstrap.no_constraint_type
        || type_flags(store, constraint)?.intersects(TypeFlags::ANY)
    {
        return Ok(source);
    }
    let constituents = match store.type_payload(constraint).map(TypeRecord::data) {
        Some(TypeData::Union(union)) => union.union.types.clone(),
        Some(_) => vec![constraint],
        None => return Err(ConditionalTypeError::InvalidType(constraint)),
    };
    if constituents.iter().any(|constituent| {
        store
            .type_payload(*constituent)
            .is_some_and(|record| record.flags().intersects(TypeFlags::STRING))
    }) {
        return Ok(source);
    }

    for constituent in &constituents {
        if let Some(TypeData::Literal(literal)) =
            store.type_payload(*constituent).map(TypeRecord::data)
            && matches!(&literal.value, LiteralValue::String(text) if text == &value)
        {
            return Ok(*constituent);
        }
    }

    let number = ts_jsnum::from_string(&value);
    if !number.is_nan() && !number.is_infinite() && number.to_string() == value {
        for constituent in &constituents {
            let record = store
                .type_payload(*constituent)
                .ok_or(ConditionalTypeError::InvalidType(*constituent))?;
            if record.flags().intersects(TypeFlags::NUMBER) {
                return store
                    .regular_number_literal_type(number)
                    .map_err(Into::into);
            }
            if let TypeData::Literal(literal) = record.data()
                && matches!(&literal.value, LiteralValue::Number(existing) if *existing == number)
            {
                return Ok(*constituent);
            }
        }
    }

    if let Some(bigint) = canonical_bigint_inference_value(&value) {
        for constituent in &constituents {
            let record = store
                .type_payload(*constituent)
                .ok_or(ConditionalTypeError::InvalidType(*constituent))?;
            if record.flags().intersects(TypeFlags::BIG_INT) {
                return store
                    .regular_bigint_literal_type(bigint)
                    .map_err(Into::into);
            }
            if let TypeData::Literal(literal) = record.data()
                && matches!(&literal.value, LiteralValue::BigInt(existing) if *existing == bigint)
            {
                return Ok(*constituent);
            }
        }
    }

    if matches!(value.as_str(), "true" | "false") {
        let expected = value == "true";
        for constituent in &constituents {
            let record = store
                .type_payload(*constituent)
                .ok_or(ConditionalTypeError::InvalidType(*constituent))?;
            if let TypeData::Literal(literal) = record.data()
                && matches!(literal.value, LiteralValue::Boolean(actual) if actual == expected)
            {
                return Ok(*constituent);
            }
            if record.flags().intersects(TypeFlags::BOOLEAN) {
                let bootstrap = store
                    .intrinsic_bootstrap()
                    .ok_or(ConditionalTypeError::MissingBootstrap)?;
                return Ok(if expected {
                    bootstrap.true_type
                } else {
                    bootstrap.false_type
                });
            }
        }
    }

    Ok(source)
}

fn canonical_bigint_inference_value(value: &str) -> Option<ts_jsnum::PseudoBigInt> {
    let digits = value.strip_prefix('-').unwrap_or(value);
    if digits.is_empty() || !digits.bytes().all(|digit| digit.is_ascii_digit()) {
        return None;
    }
    let parsed = ts_jsnum::PseudoBigInt::parse_valid(value);
    (parsed.to_string() == value).then_some(parsed)
}

fn infer_template_literal_matches(
    store: &mut CanonicalTypeMapperStore,
    source_texts: &[String],
    source_types: &[TypeId],
    target_texts: &[String],
    target_types: &[TypeId],
) -> Result<Option<Vec<TypeId>>, ConditionalTypeError> {
    if source_texts.len() != source_types.len().saturating_add(1)
        || target_texts.len() != target_types.len().saturating_add(1)
        || source_texts.is_empty()
        || target_types.is_empty()
    {
        return Ok(None);
    }
    if source_texts == target_texts && source_types.len() == target_types.len() {
        return Ok(Some(source_types.to_vec()));
    }

    let last_source = source_texts.len() - 1;
    let last_target = target_texts.len() - 1;
    let source_start = &source_texts[0];
    let source_end = &source_texts[last_source];
    let target_start = &target_texts[0];
    let target_end = &target_texts[last_target];
    if last_source == 0 && source_start.len() < target_start.len() + target_end.len()
        || !source_start.starts_with(target_start)
        || !source_end.ends_with(target_end)
    {
        return Ok(None);
    }
    let remaining_end = &source_end[..source_end.len() - target_end.len()];
    let mut segment = 0;
    let mut position = target_start.len();
    let mut matches = Vec::with_capacity(target_types.len());

    for delimiter in &target_texts[1..last_target] {
        let (match_segment, match_position) = if delimiter.is_empty() {
            let current = if segment == last_source {
                remaining_end
            } else {
                &source_texts[segment]
            };
            if let Some(character) = current[position..].chars().next() {
                (segment, position + character.len_utf8())
            } else if segment < last_source {
                (segment + 1, 0)
            } else {
                return Ok(None);
            }
        } else {
            let mut search_segment = segment;
            let mut search_position = position;
            loop {
                let current = if search_segment == last_source {
                    remaining_end
                } else {
                    &source_texts[search_segment]
                };
                if let Some(offset) = current[search_position..].find(delimiter) {
                    break (search_segment, search_position + offset);
                }
                search_segment += 1;
                if search_segment == source_texts.len() {
                    return Ok(None);
                }
                search_position = 0;
            }
        };
        matches.push(capture_template_literal_part(
            store,
            source_texts,
            source_types,
            remaining_end,
            segment,
            position,
            match_segment,
            match_position,
        )?);
        segment = match_segment;
        position = match_position + delimiter.len();
    }
    matches.push(capture_template_literal_part(
        store,
        source_texts,
        source_types,
        remaining_end,
        segment,
        position,
        last_source,
        remaining_end.len(),
    )?);
    Ok(Some(matches))
}

#[allow(clippy::too_many_arguments)] // Both source endpoints are needed for upstream segment capture.
fn capture_template_literal_part(
    store: &mut CanonicalTypeMapperStore,
    source_texts: &[String],
    source_types: &[TypeId],
    remaining_end: &str,
    start_segment: usize,
    start_position: usize,
    end_segment: usize,
    end_position: usize,
) -> Result<TypeId, ConditionalTypeError> {
    let source_text = |index: usize| {
        if index + 1 == source_texts.len() {
            remaining_end
        } else {
            source_texts[index].as_str()
        }
    };
    if start_segment == end_segment {
        return store
            .regular_string_literal_type(
                source_text(start_segment)[start_position..end_position].to_owned(),
            )
            .map_err(Into::into);
    }

    let mut texts = Vec::with_capacity(end_segment - start_segment + 1);
    texts.push(source_texts[start_segment][start_position..].to_owned());
    texts.extend(source_texts[start_segment + 1..end_segment].iter().cloned());
    texts.push(source_text(end_segment)[..end_position].to_owned());
    store
        .get_template_literal_type(&texts, &source_types[start_segment..end_segment])
        .map_err(Into::into)
}

#[allow(clippy::too_many_arguments)] // A constraint uses the same active mapper as its root.
fn inferred_candidate_satisfies_constraint(
    store: &mut CanonicalTypeMapperStore,
    parameter: TypeId,
    candidate: TypeId,
    mapped_parameters: &[TypeId],
    type_arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
) -> Result<bool, ConditionalTypeError> {
    let constraint = match store.type_payload(parameter).map(TypeRecord::data) {
        Some(TypeData::TypeParameter(data)) => data.constraint,
        _ => return Err(ConditionalTypeError::InvalidTypeParameter(parameter)),
    };
    let Some(constraint) = constraint else {
        return Ok(true);
    };
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    if constraint == bootstrap.no_constraint_type {
        return Ok(true);
    }
    let constraint = map_type(
        store,
        constraint,
        mapped_parameters,
        type_arguments,
        global_types,
        session,
    )?;
    is_assignable(store, candidate, constraint, global_types)
}

fn union_result(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<TypeId, ConditionalTypeError> {
    if let Some(global_types) = global_types {
        store
            .expression_union_type_with_global_types(
                global_types,
                types,
                super::bootstrap::UnionReduction::Literal,
            )
            .map_err(Into::into)
    } else {
        canonical_anonymous_union(store, types).map_err(Into::into)
    }
}

/// Compares conditional operands, including concrete fixed tuple wrappers.
pub(super) fn conditional_check_is_assignable(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<bool, ConditionalTypeError> {
    validate_owned_type(store, source)?;
    validate_owned_type(store, target)?;
    conditional_check_is_assignable_worker(store, source, target, global_types, &mut HashSet::new())
}

fn is_assignable(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<bool, ConditionalTypeError> {
    conditional_check_is_assignable(store, source, target, global_types)
}

fn conditional_check_is_assignable_worker(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
    visiting: &mut HashSet<(TypeId, TypeId)>,
) -> Result<bool, ConditionalTypeError> {
    if source == target {
        return Ok(true);
    }
    if !visiting.insert((source, target)) {
        return Ok(true);
    }
    let result = if let (Some(source_shape), Some(target_shape)) = (
        inference_tuple_shape(store, source)?,
        inference_tuple_shape(store, target)?,
    ) {
        concrete_tuple_types_are_assignable(
            store,
            &source_shape,
            &target_shape,
            global_types,
            visiting,
        )
    } else {
        ordinary_assignability(store, source, target, global_types)
    };
    visiting.remove(&(source, target));
    result
}

fn concrete_tuple_types_are_assignable(
    store: &mut CanonicalTypeMapperStore,
    source: &InferenceTupleShape,
    target: &InferenceTupleShape,
    global_types: Option<&CanonicalGlobalTypes>,
    visiting: &mut HashSet<(TypeId, TypeId)>,
) -> Result<bool, ConditionalTypeError> {
    if source.readonly && !target.readonly {
        return Ok(false);
    }
    let source_len = source.element_types.len();
    let target_len = target.element_types.len();
    if source_len < target.min_length {
        return Ok(false);
    }
    let target_rest = target
        .element_infos
        .iter()
        .position(|info| info.flags().intersects(ElementFlags::REST));
    if target_rest.is_none() && source_len > target_len {
        return Ok(false);
    }
    for (index, source_type) in source.element_types.iter().copied().enumerate() {
        let target_index = if index < target_len {
            index
        } else if let Some(rest) = target_rest {
            rest
        } else {
            return Ok(false);
        };
        if source.element_infos[index]
            .flags()
            .intersects(ElementFlags::OPTIONAL)
            && target.element_infos[target_index]
                .flags()
                .intersects(ElementFlags::REQUIRED)
        {
            return Ok(false);
        }
        if !conditional_check_is_assignable_worker(
            store,
            source_type,
            target.element_types[target_index],
            global_types,
            visiting,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn ordinary_assignability(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<bool, ConditionalTypeError> {
    match global_types {
        Some(global_types) => store
            .is_type_assignable_to_with_global_types(source, target, global_types)
            .map_err(Into::into),
        None => store
            .is_type_assignable_to(source, target)
            .map_err(Into::into),
    }
}

fn type_flags(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<TypeFlags, ConditionalTypeError> {
    store
        .type_payload(type_)
        .map(TypeRecord::flags)
        .ok_or(ConditionalTypeError::InvalidType(type_))
}

fn is_never(store: &CanonicalTypeMapperStore, type_: TypeId) -> Result<bool, ConditionalTypeError> {
    Ok(type_flags(store, type_)?.intersects(TypeFlags::NEVER))
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, SyntaxKind};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, EscapedName, SymbolData, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore, ValueSymbolLinks,
        declared::execute_type_parameter, mapper::TypeMapper, signatures::SignatureFlags,
        types::ObjectFlags,
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    impl Fixture {
        fn new(source: &str) -> Self {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(17);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/conditional.ts\""),
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
            let mut store = SemanticStore::<TypeRecord, TypeMapper>::from_symbol_store(symbols);
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
            store
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
                .unwrap();
            Self {
                parsed,
                file,
                bound,
                store,
            }
        }

        fn conditional(&self) -> NodeRef {
            self.parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ConditionalType).then_some(NodeRef::new(
                        self.parsed.arena.id(),
                        self.file,
                        node,
                    ))
                })
                .unwrap()
        }

        fn type_parameter(&mut self, expected: &str) -> TypeId {
            let declaration = self
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::TypeParameterDeclaration(parameter) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &self.parsed.arena.get(parameter.name)?.data
                    else {
                        return None;
                    };
                    (name.text == expected).then_some(NodeRef::new(
                        self.parsed.arena.id(),
                        self.file,
                        node,
                    ))
                })
                .unwrap_or_else(|| panic!("missing type parameter {expected}"));
            let symbol = self
                .bound
                .symbol(declaration)
                .unwrap_or_else(|| panic!("missing type-parameter symbol {expected}"));
            execute_type_parameter(&mut self.store, symbol)
        }
    }

    fn branches(true_type: TypeId, false_type: TypeId) -> ConditionalTypeBranches {
        ConditionalTypeBranches {
            true_type,
            false_type,
        }
    }

    fn callable_object(
        store: &mut CanonicalTypeMapperStore,
        return_type: TypeId,
        construct: bool,
    ) -> TypeId {
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(return_type),
                None,
                0,
            )
            .unwrap();
        let call = (!construct).then(|| vec![signature]);
        let constructor = construct.then(|| vec![signature]);
        assert!(store.set_structured_type_members(object, None, None, call, constructor, None));
        object
    }

    fn property_object(store: &mut CanonicalTypeMapperStore, name: &str, value: TypeId) -> TypeId {
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let property = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source(name),
            ))
            .unwrap();
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(value),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            object,
            None,
            Some(vec![property]),
            None,
            None,
            None,
        ));
        object
    }

    #[test]
    fn concrete_conditionals_choose_the_correct_branch_and_reuse_node_identity() {
        let mut fixture = Fixture::new("type Result = string extends string ? number : boolean;");
        let node = fixture.conditional();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, boolean) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
        );
        let request = ConditionalTypeRequest {
            node,
            check_type: string,
            extends_type: string,
            branches: branches(number, boolean),
            infer_type_parameters: &[],
            outer_type_parameters: &[],
            alias: None,
        };

        assert_eq!(
            get_type_from_conditional_type(&mut fixture.store, request, None),
            Ok(number)
        );
        assert_eq!(fixture.store.conditional_root_len(), 1);
        assert_eq!(
            fixture
                .store
                .type_node_links(node)
                .and_then(|links| links.resolved_type),
            Some(number)
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
            fixture.store.mapper_len(),
        );
        assert_eq!(
            get_type_from_conditional_type(&mut fixture.store, request, None),
            Ok(number)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            ),
            warm
        );
    }

    #[test]
    fn distributive_conditionals_filter_unions_and_preserve_never() {
        let mut fixture = Fixture::new("type Exclude<T, U> = T extends U ? never : T;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let excluded = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let branch_types = branches(never, parameter);
        let declared = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: excluded,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: &[parameter, excluded],
                alias: None,
            },
            None,
        )
        .unwrap();
        let TypeData::Conditional(conditional) =
            fixture.store.type_payload(declared).unwrap().data()
        else {
            panic!("a generic conditional must retain its deferred type identity")
        };
        let root = conditional.root;
        let root_record = fixture.store.conditional_root(root).unwrap();
        assert_eq!(root_record.node(), node);
        assert!(root_record.is_distributive());
        assert_eq!(
            root_record.outer_type_parameters(),
            Some([parameter, excluded].as_slice())
        );
        let TypeCacheState::Allocated(cache) = root_record.instantiations() else {
            panic!("a generic conditional root owns its instantiation cache")
        };
        assert_eq!(cache.len(), 1);

        let union = canonical_anonymous_union(&mut fixture.store, &[string, number]).unwrap();
        let filtered = get_conditional_type_instantiation(
            &mut fixture.store,
            ConditionalTypeInstantiation {
                conditional_type: declared,
                type_arguments: &[union, string],
                branches: branch_types,
                alias: None,
                for_constraint: false,
            },
            None,
            None,
        )
        .unwrap();
        assert_eq!(filtered, number);
        let warm = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
            fixture.store.mapper_len(),
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[union, string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(number)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            ),
            warm
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[never, string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(never)
        );
    }

    #[test]
    fn any_joins_both_branches_except_against_any_or_unknown() {
        let mut fixture = Fixture::new("type Result = any extends string ? number : boolean;");
        let node = fixture.conditional();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (any, string, number, boolean) = (
            bootstrap.any_type,
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
        );
        let result = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: any,
                extends_type: string,
                branches: branches(number, boolean),
                infer_type_parameters: &[],
                outer_type_parameters: &[],
                alias: None,
            },
            None,
        )
        .unwrap();
        let expected = canonical_anonymous_union(&mut fixture.store, &[number, boolean]).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn naked_any_uses_both_branches_but_tuple_wrapped_any_uses_only_the_true_branch() {
        let mut naked = Fixture::new("type T = any extends number ? 1 : 0;");
        let naked_node = naked.conditional();
        let bootstrap = naked.store.intrinsic_bootstrap().unwrap();
        let (any, number) = (bootstrap.any_type, bootstrap.number_type);
        let one = naked
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let zero = naked
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(0.0))
            .unwrap();
        let naked_result = get_type_from_conditional_type(
            &mut naked.store,
            ConditionalTypeRequest {
                node: naked_node,
                check_type: any,
                extends_type: number,
                branches: branches(one, zero),
                infer_type_parameters: &[],
                outer_type_parameters: &[],
                alias: None,
            },
            None,
        )
        .unwrap();
        let TypeData::Union(union) = naked.store.type_payload(naked_result).unwrap().data() else {
            panic!("a naked any conditional must retain both numeric branches")
        };
        assert!(union.union.types.contains(&one));
        assert!(union.union.types.contains(&zero));

        let mut wrapped = Fixture::new("type U = [any] extends [number] ? 1 : 0;");
        let wrapped_node = wrapped.conditional();
        let bootstrap = wrapped.store.intrinsic_bootstrap().unwrap();
        let (any, number) = (bootstrap.any_type, bootstrap.number_type);
        let one = wrapped
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let zero = wrapped
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(0.0))
            .unwrap();
        let required = wrapped
            .store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let check = wrapped
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&[any], &[required], false))
            .unwrap();
        let extends = wrapped
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number],
                &[required],
                false,
            ))
            .unwrap();
        assert_eq!(
            conditional_check_is_assignable(&mut wrapped.store, check, extends, None),
            Ok(true)
        );
        assert_eq!(
            get_type_from_conditional_type(
                &mut wrapped.store,
                ConditionalTypeRequest {
                    node: wrapped_node,
                    check_type: check,
                    extends_type: extends,
                    branches: branches(one, zero),
                    infer_type_parameters: &[],
                    outer_type_parameters: &[],
                    alias: None,
                },
                None,
            ),
            Ok(one)
        );
    }

    #[test]
    fn naked_infer_parameters_retain_candidates_and_respect_constraints() {
        let mut fixture = Fixture::new("type Result<T> = T extends infer U ? U : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        assert!(fixture.store.set_type_parameter_resolution(
            inferred,
            Some(string),
            None,
            None,
            None,
        ));
        let branch_types = branches(inferred, never);
        let declared = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: inferred,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: &[parameter],
                alias: None,
            },
            None,
        )
        .unwrap();

        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(string)
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[number],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(never)
        );
    }

    #[test]
    fn conditional_keys_preserve_alias_and_constraint_dimensions() {
        let mut fixture = Fixture::new("type Result<T> = T extends string ? T : never;");
        let parameter = fixture.type_parameter("T");
        let ordinary = conditional_type_key(&mut fixture.store, &[parameter], None, false)
            .expect("ordinary cache key");
        let constraint = conditional_type_key(&mut fixture.store, &[parameter], None, true)
            .expect("constraint cache key");
        assert_ne!(ordinary, constraint);
    }

    #[test]
    fn source_owned_conditional_self_recursion_reaches_the_pinned_limit() {
        let mut fixture = Fixture::new("type Loop<T> = T extends string ? string : Loop<T>;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let declared = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: string,
                branches: branches(string, never),
                infer_type_parameters: &[],
                outer_type_parameters: &[parameter],
                alias: None,
            },
            None,
        )
        .unwrap();
        let TypeData::Conditional(data) = fixture.store.type_payload(declared).unwrap().data()
        else {
            panic!("the recursive source alias must retain its conditional root")
        };
        let root = fixture.store.conditional_root(data.root).unwrap();
        assert!(root.alias().is_none());
        assert!(conditional_node_has_alias_owner(
            &fixture.store,
            root.node()
        ));
        let branch_types = branches(string, declared);
        let before = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
            fixture.store.mapper_len(),
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[number],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Err(ConditionalTypeError::TailRecursionLimit {
                count: CONDITIONAL_TAIL_RECURSION_LIMIT,
                limit: CONDITIONAL_TAIL_RECURSION_LIMIT,
            })
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            ),
            before
        );
    }

    #[test]
    fn foreign_inputs_and_duplicate_parameters_fail_before_root_allocation() {
        let mut fixture = Fixture::new("type Result<T> = T extends string ? T : never;");
        let foreign = Fixture::new("type Foreign = string extends string ? number : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, never) = (bootstrap.string_type, bootstrap.never_type);
        let foreign_string = foreign.store.intrinsic_bootstrap().unwrap().string_type;
        let before = fixture.store.conditional_root_len();

        assert_eq!(
            get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: foreign_string,
                    extends_type: string,
                    branches: branches(parameter, never),
                    infer_type_parameters: &[],
                    outer_type_parameters: &[parameter],
                    alias: None,
                },
                None,
            ),
            Err(ConditionalTypeError::InvalidType(foreign_string))
        );
        assert_eq!(
            get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: string,
                    branches: branches(parameter, never),
                    infer_type_parameters: &[parameter],
                    outer_type_parameters: &[parameter],
                    alias: None,
                },
                None,
            ),
            Err(ConditionalTypeError::DuplicateTypeParameter(parameter))
        );
        assert_eq!(fixture.store.conditional_root_len(), before);
    }

    #[test]
    fn default_constraints_cache_branches_and_exclude_any() {
        for true_branch_is_any in [true, false] {
            let mut fixture = Fixture::new("type Result<T> = T extends string ? any : number;");
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, any) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.any_type,
            );
            let branch_types = if true_branch_is_any {
                branches(any, number)
            } else {
                branches(number, any)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: string,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: &[parameter],
                    alias: None,
                },
                None,
            )
            .unwrap();
            let cold = conditional_snapshot(&fixture.store, conditional).unwrap();
            assert_eq!(cold.resolved_true_type, None);
            assert_eq!(cold.resolved_false_type, None);
            assert_eq!(cold.resolved_default_constraint, None);

            assert_eq!(
                get_default_constraint_of_conditional_type(
                    &mut fixture.store,
                    conditional,
                    branch_types,
                    None,
                    None,
                ),
                Ok(number)
            );
            let resolved = conditional_snapshot(&fixture.store, conditional).unwrap();
            assert_eq!(resolved.resolved_true_type, Some(branch_types.true_type));
            assert_eq!(resolved.resolved_false_type, Some(branch_types.false_type));
            assert_eq!(resolved.resolved_default_constraint, Some(number));

            let warm = (fixture.store.type_len(), fixture.store.mapper_len());
            assert_eq!(
                get_default_constraint_of_conditional_type(
                    &mut fixture.store,
                    conditional,
                    branch_types,
                    None,
                    None,
                ),
                Ok(number)
            );
            assert_eq!((fixture.store.type_len(), fixture.store.mapper_len()), warm);
        }
    }

    #[test]
    fn distributive_constraints_filter_a_constrained_parameter() {
        let mut fixture = Fixture::new("type Result<T> = T extends string ? T : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let constraint = canonical_anonymous_union(&mut fixture.store, &[string, number]).unwrap();
        assert!(fixture.store.set_type_parameter_resolution(
            parameter,
            Some(constraint),
            None,
            None,
            None,
        ));
        let branch_types = branches(parameter, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: string,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: &[parameter],
                alias: None,
            },
            None,
        )
        .unwrap();

        assert_eq!(
            get_constraint_of_distributive_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(Some(string))
        );
        let resolved = conditional_snapshot(&fixture.store, conditional).unwrap();
        assert_eq!(resolved.resolved_constraint_of_distributive, Some(string));
        assert_eq!(
            get_constraint_from_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(string)
        );

        assert_eq!(
            get_true_type_from_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(parameter)
        );
        assert_eq!(
            get_false_type_from_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(never)
        );
        assert_eq!(
            constraints::get_constraint_of_type(&mut fixture.store, conditional),
            Ok(Some(string))
        );
    }

    #[test]
    fn template_inference_consumes_complete_unicode_code_points() {
        for (source, expected, selected) in [
            (
                "type Head<T> = T extends `${infer H}${infer R}` ? H : never;",
                "\u{1F600}",
                "H",
            ),
            (
                "type Rest<T> = T extends `${infer H}${infer R}` ? R : never;",
                "abc",
                "R",
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let head = fixture.type_parameter("H");
            let rest = fixture.type_parameter("R");
            let never = fixture.store.intrinsic_bootstrap().unwrap().never_type;
            let template = fixture
                .store
                .get_template_literal_type(
                    &[String::new(), String::new(), String::new()],
                    &[head, rest],
                )
                .unwrap();
            let selected = if selected == "H" { head } else { rest };
            let branch_types = branches(selected, never);
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: template,
                    branches: branch_types,
                    infer_type_parameters: &[head, rest],
                    outer_type_parameters: &[parameter],
                    alias: None,
                },
                None,
            )
            .unwrap();
            let value = fixture
                .store
                .regular_string_literal_type("\u{1F600}abc".to_owned())
                .unwrap();
            let result = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[value],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            let Some(TypeData::Literal(literal)) =
                fixture.store.type_payload(result).map(TypeRecord::data)
            else {
                panic!("template inference must produce a string literal")
            };
            assert_eq!(literal.value, LiteralValue::String(expected.to_owned()));
        }
    }

    #[test]
    fn template_inference_matches_delimiters_and_rejects_missing_segments() {
        let mut fixture =
            Fixture::new("type Left<T> = T extends `start-${infer A}:${infer B}-end` ? A : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let left = fixture.type_parameter("A");
        let right = fixture.type_parameter("B");
        let never = fixture.store.intrinsic_bootstrap().unwrap().never_type;
        let template = fixture
            .store
            .get_template_literal_type(
                &["start-".to_owned(), ":".to_owned(), "-end".to_owned()],
                &[left, right],
            )
            .unwrap();
        let branch_types = branches(left, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: template,
                branches: branch_types,
                infer_type_parameters: &[left, right],
                outer_type_parameters: &[parameter],
                alias: None,
            },
            None,
        )
        .unwrap();
        for (source, expected) in [("start-first:second-end", Some("first")), ("bad", None)] {
            let value = fixture
                .store
                .regular_string_literal_type(source.to_owned())
                .unwrap();
            let result = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[value],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            if let Some(expected) = expected {
                let Some(TypeData::Literal(literal)) =
                    fixture.store.type_payload(result).map(TypeRecord::data)
                else {
                    panic!("a matching template must infer its first segment")
                };
                assert_eq!(literal.value, LiteralValue::String(expected.to_owned()));
            } else {
                assert_eq!(result, never);
            }
        }
    }

    #[test]
    fn constrained_template_inference_preserves_numeric_bigint_and_boolean_literals() {
        for (source, constraint_kind, expected) in [
            (
                "42",
                "number",
                Some(LiteralValue::Number(ts_jsnum::Number::new(42.0))),
            ),
            (
                "-7",
                "bigint",
                Some(LiteralValue::BigInt(ts_jsnum::PseudoBigInt::parse_valid(
                    "-7",
                ))),
            ),
            ("true", "boolean", Some(LiteralValue::Boolean(true))),
            ("01", "number", None),
        ] {
            let mut fixture = Fixture::new("type Parse<T> = T extends `${infer U}` ? U : never;");
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let inferred = fixture.type_parameter("U");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let never = bootstrap.never_type;
            let constraint = match constraint_kind {
                "number" => bootstrap.number_type,
                "bigint" => bootstrap.bigint_type,
                "boolean" => bootstrap.boolean_type,
                _ => unreachable!(),
            };
            assert!(fixture.store.set_type_parameter_resolution(
                inferred,
                Some(constraint),
                None,
                None,
                None,
            ));
            let template = fixture
                .store
                .get_template_literal_type(&[String::new(), String::new()], &[inferred])
                .unwrap();
            let branch_types = branches(inferred, never);
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: template,
                    branches: branch_types,
                    infer_type_parameters: &[inferred],
                    outer_type_parameters: &[parameter],
                    alias: None,
                },
                None,
            )
            .unwrap();
            let value = fixture
                .store
                .regular_string_literal_type(source.to_owned())
                .unwrap();
            let result = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[value],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            if let Some(expected) = expected {
                let Some(TypeData::Literal(literal)) =
                    fixture.store.type_payload(result).map(TypeRecord::data)
                else {
                    panic!("{source:?} must infer a {constraint_kind} literal")
                };
                assert_eq!(literal.value, expected);
            } else {
                assert_eq!(result, never);
            }
        }
    }

    #[test]
    fn constrained_template_inference_keeps_strings_when_the_constraint_allows_them() {
        let mut fixture = Fixture::new("type Parse<T> = T extends `${infer U}` ? U : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let constraint = canonical_anonymous_union(&mut fixture.store, &[string, number]).unwrap();
        assert!(fixture.store.set_type_parameter_resolution(
            inferred,
            Some(constraint),
            None,
            None,
            None,
        ));
        let template = fixture
            .store
            .get_template_literal_type(&[String::new(), String::new()], &[inferred])
            .unwrap();
        let branch_types = branches(inferred, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: template,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: &[parameter],
                alias: None,
            },
            None,
        )
        .unwrap();
        let value = fixture
            .store
            .regular_string_literal_type("42".to_owned())
            .unwrap();
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[value],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(value)
        );
    }

    #[test]
    fn conditional_inference_reads_call_and_construct_return_types() {
        for construct in [false, true] {
            let mut fixture = Fixture::new("type Result<T> = T extends infer U ? U : never;");
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let inferred = fixture.type_parameter("U");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, never) = (bootstrap.string_type, bootstrap.never_type);
            let target = callable_object(&mut fixture.store, inferred, construct);
            let source = callable_object(&mut fixture.store, string, construct);
            let branch_types = branches(inferred, never);
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: target,
                    branches: branch_types,
                    infer_type_parameters: &[inferred],
                    outer_type_parameters: &[parameter],
                    alias: None,
                },
                None,
            )
            .unwrap();
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[source],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(string),
                "construct={construct}"
            );
        }
    }

    #[test]
    fn conditional_inference_reads_named_object_properties() {
        let mut fixture = Fixture::new("type Result<T> = T extends infer U ? U : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, never) = (bootstrap.string_type, bootstrap.never_type);
        let target = property_object(&mut fixture.store, "value", inferred);
        let matching = property_object(&mut fixture.store, "value", string);
        let missing = property_object(&mut fixture.store, "other", string);
        let branch_types = branches(inferred, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: target,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: &[parameter],
                alias: None,
            },
            None,
        )
        .unwrap();

        for (source, expected) in [(matching, string), (missing, never)] {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[source],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(expected)
            );
        }
    }

    #[test]
    fn tuple_inference_preserves_elements_and_rejects_short_inputs() {
        let mut fixture = Fixture::new("type Result<T> = T extends [infer U, number] ? U : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let required = fixture
            .store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let target_infos = [required, required];
        let target = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[inferred, number],
                &target_infos,
                false,
            ))
            .unwrap();
        let matching = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string, number],
                &target_infos,
                false,
            ))
            .unwrap();
        let missing = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string],
                &[required],
                false,
            ))
            .unwrap();
        let branch_types = branches(inferred, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: target,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: &[parameter],
                alias: None,
            },
            None,
        )
        .unwrap();

        for (source, expected) in [(matching, string), (missing, never)] {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[source],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(expected)
            );
        }
    }
}
