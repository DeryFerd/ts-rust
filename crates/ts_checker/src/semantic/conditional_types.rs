//! Canonical conditional-type roots, distribution, and bounded inference.
//!
//! This module follows `getTypeFromConditionalTypeNode`, `getConditionalType`,
//! and `getConditionalTypeInstantiation` in the pinned TypeScript Go checker.
//! Syntax planning and branch resolution remain with the type-node owner.

use std::collections::{HashMap, HashSet};

use ts_ast::NodeRef;
use xxhash_rust::xxh3::Xxh3;

use super::{
    CanonicalGlobalTypes, ConditionalRootId, RelationUnavailable, SignatureId, TypeAliasId, TypeId,
    TypeMapperId,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession, canonical_anonymous_union,
        instantiate_type_with_vector_and_session,
    },
    mapper::CanonicalTypeMapperStore,
    signatures::Signature,
    type_records::{CacheHashKey, TypeCacheState, TypeData, TypeRecord},
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
    InvalidSignature(SignatureId),
    UnsupportedInference { source: TypeId, target: TypeId },
    TailRecursionLimit { count: usize, limit: usize },
    Instantiation(InstantiationError),
    Relation(RelationUnavailable),
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
            Self::Relation(error) => error.fmt(formatter),
            Self::Union(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ConditionalTypeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Instantiation(error) => Some(error),
            Self::Relation(error) => Some(error),
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
    let assignable =
        extends_any_or_unknown || is_assignable(store, check_type, inferred_extends, global_types)?;

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
        map_type(
            store,
            branches.true_type,
            &combined_parameters,
            &combined_arguments,
            global_types,
            session,
        )
    } else {
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
        TypeData::Conditional(conditional) => {
            contains_mapped_type_parameter(store, conditional.check_type, parameters, visiting)?
                || contains_mapped_type_parameter(
                    store,
                    conditional.extends_type,
                    parameters,
                    visiting,
                )?
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
            TypeData::Conditional(_) => true,
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

    let source_record = store
        .type_payload(source)
        .ok_or(ConditionalTypeError::InvalidType(source))?;
    let target_record = store
        .type_payload(target)
        .ok_or(ConditionalTypeError::InvalidType(target))?;
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

    let source_signature = single_call_signature(source_record.data());
    let target_signature = single_call_signature(target_record.data());
    if let (Some(source_signature), Some(target_signature)) = (source_signature, target_signature) {
        let source_return = store
            .signature(source_signature)
            .and_then(Signature::resolved_return_type)
            .ok_or(ConditionalTypeError::InvalidSignature(source_signature))?;
        let target_return = store
            .signature(target_signature)
            .and_then(Signature::resolved_return_type)
            .ok_or(ConditionalTypeError::InvalidSignature(target_signature))?;
        infer_from_types(
            store,
            source_return,
            target_return,
            parameters,
            candidates,
            global_types,
        )
    } else if contains_type_parameter(store, target, &HashSet::new())? {
        Err(ConditionalTypeError::UnsupportedInference { source, target })
    } else {
        is_assignable(store, source, target, global_types)
    }
}

fn single_call_signature(data: &TypeData) -> Option<SignatureId> {
    let structured = data.structured()?;
    if structured.call_signature_count != 1 {
        return None;
    }
    structured.signatures.as_deref()?.first().copied()
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

fn is_assignable(
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
        CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore, declared::execute_type_parameter,
        mapper::TypeMapper,
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
    fn tail_recursion_stops_at_the_pinned_limit_before_mutation() {
        let mut fixture = Fixture::new("type Result<T> = T extends string ? T : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, never) = (bootstrap.string_type, bootstrap.never_type);
        let branch_types = branches(parameter, never);
        let declared = get_type_from_conditional_type(
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
        let before = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
            fixture.store.mapper_len(),
        );
        assert_eq!(
            get_conditional_type_instantiation_with_tail_count(
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
                CONDITIONAL_TAIL_RECURSION_LIMIT,
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
}
