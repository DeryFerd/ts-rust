//! Canonical conditional-type roots, distribution, and bounded inference.
//!
//! This module follows `getTypeFromConditionalTypeNode`, `getConditionalType`,
//! and `getConditionalTypeInstantiation` in the pinned TypeScript Go checker.
//! Syntax planning and branch resolution remain with the type-node owner.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, SymbolFlags};
use xxhash_rust::xxh3::Xxh3;

use super::{
    CanonicalGlobalTypes, ConditionalRootId, RelationUnavailable, SemanticSymbolId, SignatureId,
    SourceFileRef, TypeAliasId, TypeId, TypeMapperId,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    constraints::{self, ConstraintError},
    declared::{cached_ordinary_type_parameter_owner, malformed_alias_merge},
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession,
        cached_instantiation_with_vector, canonical_anonymous_union, instantiate_type_with_session,
        instantiate_type_with_vector_and_session,
    },
    mapper::CanonicalTypeMapperStore,
    object_members::{StoredDeclaredCallSetValidation, validate_stored_declared_call_set},
    signatures::{ElementFlags, SignatureFlags, TupleElementInfo},
    store::SourceNodeParent,
    template_types::{TemplateTypeError, split_first_template_code_point},
    tuple_types::{CanonicalTupleTypeRequest, TupleTypeError},
    type_nodes::{ConditionalAliasDeclarationProof, ConditionalAliasReferenceProof},
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
    pub alias: Option<&'a ConditionalAliasReferenceProof>,
    pub for_constraint: bool,
}

/// Alias inputs stay borrowed until evaluation returns a deferred type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConditionalAliasIdentity<'a> {
    pub symbol: SemanticSymbolId,
    pub type_arguments: &'a [TypeId],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RetainedConditionalAlias {
    id: TypeAliasId,
    symbol: SemanticSymbolId,
    type_arguments: Vec<TypeId>,
}

impl RetainedConditionalAlias {
    fn identity(&self) -> ConditionalAliasIdentity<'_> {
        ConditionalAliasIdentity {
            symbol: self.symbol,
            type_arguments: &self.type_arguments,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ConditionalDefinition {
    root: ConditionalRootId,
    node: NodeRef,
    check_type: TypeId,
    extends_type: TypeId,
    is_distributive: bool,
    infer_type_parameters: Vec<TypeId>,
    outer_type_parameters: Vec<TypeId>,
    alias: Option<RetainedConditionalAlias>,
}

/// Only conditional evaluation can create this immutable production record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ConditionalTypeProduction {
    type_: TypeId,
    definition: ConditionalDefinition,
    check_type: TypeId,
    extends_type: TypeId,
    mapper: Option<TypeMapperId>,
    mapped_parameters: Vec<TypeId>,
    type_arguments: Vec<TypeId>,
    alias: Option<RetainedConditionalAlias>,
    alias_reference: Option<NodeRef>,
}

impl ConditionalTypeProduction {
    pub(super) const fn type_id(&self) -> TypeId {
        self.type_
    }

    pub(super) const fn root(&self) -> ConditionalRootId {
        self.definition.root
    }
}

/// The source producer and its complete root arguments, before a second mapper.
/// Only the conditional owner can construct this proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ConditionalRemapProjection {
    production: ConditionalTypeProduction,
    arguments: Vec<TypeId>,
}

impl ConditionalRemapProjection {
    pub(super) const fn type_id(&self) -> TypeId {
        self.production.type_
    }

    pub(super) fn parameters(&self) -> &[TypeId] {
        &self.production.definition.outer_type_parameters
    }

    pub(super) fn arguments(&self) -> &[TypeId] {
        &self.arguments
    }

    pub(super) fn alias(&self) -> Option<ConditionalAliasIdentity<'_>> {
        self.production
            .alias
            .as_ref()
            .map(RetainedConditionalAlias::identity)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ConditionalRemapLookup {
    Cold,
    Hit(TypeId),
    NeedsSourceEvaluation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ConditionalRemapResult {
    Deferred(TypeId),
    Recovered(TypeId),
    NeedsSourceEvaluation,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum ConditionalQueryKey {
    Node(NodeRef),
    Instantiation(ConditionalRootId, CacheHashKey),
    AliasReference(NodeRef),
    AliasDeclaration(SemanticSymbolId),
}

/// Mutable checker caches must agree with this retained query result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ConditionalQueryProduction {
    key: ConditionalQueryKey,
    definition: ConditionalDefinition,
    type_arguments: Vec<TypeId>,
    alias: Option<(SemanticSymbolId, Vec<TypeId>)>,
    for_constraint: bool,
    result: TypeId,
    source_declaration: Option<NodeRef>,
    result_alias: Option<RetainedConditionalAlias>,
}

impl ConditionalQueryProduction {
    pub(super) const fn key(&self) -> ConditionalQueryKey {
        self.key
    }

    pub(super) const fn root(&self) -> ConditionalRootId {
        self.definition.root
    }

    pub(super) const fn result(&self) -> TypeId {
        self.result
    }
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
    InvalidAliasSymbol(SemanticSymbolId),
    Capacity,
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
            Self::InvalidAliasSymbol(symbol) => {
                write!(formatter, "invalid conditional alias symbol {symbol:?}")
            }
            Self::Capacity => formatter.write_str("conditional type capacity is unavailable"),
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
    let query_key = ConditionalQueryKey::Node(request.node);
    if store.conditional_query_production(query_key).is_some() {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
    }
    if !store.try_reserve_conditional_productions(0, 1)
        || !store
            .try_reserve_type_node_links(usize::from(store.type_node_links(request.node).is_none()))
    {
        return Err(ConditionalTypeError::Capacity);
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
    let definition = conditional_definition(store, root)?;

    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let result = evaluate_conditional(
        store,
        root,
        request.branches,
        &[],
        &[],
        global_types,
        false,
        None,
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
    let proof = ConditionalQueryProduction {
        key: query_key,
        definition,
        type_arguments: request.outer_type_parameters.to_vec(),
        alias: None,
        for_constraint: false,
        result,
        source_declaration: None,
        result_alias: retain_result_alias(store, result)?,
    };
    validate_query_production(store, &proof)?;
    if !store.publish_conditional_query_production(proof) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
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
    let source_query = if let Some(source) = request.alias {
        if request.for_constraint
            || !source.matches_request(store, request.conditional_type, request.type_arguments)
        {
            return Err(ConditionalTypeError::InvalidTypeNodeCache(
                source.reference(),
            ));
        }
        let definition = validated_conditional_production(store, request.conditional_type)?
            .definition
            .clone();
        let key = ConditionalQueryKey::AliasReference(source.reference());
        let alias = source
            .identity()
            .map(|alias| (alias.symbol, alias.type_arguments.to_vec()));
        if let Some(proof) = store.conditional_query_production(key) {
            if proof.definition != definition
                || proof.type_arguments != request.type_arguments
                || proof.alias != alias
                || proof.for_constraint
            {
                return Err(ConditionalTypeError::InvalidTypeNodeCache(
                    source.reference(),
                ));
            }
            validate_query_production(store, proof)?;
        } else if !store.try_reserve_conditional_productions(0, 1) {
            return Err(ConditionalTypeError::Capacity);
        }
        Some((key, definition, alias))
    } else {
        None
    };
    let result = get_conditional_type_instantiation_with_tail_count(
        store,
        request,
        global_types,
        session,
        0,
    )?;
    if let Some((key, definition, alias)) = source_query {
        if let Some(proof) = store.conditional_query_production(key) {
            if proof.result != result {
                return Err(ConditionalTypeError::InvalidInstantiationCache(
                    definition.root,
                ));
            }
        } else {
            let proof = ConditionalQueryProduction {
                key,
                definition,
                type_arguments: request.type_arguments.to_vec(),
                alias,
                for_constraint: false,
                result,
                source_declaration: None,
                result_alias: retain_result_alias(store, result)?,
            };
            validate_query_production(store, &proof)?;
            if !store.publish_conditional_query_production(proof) {
                return Err(ConditionalTypeError::InvalidConditional(result));
            }
        }
    }
    Ok(result)
}

/// Returns authenticated alias data without evaluating conditional branches.
pub(super) fn conditional_alias_projection(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> Result<Option<ConditionalAliasIdentity<'_>>, ConditionalTypeError> {
    let proof = validated_conditional_production(store, conditional)?;
    Ok(proof.alias.as_ref().map(RetainedConditionalAlias::identity))
}

/// Reconstructs the old mapper without allocating a composite mapper or reading branches.
pub(super) fn conditional_remap_projection(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> Result<ConditionalRemapProjection, ConditionalTypeError> {
    let production = validated_conditional_production(store, conditional)?;
    conditional_snapshot(store, conditional)?;
    let definition = &production.definition;
    let node_query = store
        .conditional_query_production(ConditionalQueryKey::Node(definition.node))
        .ok_or(ConditionalTypeError::InvalidTypeNodeCache(definition.node))?;
    if node_query.definition != *definition
        || store
            .type_node_links(definition.node)
            .and_then(|links| links.resolved_type)
            != Some(node_query.result)
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(definition.node));
    }
    validate_query_production(store, node_query)?;
    if let Some(alias) = &definition.alias {
        validate_remap_source_alias_links(store, alias.identity(), definition)?;
    }
    if let Some(reference) = production.alias_reference {
        let origin = store
            .conditional_query_production(ConditionalQueryKey::AliasReference(reference))
            .ok_or(ConditionalTypeError::InvalidTypeNodeCache(reference))?;
        if origin.definition != *definition
            || origin.alias.as_ref().map(|(symbol, _)| *symbol)
                != production.alias.as_ref().map(|alias| alias.symbol)
            || store
                .type_node_links(reference)
                .and_then(|links| links.resolved_type)
                != Some(origin.result)
        {
            return Err(ConditionalTypeError::InvalidTypeNodeCache(reference));
        }
        validate_query_production(store, origin)?;
        if let Some((symbol, arguments)) = &origin.alias {
            validate_remap_source_alias_links(
                store,
                ConditionalAliasIdentity {
                    symbol: *symbol,
                    type_arguments: arguments,
                },
                definition,
            )?;
        }
    }
    if !production.mapped_parameters.is_empty()
        && production.mapped_parameters != definition.outer_type_parameters
    {
        return Err(ConditionalTypeError::InvalidConditional(conditional));
    }
    let arguments = if production.mapped_parameters.is_empty() {
        definition.outer_type_parameters.clone()
    } else {
        production.type_arguments.clone()
    };
    let projection = ConditionalRemapProjection {
        production: production.clone(),
        arguments,
    };
    // A distributed constituent may have no separate root-cache entry. An
    // existing entry or retained query must still pass the complete cache proof.
    remap_cached_result(
        store,
        &projection,
        projection.arguments(),
        projection.alias(),
    )?;
    validate_remap_capture_source(store, &projection)?;
    Ok(projection)
}

fn validate_remap_capture_source(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
) -> Result<(), ConditionalTypeError> {
    let unsupported = || {
        ConditionalTypeError::Instantiation(InstantiationError::UnsupportedType(
            projection.type_id(),
        ))
    };
    let invalid = || ConditionalTypeError::InvalidConditional(projection.type_id());
    let definition = &projection.production.definition;
    let alias = definition.alias.as_ref().ok_or_else(unsupported)?;
    let invalid_owner = || ConditionalTypeError::InvalidAliasSymbol(alias.symbol);
    let [declaration] = store
        .symbol(alias.symbol)
        .and_then(|symbol| symbol.declarations())
        .ok_or_else(invalid_owner)?
    else {
        return Err(invalid_owner());
    };
    if declaration.arena != definition.node.arena || declaration.file != definition.node.file {
        return Err(invalid_owner());
    }
    if !remap_alias_scope_is_supported(store, *declaration, alias.symbol)? {
        return Err(unsupported());
    }
    // This source-only header proves every own parameter and excludes enclosing
    // generic scopes. Inline roots do not yet retain a complete capture proof.
    let header =
        super::object_aliases::property_object_alias_identity_source_header(store, alias.symbol)
            .map_err(|_| invalid_owner())?;
    let mut node = store
        .source_direct_type_annotation(header.alias_declaration)
        .ok_or_else(invalid)?;
    let mut visited = HashSet::new();
    while node != definition.node {
        if !visited.insert(node)
            || store.source_node_kind(node) != Some(SyntaxKind::ParenthesizedType)
        {
            return Err(invalid());
        }
        let children = store.source_direct_children(node).ok_or_else(invalid)?;
        let [child] = children.as_slice() else {
            return Err(invalid());
        };
        if child.arena != node.arena
            || child.file != node.file
            || store.source_node_parent(*child) != Some(SourceNodeParent::Parent(node))
        {
            return Err(invalid());
        }
        node = *child;
    }
    if header.alias_symbol != alias.symbol
        || definition.outer_type_parameters != alias.type_arguments
        || header.parameters.len() != definition.outer_type_parameters.len()
        || header
            .parameters
            .iter()
            .zip(&definition.outer_type_parameters)
            .any(|((_, symbol), parameter)| {
                cached_ordinary_type_parameter_owner(store, *parameter) != Some(*symbol)
            })
    {
        return Err(invalid());
    }
    Ok(())
}

fn remap_alias_scope_is_supported(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    alias: SemanticSymbolId,
) -> Result<bool, ConditionalTypeError> {
    let invalid = || ConditionalTypeError::InvalidAliasSymbol(alias);
    let mut node = declaration;
    let mut visited = HashSet::from([node]);
    let mut unsupported_capture =
        store.source_node_kind(node).ok_or_else(invalid)? != SyntaxKind::TypeAliasDeclaration;
    loop {
        match store.source_node_parent(node).ok_or_else(invalid)? {
            SourceNodeParent::Root => {
                if store.source_node_kind(node) != Some(SyntaxKind::SourceFile)
                    || !store.contains_source_file(SourceFileRef::new(store.id(), node))
                {
                    return Err(invalid());
                }
                return Ok(!unsupported_capture);
            }
            SourceNodeParent::Parent(parent) => {
                if parent.arena != declaration.arena
                    || parent.file != declaration.file
                    || !visited.insert(parent)
                {
                    return Err(invalid());
                }
                let kind = store.source_node_kind(parent).ok_or_else(invalid)?;
                let children = store.source_direct_children(parent).ok_or_else(invalid)?;
                if children.iter().filter(|&&child| child == node).count() != 1
                    || children.iter().any(|child| {
                        child.arena != declaration.arena
                            || child.file != declaration.file
                            || store.source_node_kind(*child).is_none()
                            || store.source_node_parent(*child)
                                != Some(SourceNodeParent::Parent(parent))
                    })
                {
                    return Err(invalid());
                }
                unsupported_capture |= !matches!(
                    kind,
                    SyntaxKind::SourceFile
                        | SyntaxKind::ModuleBlock
                        | SyntaxKind::ModuleDeclaration
                );
                node = parent;
            }
        }
    }
}

fn validate_remap_source_alias_links(
    store: &CanonicalTypeMapperStore,
    source: ConditionalAliasIdentity<'_>,
    definition: &ConditionalDefinition,
) -> Result<(), ConditionalTypeError> {
    let invalid = || ConditionalTypeError::InvalidAliasSymbol(source.symbol);
    let links = store.type_alias_links(source.symbol);
    if links.is_some_and(|links| {
        links.is_constructor_declared_property
            || links
                .type_parameters
                .as_deref()
                .is_some_and(|parameters| parameters != source.type_arguments)
    }) {
        return Err(invalid());
    }
    let Some(proof) =
        store.conditional_query_production(ConditionalQueryKey::AliasDeclaration(source.symbol))
    else {
        // A direct query of the conditional node may precede alias publication.
        // That cold state cannot excuse contradictory installed alias results.
        return if links.is_some_and(|links| {
            links.declared_type.is_some()
                || links
                    .instantiations
                    .as_ref()
                    .is_some_and(|cache| !cache.is_empty())
        }) {
            Err(invalid())
        } else {
            Ok(())
        };
    };
    let links = links.ok_or_else(invalid)?;
    if proof.definition != *definition || links.declared_type != Some(proof.result) {
        return Err(invalid());
    }
    validate_conditional_alias_declaration(store, source.symbol, proof.result)?;
    if proof.type_arguments.is_empty() {
        if links
            .instantiations
            .as_ref()
            .is_some_and(|cache| !cache.is_empty())
        {
            return Err(invalid());
        }
    } else if links
        .instantiations
        .as_ref()
        .and_then(|cache| cache.get(&super::declared::type_list_key(&proof.type_arguments)))
        != Some(&proof.result)
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_conditional_remap_inputs(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
) -> Result<(), ConditionalTypeError> {
    if conditional_remap_projection(store, projection.type_id())? != *projection {
        return Err(ConditionalTypeError::InvalidConditional(
            projection.type_id(),
        ));
    }
    if arguments.len() != projection.parameters().len() {
        return Err(ConditionalTypeError::InvalidInstantiationArity {
            expected: projection.parameters().len(),
            actual: arguments.len(),
        });
    }
    let mut visiting = HashSet::new();
    for argument in arguments {
        validate_conditional_operand(store, *argument, &mut visiting)?;
    }
    if alias.map(|alias| (alias.symbol, alias.type_arguments.len()))
        != projection
            .alias()
            .map(|alias| (alias.symbol, alias.type_arguments.len()))
    {
        return Err(ConditionalTypeError::InvalidConditional(
            projection.type_id(),
        ));
    }
    if let Some(alias) = alias {
        validate_alias_identity(store, alias, &mut visiting)?;
    }
    // Without a real alias-reference origin the visible alias is the root alias.
    // A remap cannot create a new source alias or claim a new reference node.
    if projection.production.alias_reference.is_none() {
        let expected = mapped_root_alias(
            store,
            projection.production.definition.root,
            projection.parameters(),
            arguments,
        )?;
        if alias
            != expected
                .as_ref()
                .map(|(symbol, arguments)| ConditionalAliasIdentity {
                    symbol: *symbol,
                    type_arguments: arguments,
                })
        {
            return Err(ConditionalTypeError::InvalidConditional(
                projection.type_id(),
            ));
        }
    }
    Ok(())
}

fn remap_query_alias<'a>(
    projection: &ConditionalRemapProjection,
    alias: Option<ConditionalAliasIdentity<'a>>,
) -> Option<ConditionalAliasIdentity<'a>> {
    projection.production.alias_reference.and(alias)
}

fn remap_cache_key(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
) -> Result<CacheHashKey, ConditionalTypeError> {
    let alias = remap_query_alias(projection, alias)
        .map(|alias| {
            store
                .symbol_store()
                .assigned_global_symbol_id(alias.symbol)
                .map(|symbol| (symbol, alias.type_arguments))
                .ok_or(ConditionalTypeError::InvalidAliasSymbol(alias.symbol))
        })
        .transpose()?;
    Ok(conditional_type_key_parts(arguments, alias, false))
}

fn remap_cached_result(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    let root = projection.production.definition.root;
    let record = store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?;
    let cache = match record.instantiations() {
        TypeCacheState::Unallocated if projection.parameters().is_empty() => return Ok(None),
        TypeCacheState::Allocated(cache) if !projection.parameters().is_empty() => cache,
        _ => return Err(ConditionalTypeError::InvalidInstantiationCache(root)),
    };
    let key = remap_cache_key(store, projection, arguments, alias)?;
    let Some(cached) = cache.get(&key).copied() else {
        return if store
            .conditional_query_production(ConditionalQueryKey::Instantiation(root, key))
            .is_some()
        {
            Err(ConditionalTypeError::InvalidInstantiationCache(root))
        } else {
            Ok(None)
        };
    };
    validate_cached_instantiation(
        store,
        root,
        key,
        cached,
        projection.parameters(),
        arguments,
        remap_query_alias(projection, alias),
        false,
    )?;
    Ok(Some(cached))
}

/// A proved subset of Go's `isDeferredType`. A reference such as Array<T>
/// does not qualify merely because one of its arguments is a type parameter.
fn remap_check_stays_deferred(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    visiting: &mut HashSet<TypeId>,
) -> Result<bool, ConditionalTypeError> {
    if !visiting.insert(type_) {
        return Err(ConditionalTypeError::InvalidType(type_));
    }
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    let result = match record.data() {
        TypeData::TypeParameter(_) => record.flags() == TypeFlags::TYPE_PARAMETER,
        TypeData::Conditional(_) => {
            validated_conditional_production(store, type_)?;
            true
        }
        TypeData::IndexedAccess(indexed) => {
            if super::indexed_access_types::cached_deferred_indexed_access_type(
                store,
                indexed.object_type,
                indexed.index_type,
                indexed.access_flags,
            )
            .map_err(ConditionalTypeError::InvalidType)?
                != Some(type_)
            {
                return Err(ConditionalTypeError::InvalidType(type_));
            }
            true
        }
        TypeData::Index(_) => {
            super::keyof_types::validate_generic_keyof_index_type(store, type_)
                .map_err(|_| ConditionalTypeError::InvalidType(type_))?;
            true
        }
        TypeData::Union(data) => data.union.types.iter().try_fold(false, |generic, type_| {
            Ok::<_, ConditionalTypeError>(
                generic | remap_check_stays_deferred(store, *type_, visiting)?,
            )
        })?,
        TypeData::Intersection(data) => {
            data.intersection
                .types
                .iter()
                .try_fold(false, |generic, type_| {
                    Ok::<_, ConditionalTypeError>(
                        generic | remap_check_stays_deferred(store, *type_, visiting)?,
                    )
                })?
        }
        _ => false,
    };
    visiting.remove(&type_);
    Ok(result)
}

fn remap_can_defer(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    check_type: TypeId,
    extends_type: TypeId,
) -> Result<bool, ConditionalTypeError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    if [check_type, extends_type]
        .iter()
        .any(|type_| *type_ == bootstrap.error_type || *type_ == bootstrap.wildcard_type)
        || (projection.production.definition.is_distributive
            && type_flags(store, check_type)?.intersects(TypeFlags::UNION | TypeFlags::NEVER))
    {
        return Ok(false);
    }
    remap_check_stays_deferred(store, check_type, &mut HashSet::new())
}

/// Read-only replay checks deferral before accepting even a valid concrete cache hit.
pub(super) fn cached_deferred_conditional_remap(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ConditionalRemapLookup, ConditionalTypeError> {
    validate_conditional_remap_inputs(store, projection, arguments, alias)?;
    let cached = remap_cached_result(store, projection, arguments, alias)?;
    let definition = &projection.production.definition;
    let mapped = [definition.check_type, definition.extends_type].map(|type_| {
        cached_instantiation_with_vector(
            store,
            type_,
            projection.parameters(),
            arguments,
            array_targets,
            None,
        )
    });
    let [check, extends] = mapped;
    let (Some(check), Some(extends)) = (check?, extends?) else {
        return Ok(ConditionalRemapLookup::Cold);
    };
    if !remap_can_defer(store, projection, check, extends)? {
        return Ok(ConditionalRemapLookup::NeedsSourceEvaluation);
    }
    if let Some(cached) = cached {
        let result = validated_conditional_production(store, cached)?;
        if result.definition != *definition
            || result.check_type != check
            || result.extends_type != extends
            || result
                .alias
                .as_ref()
                .map(RetainedConditionalAlias::identity)
                != alias
        {
            return Err(ConditionalTypeError::InvalidInstantiationCache(
                definition.root,
            ));
        }
        Ok(ConditionalRemapLookup::Hit(cached))
    } else if arguments == projection.arguments() && alias == projection.alias() {
        Ok(ConditionalRemapLookup::Hit(projection.type_id()))
    } else {
        Ok(ConditionalRemapLookup::Cold)
    }
}

/// Remaps only a still-deferred conditional. Branch nodes and lazy branch caches
/// are not inputs to this operation and remain owned by the source query.
pub(super) fn remap_deferred_conditional_with_session(
    store: &mut CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<ConditionalRemapResult, ConditionalTypeError> {
    match cached_deferred_conditional_remap(store, projection, arguments, alias, array_targets)? {
        ConditionalRemapLookup::Hit(type_) => return Ok(ConditionalRemapResult::Deferred(type_)),
        ConditionalRemapLookup::NeedsSourceEvaluation => {
            return Ok(ConditionalRemapResult::NeedsSourceEvaluation);
        }
        ConditionalRemapLookup::Cold => {}
    }
    let definition = &projection.production.definition;
    let mark = session.limit_event_mark();
    let mut operands = Vec::with_capacity(2);
    for operand in [definition.check_type, definition.extends_type] {
        operands.push(instantiate_type_with_vector_and_session(
            store,
            operand,
            projection.parameters(),
            arguments,
            array_targets,
            session,
        )?);
        if session.limit_event_occurred_since(mark)
            && let Some(error) = session.recovery_error_type()
        {
            return Ok(ConditionalRemapResult::Recovered(error));
        }
    }
    let (check_type, extends_type) = (operands[0], operands[1]);
    if !remap_can_defer(store, projection, check_type, extends_type)? {
        return Ok(ConditionalRemapResult::NeedsSourceEvaluation);
    }
    // Dependency demand may have completed an existing root entry. Validate it
    // again before reserving or publishing any conditional result.
    if let ConditionalRemapLookup::Hit(cached) =
        cached_deferred_conditional_remap(store, projection, arguments, alias, array_targets)?
    {
        return Ok(ConditionalRemapResult::Deferred(cached));
    }
    let root = definition.root;
    let key = remap_cache_key(store, projection, arguments, alias)?;
    let TypeCacheState::Allocated(cache) = store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?
        .instantiations()
    else {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    };
    let mut cache = cache.clone();
    if !store.try_reserve_conditional_productions(0, 1) {
        return Err(ConditionalTypeError::Capacity);
    }
    let alias_source = projection
        .production
        .alias_reference
        .zip(alias)
        .map(|(reference, alias)| (alias, reference));
    let result = deferred_conditional(
        store,
        root,
        check_type,
        extends_type,
        projection.parameters(),
        arguments,
        alias_source,
    )?;
    cache.insert(key, result);
    if !store.set_conditional_root_instantiations(root, TypeCacheState::Allocated(cache)) {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    let proof = ConditionalQueryProduction {
        key: ConditionalQueryKey::Instantiation(root, key),
        definition: definition.clone(),
        type_arguments: arguments.to_vec(),
        alias: remap_query_alias(projection, alias)
            .map(|alias| (alias.symbol, alias.type_arguments.to_vec())),
        for_constraint: false,
        result,
        source_declaration: None,
        result_alias: retain_result_alias(store, result)?,
    };
    validate_query_production(store, &proof)?;
    if !store.publish_conditional_query_production(proof) {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    Ok(ConditionalRemapResult::Deferred(result))
}

/// A reduced conditional keeps its source root's alias separate from its result.
pub(super) fn conditional_query_alias(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<Option<TypeAliasId>, ConditionalTypeError> {
    let proof = store
        .conditional_query_production(ConditionalQueryKey::Node(node))
        .ok_or(ConditionalTypeError::InvalidTypeNodeCache(node))?;
    validate_query_production(store, proof)?;
    if store
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        != Some(proof.result)
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(node));
    }
    Ok(proof.definition.alias.as_ref().map(|alias| alias.id))
}

pub(super) fn validate_conditional_reference_result(
    store: &CanonicalTypeMapperStore,
    reference: NodeRef,
    result: TypeId,
) -> Result<bool, ConditionalTypeError> {
    let Some(proof) =
        store.conditional_query_production(ConditionalQueryKey::AliasReference(reference))
    else {
        return Ok(false);
    };
    if proof.result != result {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(reference));
    }
    validate_query_production(store, proof)?;
    Ok(true)
}

pub(super) fn record_conditional_alias_declaration(
    store: &mut CanonicalTypeMapperStore,
    source: &ConditionalAliasDeclarationProof,
) -> Result<(), ConditionalTypeError> {
    if !source.matches_source(store) {
        return Err(ConditionalTypeError::InvalidAliasSymbol(source.symbol()));
    }
    let definition = validated_conditional_production(store, source.result())?
        .definition
        .clone();
    let key = ConditionalQueryKey::AliasDeclaration(source.symbol());
    if let Some(proof) = store.conditional_query_production(key) {
        if proof.result != source.result()
            || proof.definition != definition
            || proof.source_declaration != Some(source.declaration())
            || proof.type_arguments != source.type_parameters()
        {
            return Err(ConditionalTypeError::InvalidAliasSymbol(source.symbol()));
        }
        return validate_query_production(store, proof);
    }
    if !store.try_reserve_conditional_productions(0, 1) {
        return Err(ConditionalTypeError::Capacity);
    }
    let proof = ConditionalQueryProduction {
        key,
        definition,
        type_arguments: source.type_parameters().to_vec(),
        alias: None,
        for_constraint: false,
        result: source.result(),
        source_declaration: Some(source.declaration()),
        result_alias: retain_result_alias(store, source.result())?,
    };
    if !store.publish_conditional_query_production(proof) {
        return Err(ConditionalTypeError::InvalidAliasSymbol(source.symbol()));
    }
    Ok(())
}

pub(super) fn validate_conditional_alias_declaration(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    result: TypeId,
) -> Result<(), ConditionalTypeError> {
    let Some(proof) =
        store.conditional_query_production(ConditionalQueryKey::AliasDeclaration(symbol))
    else {
        return if matches!(
            store.type_payload(result).map(TypeRecord::data),
            Some(TypeData::Conditional(_))
        ) {
            Err(ConditionalTypeError::InvalidAliasSymbol(symbol))
        } else {
            Ok(())
        };
    };
    if proof.result != result {
        return Err(ConditionalTypeError::InvalidAliasSymbol(symbol));
    }
    validate_query_production(store, proof)
}

fn retain_conditional_alias(
    store: &CanonicalTypeMapperStore,
    alias: Option<TypeAliasId>,
) -> Result<Option<RetainedConditionalAlias>, ConditionalTypeError> {
    alias
        .map(|id| {
            let identity = stored_alias_identity(store, id)?;
            validate_alias_identity(store, identity, &mut HashSet::new())?;
            Ok(RetainedConditionalAlias {
                id,
                symbol: identity.symbol,
                type_arguments: identity.type_arguments.to_vec(),
            })
        })
        .transpose()
}

fn retain_result_alias(
    store: &CanonicalTypeMapperStore,
    result: TypeId,
) -> Result<Option<RetainedConditionalAlias>, ConditionalTypeError> {
    let record = store
        .type_payload(result)
        .ok_or(ConditionalTypeError::InvalidType(result))?;
    record
        .alias()
        .map(|id| {
            let alias = stored_alias_identity(store, id)?;
            Ok(RetainedConditionalAlias {
                id,
                symbol: alias.symbol,
                type_arguments: alias.type_arguments.to_vec(),
            })
        })
        .transpose()
}

fn conditional_definition(
    store: &CanonicalTypeMapperStore,
    root: ConditionalRootId,
) -> Result<ConditionalDefinition, ConditionalTypeError> {
    let record = store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?;
    Ok(ConditionalDefinition {
        root,
        node: record.node(),
        check_type: record.check_type(),
        extends_type: record.extends_type(),
        is_distributive: record.is_distributive(),
        infer_type_parameters: record.infer_type_parameters().unwrap_or_default().to_vec(),
        outer_type_parameters: record.outer_type_parameters().unwrap_or_default().to_vec(),
        alias: retain_conditional_alias(store, record.alias())?,
    })
}

fn validate_conditional_definition(
    store: &CanonicalTypeMapperStore,
    definition: &ConditionalDefinition,
) -> Result<(), ConditionalTypeError> {
    if conditional_definition(store, definition.root)? != *definition {
        return Err(ConditionalTypeError::InvalidRoot(definition.root));
    }
    validate_root_alias(
        store,
        definition.node,
        &definition.outer_type_parameters,
        definition.alias.as_ref().map(|alias| alias.id),
    )
}

fn validated_conditional_production(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> Result<&ConditionalTypeProduction, ConditionalTypeError> {
    let invalid = || ConditionalTypeError::InvalidConditional(conditional);
    let proof = store
        .conditional_type_production(conditional)
        .ok_or_else(invalid)?;
    let record = store.type_payload(conditional).ok_or_else(invalid)?;
    let TypeData::Conditional(data) = record.data() else {
        return Err(invalid());
    };
    // Deferred production currently leaves combined_mapper unset.
    if record.flags() != TypeFlags::CONDITIONAL
        || record.symbol().is_some()
        || data.root != proof.definition.root
        || data.check_type != proof.check_type
        || data.extends_type != proof.extends_type
        || data.mapper != proof.mapper
        || data.combined_mapper.is_some()
        || retain_conditional_alias(store, record.alias())? != proof.alias
    {
        return Err(invalid());
    }
    validate_conditional_definition(store, &proof.definition)?;
    if let Some(reference) = proof.alias_reference {
        let alias = proof.alias.as_ref().ok_or_else(invalid)?;
        validate_conditional_alias_reference_owner(store, reference, alias.symbol)?;
    }
    if let Some(mapper) = proof.mapper {
        if store.type_mapper_has_exact_endpoints(
            mapper,
            &proof.mapped_parameters,
            &proof.type_arguments,
        ) != Some(true)
        {
            return Err(ConditionalTypeError::InvalidMapper(mapper));
        }
    } else if proof.mapped_parameters != proof.type_arguments {
        return Err(invalid());
    }
    Ok(proof)
}

fn validate_query_production(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalQueryProduction,
) -> Result<(), ConditionalTypeError> {
    validate_conditional_definition(store, &proof.definition)?;
    if let ConditionalQueryKey::AliasReference(reference) = proof.key
        && let Some((symbol, _)) = proof.alias.as_ref()
    {
        validate_conditional_alias_reference_owner(store, reference, *symbol)?;
    }
    if retain_result_alias(store, proof.result)? != proof.result_alias {
        return Err(ConditionalTypeError::InvalidInstantiationCache(
            proof.definition.root,
        ));
    }
    let result =
        store
            .type_payload(proof.result)
            .ok_or(ConditionalTypeError::InvalidInstantiationCache(
                proof.definition.root,
            ))?;
    if matches!(result.data(), TypeData::Conditional(_)) {
        validated_conditional_production(store, proof.result)?;
    }
    let root = store
        .conditional_root(proof.definition.root)
        .ok_or(ConditionalTypeError::InvalidRoot(proof.definition.root))?;
    let cache_key = match proof.key {
        ConditionalQueryKey::AliasDeclaration(symbol) => {
            validate_alias_identity(
                store,
                ConditionalAliasIdentity {
                    symbol,
                    type_arguments: &proof.type_arguments,
                },
                &mut HashSet::new(),
            )?;
            let Some(declaration) = proof.source_declaration else {
                return Err(ConditionalTypeError::InvalidAliasSymbol(symbol));
            };
            if store
                .symbol(symbol)
                .and_then(|symbol| symbol.declarations())
                != Some(&[declaration][..])
                || store
                    .type_alias_links(symbol)
                    .and_then(|links| links.type_parameters.as_deref())
                    .unwrap_or_default()
                    != proof.type_arguments
            {
                return Err(ConditionalTypeError::InvalidAliasSymbol(symbol));
            }
            return Ok(());
        }
        ConditionalQueryKey::Node(_) | ConditionalQueryKey::AliasReference(_)
            if proof.definition.outer_type_parameters.is_empty() =>
        {
            return if root.instantiations() == &TypeCacheState::Unallocated {
                Ok(())
            } else {
                Err(ConditionalTypeError::InvalidInstantiationCache(
                    proof.definition.root,
                ))
            };
        }
        ConditionalQueryKey::Node(_) => {
            conditional_type_key_parts(&proof.definition.outer_type_parameters, None, false)
        }
        ConditionalQueryKey::Instantiation(_, key) => key,
        ConditionalQueryKey::AliasReference(_) => {
            let alias = proof
                .alias
                .as_ref()
                .map(|(symbol, arguments)| {
                    store
                        .symbol_store()
                        .assigned_global_symbol_id(*symbol)
                        .map(|symbol| (symbol, arguments.as_slice()))
                        .ok_or(ConditionalTypeError::InvalidAliasSymbol(*symbol))
                })
                .transpose()?;
            conditional_type_key_parts(&proof.type_arguments, alias, proof.for_constraint)
        }
    };
    if !matches!(root.instantiations(), TypeCacheState::Allocated(cache) if cache.get(&cache_key) == Some(&proof.result))
    {
        return Err(ConditionalTypeError::InvalidInstantiationCache(
            proof.definition.root,
        ));
    }
    Ok(())
}

fn validate_conditional_alias_reference_owner(
    store: &CanonicalTypeMapperStore,
    reference: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), ConditionalTypeError> {
    let declaration = conditional_alias_declaration(store, reference)
        .ok_or(ConditionalTypeError::InvalidAliasSymbol(symbol))?;
    if store.source_node_kind(reference) != Some(SyntaxKind::TypeReference)
        || store
            .symbol(symbol)
            .and_then(|symbol| symbol.declarations())
            != Some(&[declaration][..])
    {
        return Err(ConditionalTypeError::InvalidAliasSymbol(symbol));
    }
    Ok(())
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
        let declared_call_set_constraint = store
            .type_payload(data.check_type)
            .and_then(|record| match record.data() {
                TypeData::TypeParameter(parameter) => parameter.constraint,
                _ => None,
            })
            .filter(|constraint| {
                matches!(
                    validate_stored_declared_call_set(store, *constraint),
                    StoredDeclaredCallSetValidation::Valid(_)
                )
            });
        let constraint = if declared_call_set_constraint.is_some() {
            declared_call_set_constraint
        } else {
            match constraints::get_constraint_of_type(store, data.check_type) {
                Ok(constraint) => constraint,
                Err(ConstraintError::UnresolvedTypeParameter(type_))
                    if type_ == data.check_type =>
                {
                    None
                }
                Err(error) => return Err(error.into()),
            }
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
    if store.conditional_type_production(conditional).is_some() {
        validated_conditional_production(store, conditional)?;
    }
    match store.type_payload(conditional).map(TypeRecord::data) {
        Some(TypeData::Conditional(data)) => {
            let root = store
                .conditional_root(data.root)
                .ok_or(ConditionalTypeError::InvalidRoot(data.root))?;
            if store.source_node_kind(root.node()) != Some(SyntaxKind::ConditionalType) {
                return Err(ConditionalTypeError::InvalidNode(root.node()));
            }
            validate_root_alias(
                store,
                root.node(),
                root.outer_type_parameters().unwrap_or_default(),
                root.alias(),
            )?;
            let mut visiting = HashSet::new();
            if let Some(alias) = store.type_payload(conditional).and_then(TypeRecord::alias) {
                validate_alias_identity(
                    store,
                    stored_alias_identity(store, alias)?,
                    &mut visiting,
                )?;
            }
            for type_ in [
                data.check_type,
                data.extends_type,
                root.check_type(),
                root.extends_type(),
            ] {
                validate_conditional_operand(store, type_, &mut visiting)?;
            }
            Ok(data.clone())
        }
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
    let definition = validated_conditional_production(store, request.conditional_type)?
        .definition
        .clone();
    validate_branch_types(store, request.branches)?;
    if let Some(proof) = request.alias
        && !proof.matches_request(store, request.conditional_type, request.type_arguments)
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            proof.reference(),
        ));
    }
    let alias = request
        .alias
        .and_then(ConditionalAliasReferenceProof::identity);
    let alias_source = request.alias.and_then(|proof| {
        proof
            .identity()
            .map(|identity| (identity, proof.reference()))
    });
    if let Some(alias) = alias {
        validate_alias_identity(store, alias, &mut HashSet::new())?;
    }

    let data = conditional_snapshot(store, request.conditional_type)?;
    let (root, existing_mapper) = (data.root, data.mapper);
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
    let mut visiting = HashSet::new();
    for argument in request.type_arguments {
        validate_conditional_operand(store, *argument, &mut visiting)?;
    }

    let key = conditional_type_key(store, request.type_arguments, alias, request.for_constraint)?;
    if let Some(cached) = cached_values.get(&key).copied() {
        validate_cached_instantiation(
            store,
            root,
            key,
            cached,
            &outer_parameters,
            request.type_arguments,
            alias,
            request.for_constraint,
        )?;
        return Ok(cached);
    }
    let query_key = ConditionalQueryKey::Instantiation(root, key);
    if store.conditional_query_production(query_key).is_some() {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    if !store.try_reserve_conditional_productions(0, 1) {
        return Err(ConditionalTypeError::Capacity);
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
                        None,
                        session,
                        tail_count,
                    )?);
                }
                union_result_with_alias(store, &results, global_types, alias)?
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
                alias_source,
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
            alias_source,
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
    let proof = ConditionalQueryProduction {
        key: query_key,
        definition,
        type_arguments: request.type_arguments.to_vec(),
        alias: alias.map(|alias| (alias.symbol, alias.type_arguments.to_vec())),
        for_constraint: request.for_constraint,
        result,
        source_declaration: None,
        result_alias: retain_result_alias(store, result)?,
    };
    validate_query_production(store, &proof)?;
    if !store.publish_conditional_query_production(proof) {
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
    alias: Option<(ConditionalAliasIdentity<'_>, NodeRef)>,
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

    if infer_parameters.is_empty()
        && let Some(simplified) = trivial_conditional_identity(
            store,
            check_type,
            extends_type,
            branches,
            mapped_parameters,
            type_arguments,
        )?
    {
        return Ok(simplified);
    }

    let mut resolved_check_parameters = HashSet::new();
    for (parameter, argument) in mapped_parameters.iter().zip(type_arguments) {
        if !contains_type_parameter(store, *argument, &HashSet::new())? {
            resolved_check_parameters.insert(*parameter);
        }
    }
    if contains_type_parameter(store, check_type, &resolved_check_parameters)? {
        return deferred_conditional(
            store,
            root,
            check_type,
            extends_type,
            mapped_parameters,
            type_arguments,
            alias,
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
            ConditionalInferenceContext {
                infer_parameters: &infer_parameters,
                mapped_parameters,
                type_arguments,
                global_types,
            },
            &mut candidates,
            session,
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
            let inferred = match candidates.as_slice() {
                [] => unknown_type,
                [candidate] => *candidate,
                _ => union_result(store, &candidates, global_types)?,
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
    let resolved_parameters = combined_parameters.iter().copied().collect::<HashSet<_>>();
    if contains_type_parameter(store, inferred_extends, &resolved_parameters)? {
        return deferred_conditional(
            store,
            root,
            check_type,
            extends_type,
            mapped_parameters,
            type_arguments,
            alias,
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

fn trivial_conditional_identity(
    store: &CanonicalTypeMapperStore,
    check_type: TypeId,
    extends_type: TypeId,
    branches: ConditionalTypeBranches,
    mapped_parameters: &[TypeId],
    type_arguments: &[TypeId],
) -> Result<Option<TypeId>, ConditionalTypeError> {
    if mapped_parameters.is_empty() {
        return Ok(None);
    }

    let mapped_branch = |branch: TypeId| {
        mapped_parameters
            .iter()
            .position(|parameter| *parameter == branch)
            .map_or(Ok(branch), |index| {
                type_arguments.get(index).copied().ok_or(
                    ConditionalTypeError::InvalidInstantiationArity {
                        expected: mapped_parameters.len(),
                        actual: type_arguments.len(),
                    },
                )
            })
    };
    let true_type = mapped_branch(branches.true_type)?;
    let false_type = mapped_branch(branches.false_type)?;
    if true_type == check_type && false_type == check_type {
        return Ok(Some(check_type));
    }

    let never = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?
        .never_type;
    let check_flags = type_flags(store, check_type)?;
    let extends_flags = type_flags(store, extends_type)?;
    let disjoint = extends_flags.intersects(TypeFlags::NEVER)
        || conditional_operands_have_disjoint_primitive_domains(store, check_type, extends_type);
    if true_type == check_type && false_type == never {
        if check_flags.intersects(TypeFlags::ANY)
            || check_type == extends_type
            || extends_flags.intersects(TypeFlags::ANY_OR_UNKNOWN)
        {
            return Ok(Some(check_type));
        }
        if disjoint {
            return Ok(Some(never));
        }
    }
    if true_type == never && false_type == check_type {
        if check_type == extends_type || extends_flags.intersects(TypeFlags::ANY_OR_UNKNOWN) {
            return Ok(Some(never));
        }
        if check_flags.intersects(TypeFlags::ANY) || disjoint {
            return Ok(Some(check_type));
        }
    }

    Ok(None)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum ConditionalPrimitiveDomain {
    String,
    Number,
    BigInt,
    Boolean,
    Symbol,
}

const MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS: usize = 16;
const MAX_CONDITIONAL_PRIMITIVE_COMPARISONS: usize = 64;

pub(super) fn conditional_operands_have_disjoint_primitive_domains(
    store: &CanonicalTypeMapperStore,
    check_type: TypeId,
    extends_type: TypeId,
) -> bool {
    let Some(check) = conditional_primitive_operand_identity(store, check_type) else {
        return false;
    };
    let Some(extends) = conditional_primitive_operand_identity(store, extends_type) else {
        return false;
    };
    let Some(check_count) = conditional_primitive_operand_count(store, check) else {
        return false;
    };
    let Some(extends_count) = conditional_primitive_operand_count(store, extends) else {
        return false;
    };
    if check_count
        .checked_mul(extends_count)
        .is_none_or(|count| count > MAX_CONDITIONAL_PRIMITIVE_COMPARISONS)
    {
        return false;
    }

    if check_count == 1 && extends_count == 1 {
        let Some(check) = conditional_primitive_leaf(store, check) else {
            return false;
        };
        let Some(extends) = conditional_primitive_leaf(store, extends) else {
            return false;
        };
        return conditional_primitive_pair_is_disjoint(store, check, extends);
    }

    let Some(checks) = conditional_primitive_operands(store, check) else {
        return false;
    };
    let Some(bounds) = conditional_primitive_operands(store, extends) else {
        return false;
    };
    checks.iter().all(|check| {
        bounds
            .iter()
            .all(|bound| conditional_primitive_pair_is_disjoint(store, *check, *bound))
    })
}

fn conditional_primitive_operand_identity(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<TypeId> {
    let record = store.type_payload(type_)?;
    match record.data() {
        TypeData::TypeParameter(parameter) => {
            cached_ordinary_type_parameter_owner(store, type_)?;
            let constraint = parameter.constraint?;
            let bootstrap = store.intrinsic_bootstrap()?;
            if [
                bootstrap.no_constraint_type,
                bootstrap.circular_constraint_type,
                bootstrap.error_type,
                bootstrap.wildcard_type,
            ]
            .contains(&constraint)
            {
                return None;
            }
            Some(constraint)
        }
        _ => Some(type_),
    }
}

fn conditional_primitive_operand_count(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<usize> {
    let record = store.type_payload(type_)?;
    match record.data() {
        TypeData::Union(union)
            if (2..=MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS)
                .contains(&union.union.types.len()) =>
        {
            Some(union.union.types.len())
        }
        TypeData::Union(_) => None,
        _ => conditional_primitive_domain(record.flags()).map(|_| 1),
    }
}

fn conditional_primitive_operands(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<(TypeId, ConditionalPrimitiveDomain)>> {
    let record = store.type_payload(type_)?;
    let TypeData::Union(union) = record.data() else {
        return conditional_primitive_leaf(store, type_).map(|value| vec![value]);
    };
    if !(2..=MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS).contains(&union.union.types.len())
        || union.union.types.iter().any(|constituent| {
            store
                .type_payload(*constituent)
                .and_then(|record| conditional_primitive_domain(record.flags()))
                .is_none()
        })
        || store.validate_union_constituent(type_).is_err()
    {
        return None;
    }

    union
        .union
        .types
        .iter()
        .map(|constituent| conditional_primitive_leaf(store, *constituent))
        .collect()
}

fn conditional_primitive_leaf(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<(TypeId, ConditionalPrimitiveDomain)> {
    let domain = conditional_primitive_domain(store.type_payload(type_)?.flags())?;
    if store.validate_union_constituent(type_).is_err() {
        return None;
    }
    Some((type_, domain))
}

fn conditional_primitive_domain(flags: TypeFlags) -> Option<ConditionalPrimitiveDomain> {
    Some(match flags {
        TypeFlags::STRING | TypeFlags::STRING_LITERAL => ConditionalPrimitiveDomain::String,
        TypeFlags::NUMBER | TypeFlags::NUMBER_LITERAL => ConditionalPrimitiveDomain::Number,
        TypeFlags::BIG_INT | TypeFlags::BIG_INT_LITERAL => ConditionalPrimitiveDomain::BigInt,
        TypeFlags::BOOLEAN | TypeFlags::BOOLEAN_LITERAL => ConditionalPrimitiveDomain::Boolean,
        TypeFlags::ES_SYMBOL | TypeFlags::UNIQUE_ES_SYMBOL => ConditionalPrimitiveDomain::Symbol,
        _ => return None,
    })
}

fn conditional_primitive_pair_is_disjoint(
    store: &CanonicalTypeMapperStore,
    (check, check_domain): (TypeId, ConditionalPrimitiveDomain),
    (extends, extends_domain): (TypeId, ConditionalPrimitiveDomain),
) -> bool {
    if check_domain != extends_domain {
        return true;
    }
    matches!(
        (
            store.type_payload(check).map(TypeRecord::data),
            store.type_payload(extends).map(TypeRecord::data),
        ),
        (Some(TypeData::Literal(check)), Some(TypeData::Literal(extends)))
            if check.value != extends.value
    )
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

fn conditional_node_has_alias_owner(store: &CanonicalTypeMapperStore, node: NodeRef) -> bool {
    conditional_alias_declaration(store, node).is_some()
}

fn conditional_alias_declaration(
    store: &CanonicalTypeMapperStore,
    mut node: NodeRef,
) -> Option<NodeRef> {
    loop {
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(node) else {
            return None;
        };
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType) => node = parent,
            Some(SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration) => {
                return Some(parent);
            }
            _ => return None,
        }
    }
}

fn stored_alias_identity(
    store: &CanonicalTypeMapperStore,
    alias: TypeAliasId,
) -> Result<ConditionalAliasIdentity<'_>, ConditionalTypeError> {
    let record = store
        .type_alias(alias)
        .ok_or(ConditionalTypeError::InvalidAlias(alias))?;
    Ok(ConditionalAliasIdentity {
        symbol: record
            .symbol()
            .ok_or(ConditionalTypeError::InvalidAlias(alias))?,
        type_arguments: record.type_arguments().unwrap_or_default(),
    })
}

fn validate_alias_identity(
    store: &CanonicalTypeMapperStore,
    alias: ConditionalAliasIdentity<'_>,
    visiting: &mut HashSet<TypeId>,
) -> Result<(), ConditionalTypeError> {
    let symbol = store
        .symbol(alias.symbol)
        .ok_or(ConditionalTypeError::InvalidAliasSymbol(alias.symbol))?;
    if !symbol.flags().contains(SymbolFlags::TYPE_ALIAS)
        || malformed_alias_merge(symbol.flags())
        || symbol.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(alias.symbol) != Some(alias.symbol)
        || symbol.declarations().is_none_or(|declarations| {
            !matches!(declarations, [declaration] if matches!(
                store.source_node_kind(*declaration),
                Some(SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration)
            ))
        })
    {
        return Err(ConditionalTypeError::InvalidAliasSymbol(alias.symbol));
    }
    for argument in alias.type_arguments {
        validate_conditional_operand(store, *argument, visiting)?;
    }
    Ok(())
}

fn validate_root_alias(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    outer_parameters: &[TypeId],
    alias: Option<TypeAliasId>,
) -> Result<(), ConditionalTypeError> {
    let Some(alias) = alias else {
        return Ok(());
    };
    let identity = stored_alias_identity(store, alias)?;
    validate_alias_identity(store, identity, &mut HashSet::new())?;
    let declaration = conditional_alias_declaration(store, node)
        .ok_or(ConditionalTypeError::InvalidAlias(alias))?;
    if store
        .symbol(identity.symbol)
        .and_then(|symbol| symbol.declarations())
        != Some(&[declaration][..])
    {
        return Err(ConditionalTypeError::InvalidAlias(alias));
    }
    let own_parameters = outer_parameters
        .iter()
        .copied()
        .filter(|parameter| {
            cached_ordinary_type_parameter_owner(store, *parameter)
                .and_then(|symbol| store.symbol(symbol))
                .and_then(|symbol| symbol.declarations())
                .is_some_and(|declarations| {
                    matches!(declarations, [parameter]
                    if store.source_node_parent(*parameter)
                        == Some(SourceNodeParent::Parent(declaration)))
                })
        })
        .collect::<Vec<_>>();
    if identity.type_arguments != own_parameters.as_slice() {
        return Err(ConditionalTypeError::InvalidAlias(alias));
    }
    Ok(())
}

fn mapped_root_alias(
    store: &CanonicalTypeMapperStore,
    root: ConditionalRootId,
    parameters: &[TypeId],
    arguments: &[TypeId],
) -> Result<Option<(SemanticSymbolId, Vec<TypeId>)>, ConditionalTypeError> {
    let Some(alias) = store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?
        .alias()
    else {
        return Ok(None);
    };
    let identity = stored_alias_identity(store, alias)?;
    let type_arguments = identity
        .type_arguments
        .iter()
        .map(|parameter| {
            parameters
                .iter()
                .position(|candidate| candidate == parameter)
                .map_or(*parameter, |index| arguments[index])
        })
        .collect();
    Ok(Some((identity.symbol, type_arguments)))
}

fn deferred_conditional(
    store: &mut CanonicalTypeMapperStore,
    root: ConditionalRootId,
    check_type: TypeId,
    extends_type: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    alias: Option<(ConditionalAliasIdentity<'_>, NodeRef)>,
) -> Result<TypeId, ConditionalTypeError> {
    let alias_reference = alias.map(|(_, reference)| reference);
    let alias = alias.map(|(identity, _)| identity);
    let definition = conditional_definition(store, root)?;
    let mapped_alias = mapped_root_alias(store, root, parameters, arguments)?;
    let alias = alias.or_else(|| {
        mapped_alias
            .as_ref()
            .map(|(symbol, arguments)| ConditionalAliasIdentity {
                symbol: *symbol,
                type_arguments: arguments,
            })
    });
    if let Some(identity) = alias {
        validate_alias_identity(store, identity, &mut HashSet::new())?;
    }
    if !store.try_reserve_conditional_productions(1, 0)
        || !store.try_reserve_types(1)
        || !store.try_reserve_type_aliases(usize::from(alias.is_some()))
        || !store.try_reserve_mappers(usize::from(
            !parameters.is_empty() && parameters != arguments,
        ))
    {
        return Err(ConditionalTypeError::Capacity);
    }
    let alias = if let Some(identity) = alias {
        let root_alias = store
            .conditional_root(root)
            .and_then(super::type_records::ConditionalRoot::alias);
        if root_alias.is_some_and(|alias| stored_alias_identity(store, alias) == Ok(identity)) {
            root_alias
        } else {
            let alias = store
                .alloc_type_alias(Some(identity.symbol))
                .ok_or(ConditionalTypeError::InvalidAliasSymbol(identity.symbol))?;
            if !store.set_type_alias_arguments(
                alias,
                (!identity.type_arguments.is_empty()).then(|| identity.type_arguments.to_vec()),
            ) {
                return Err(ConditionalTypeError::InvalidAlias(alias));
            }
            Some(alias)
        }
    } else {
        None
    };
    let mapper = if parameters.is_empty() || parameters == arguments {
        None
    } else {
        Some(
            store
                .new_type_mapper(parameters.to_vec(), arguments.to_vec())
                .ok_or(ConditionalTypeError::InvalidInstantiationCache(root))?,
        )
    };
    let conditional = store
        .alloc_conditional_type(root, check_type, extends_type, mapper, None)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?;
    if !store.set_type_alias(conditional, alias) {
        return Err(ConditionalTypeError::InvalidConditional(conditional));
    }
    let proof = ConditionalTypeProduction {
        type_: conditional,
        definition,
        check_type,
        extends_type,
        mapper,
        mapped_parameters: parameters.to_vec(),
        type_arguments: arguments.to_vec(),
        alias: retain_conditional_alias(store, alias)?,
        alias_reference,
    };
    if !store.publish_conditional_type_production(proof) {
        return Err(ConditionalTypeError::InvalidConditional(conditional));
    }
    Ok(conditional)
}

fn validate_request(
    store: &CanonicalTypeMapperStore,
    request: ConditionalTypeRequest<'_>,
) -> Result<(), ConditionalTypeError> {
    if !store.contains_node_ref(request.node)
        || store.source_node_kind(request.node) != Some(SyntaxKind::ConditionalType)
    {
        return Err(ConditionalTypeError::InvalidNode(request.node));
    }
    let mut visiting = HashSet::new();
    validate_conditional_operand(store, request.check_type, &mut visiting)?;
    validate_conditional_operand(store, request.extends_type, &mut visiting)?;
    validate_branch_types(store, request.branches)?;
    validate_root_alias(
        store,
        request.node,
        request.outer_type_parameters,
        request.alias,
    )?;
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

fn validate_conditional_operand(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    visiting: &mut HashSet<TypeId>,
) -> Result<(), ConditionalTypeError> {
    if !visiting.insert(type_) {
        return Ok(());
    }
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    let mut dependencies = Vec::new();
    if let Some(alias) = record.alias() {
        let alias_record = store
            .type_alias(alias)
            .ok_or(ConditionalTypeError::InvalidAlias(alias))?;
        dependencies.extend_from_slice(alias_record.type_arguments().unwrap_or_default());
    }
    match validate_stored_declared_call_set(store, type_) {
        StoredDeclaredCallSetValidation::Malformed => {
            return Err(RelationUnavailable::MalformedFunctionType(type_).into());
        }
        StoredDeclaredCallSetValidation::Valid(edges) => dependencies.extend(edges),
        StoredDeclaredCallSetValidation::NotDeclaredCallSet => {}
    }

    if let Some(structured) = record.data().structured() {
        let signatures = structured.signatures.as_deref().unwrap_or_default();
        if structured.call_signature_count > signatures.len() {
            return Err(RelationUnavailable::MalformedStructuredType(type_).into());
        }
        let mut unique = HashSet::with_capacity(signatures.len());
        for (index, signature) in signatures.iter().copied().enumerate() {
            let signature_record = store
                .signature(signature)
                .ok_or(ConditionalTypeError::InvalidSignature(signature))?;
            if !unique.insert(signature)
                || signature_record.flags().contains(SignatureFlags::CONSTRUCT)
                    != (index >= structured.call_signature_count)
            {
                return Err(ConditionalTypeError::InvalidSignature(signature));
            }
            if matches!(record.data(), TypeData::Object(_) | TypeData::Interface(_))
                && store
                    .declared_call_set_type_for_signature(signature)
                    .is_some_and(|owner| owner != type_)
            {
                return Err(RelationUnavailable::MalformedFunctionType(type_).into());
            }
            let return_type = signature_record
                .resolved_return_type()
                .ok_or(ConditionalTypeError::InvalidSignature(signature))?;
            dependencies.push(return_type);
            match store.callable_signature_parameter_types(signature) {
                Some(parameters) if parameters.len() == signature_record.parameters().len() => {
                    dependencies.extend_from_slice(parameters);
                }
                None if signature_record.parameters().is_empty() => {}
                _ => return Err(ConditionalTypeError::InvalidSignature(signature)),
            }
            if let Some(mapper) = signature_record.mapper()
                && store.mapper_payload(mapper).is_none()
            {
                return Err(ConditionalTypeError::InvalidMapper(mapper));
            }
        }
    }

    match record.data() {
        TypeData::Union(union) => dependencies.extend_from_slice(&union.union.types),
        TypeData::Intersection(intersection) => {
            dependencies.extend_from_slice(&intersection.intersection.types);
        }
        TypeData::TypeReference(reference) => {
            dependencies.extend_from_slice(
                reference
                    .resolved_type_arguments
                    .as_deref()
                    .unwrap_or_default(),
            );
            dependencies.extend(reference.object.target);
        }
        TypeData::Interface(interface) => {
            dependencies.extend_from_slice(
                interface
                    .reference
                    .resolved_type_arguments
                    .as_deref()
                    .unwrap_or_default(),
            );
            dependencies.extend(interface.reference.object.target);
        }
        TypeData::Tuple(tuple) => {
            dependencies.extend_from_slice(
                tuple
                    .interface
                    .reference
                    .resolved_type_arguments
                    .as_deref()
                    .unwrap_or_default(),
            );
            dependencies.extend(tuple.interface.reference.object.target);
        }
        TypeData::Object(object) => dependencies.extend(object.target),
        TypeData::TypeParameter(parameter) => dependencies.extend(parameter.constraint),
        TypeData::Index(index) => dependencies.push(index.target),
        TypeData::IndexedAccess(indexed) => {
            dependencies.extend([indexed.object_type, indexed.index_type]);
        }
        TypeData::TemplateLiteral(template) => dependencies.extend_from_slice(&template.types),
        TypeData::StringMapping(mapping) => dependencies.push(mapping.target),
        TypeData::Conditional(conditional) => {
            dependencies.extend([conditional.check_type, conditional.extends_type]);
        }
        _ => {}
    }
    for dependency in dependencies {
        validate_conditional_operand(store, dependency, visiting)?;
    }
    visiting.remove(&type_);
    Ok(())
}

fn validate_cached_conditional(
    store: &CanonicalTypeMapperStore,
    request: ConditionalTypeRequest<'_>,
    cached: TypeId,
) -> Result<TypeId, ConditionalTypeError> {
    let proof = store
        .conditional_query_production(ConditionalQueryKey::Node(request.node))
        .ok_or(ConditionalTypeError::InvalidTypeNodeCache(request.node))?;
    if proof.result != cached
        || proof.definition.check_type != request.check_type
        || proof.definition.extends_type != request.extends_type
        || proof.definition.infer_type_parameters != request.infer_type_parameters
        || proof.definition.outer_type_parameters != request.outer_type_parameters
        || proof.definition.alias != retain_conditional_alias(store, request.alias)?
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
    }
    validate_query_production(store, proof)?;
    Ok(cached)
}

#[allow(clippy::too_many_arguments)] // The retained query must match each cache-key input.
fn validate_cached_instantiation(
    store: &CanonicalTypeMapperStore,
    root: ConditionalRootId,
    key: CacheHashKey,
    cached: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    for_constraint: bool,
) -> Result<(), ConditionalTypeError> {
    let proof = store
        .conditional_query_production(ConditionalQueryKey::Instantiation(root, key))
        .or_else(|| {
            if parameters != arguments
                || alias.is_some()
                || for_constraint
                || key != conditional_type_key_parts(parameters, None, false)
            {
                return None;
            }
            let node = store.conditional_root(root)?.node();
            store.conditional_query_production(ConditionalQueryKey::Node(node))
        })
        .ok_or(ConditionalTypeError::InvalidInstantiationCache(root))?;
    let retained_alias = proof
        .alias
        .as_ref()
        .map(|(symbol, arguments)| ConditionalAliasIdentity {
            symbol: *symbol,
            type_arguments: arguments,
        });
    if proof.definition.root != root
        || proof.result != cached
        || proof.type_arguments != arguments
        || retained_alias != alias
        || proof.for_constraint != for_constraint
    {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    validate_query_production(store, proof)
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
    for branch in [branches.true_type, branches.false_type] {
        validate_owned_type(store, branch)?;
        let record = store
            .type_payload(branch)
            .ok_or(ConditionalTypeError::InvalidType(branch))?;
        if let Some(alias) = record.alias() {
            stored_alias_identity(store, alias)?;
        }
        if matches!(record.data(), TypeData::Conditional(_)) {
            validated_conditional_production(store, branch)?;
        }
    }
    Ok(())
}

fn conditional_type_key(
    store: &mut CanonicalTypeMapperStore,
    type_arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    for_constraint: bool,
) -> Result<CacheHashKey, ConditionalTypeError> {
    let alias = if let Some(alias) = alias {
        validate_alias_identity(store, alias, &mut HashSet::new())?;
        let symbol = store
            .global_symbol_id(alias.symbol)
            .ok_or(ConditionalTypeError::InvalidAliasSymbol(alias.symbol))?;
        Some((symbol, alias.type_arguments))
    } else {
        None
    };
    Ok(conditional_type_key_parts(
        type_arguments,
        alias,
        for_constraint,
    ))
}

fn conditional_type_key_parts(
    type_arguments: &[TypeId],
    alias: Option<(u64, &[TypeId])>,
    for_constraint: bool,
) -> CacheHashKey {
    let mut hasher = Xxh3::new();
    write_type_list(&mut hasher, type_arguments);
    if let Some((symbol, arguments)) = alias {
        hasher.update(&[1]);
        hasher.update(&symbol.to_le_bytes());
        write_type_list(&mut hasher, arguments);
    } else {
        hasher.update(&[0]);
    }
    if for_constraint {
        hasher.update(b"!");
    }
    CacheHashKey::new(hasher.digest128())
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
        let mut element_infos = Vec::with_capacity(tuple.element_infos.len());
        for (element, info) in tuple.element_types.into_iter().zip(tuple.element_infos) {
            let mapped = map_type(store, element, parameters, arguments, global_types, session)?;
            if info.flags().intersects(ElementFlags::VARIADIC)
                && let Some(mapped_tuple) = inference_tuple_shape(store, mapped)?
                && mapped_tuple
                    .element_infos
                    .iter()
                    .all(|element| !element.flags().intersects(ElementFlags::VARIABLE))
            {
                substituted.extend(mapped_tuple.element_types);
                element_infos.extend(mapped_tuple.element_infos);
            } else {
                substituted.push(mapped);
                element_infos.push(info);
            }
        }
        let mut request =
            CanonicalTupleTypeRequest::new(&substituted, &element_infos, tuple.readonly);
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
        TypeData::Index(index) => {
            contains_mapped_type_parameter(store, index.target, parameters, visiting)?
        }
        TypeData::IndexedAccess(indexed) => {
            contains_mapped_type_parameter(store, indexed.object_type, parameters, visiting)?
                || contains_mapped_type_parameter(store, indexed.index_type, parameters, visiting)?
        }
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
        let mut result = match record.data() {
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
            TypeData::Index(index) => visit(store, index.target, excluded, visiting)?,
            TypeData::IndexedAccess(indexed) => {
                visit(store, indexed.object_type, excluded, visiting)?
                    || visit(store, indexed.index_type, excluded, visiting)?
            }
            TypeData::Conditional(_) => true,
            TypeData::TemplateLiteral(template) => {
                template.types.iter().try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(found || visit(store, *item, excluded, visiting)?)
                })?
            }
            _ => false,
        };
        if !result && let Some(structured) = record.data().structured() {
            for signature in structured.signatures.as_deref().unwrap_or_default() {
                let signature_record = store
                    .signature(*signature)
                    .ok_or(ConditionalTypeError::InvalidSignature(*signature))?;
                let mut signature_excluded = excluded.clone();
                signature_excluded.extend(signature_record.type_parameters().iter().copied());
                for parameter in signature_record.type_parameters() {
                    let Some(TypeData::TypeParameter(parameter)) =
                        store.type_payload(*parameter).map(TypeRecord::data)
                    else {
                        return Err(ConditionalTypeError::InvalidSignature(*signature));
                    };
                    if let Some(constraint) = parameter.constraint
                        && visit(store, constraint, &signature_excluded, visiting)?
                    {
                        result = true;
                        break;
                    }
                }
                if result {
                    break;
                }
                let return_type = signature_record
                    .resolved_return_type()
                    .ok_or(ConditionalTypeError::InvalidSignature(*signature))?;
                if visit(store, return_type, &signature_excluded, visiting)? {
                    result = true;
                    break;
                }
                if let Some(parameters) = store.callable_signature_parameter_types(*signature) {
                    for parameter in parameters {
                        if visit(store, *parameter, &signature_excluded, visiting)? {
                            result = true;
                            break;
                        }
                    }
                    if result {
                        break;
                    }
                }
            }
        }
        visiting.remove(&type_);
        Ok(result)
    }

    visit(store, type_, excluded, &mut HashSet::new())
}

#[derive(Clone, Copy)]
struct ConditionalInferenceContext<'a> {
    infer_parameters: &'a [TypeId],
    mapped_parameters: &'a [TypeId],
    type_arguments: &'a [TypeId],
    global_types: Option<&'a CanonicalGlobalTypes>,
}

fn infer_from_types(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    context: ConditionalInferenceContext<'_>,
    candidates: &mut [Vec<TypeId>],
    session: &mut InstantiationSession,
) -> Result<bool, ConditionalTypeError> {
    if let Some(index) = context
        .infer_parameters
        .iter()
        .position(|parameter| *parameter == target)
    {
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
            context,
            candidates,
            session,
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
            let candidate =
                template_inference_candidate(store, source, target, context.infer_parameters)?;
            if !infer_from_types(store, candidate, target, context, candidates, session)? {
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
            if !infer_from_types(store, source, target, context, candidates, session)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }

    if target_record.data().structured().is_some() {
        if source_record.data().structured().is_none() {
            return if source_record
                .flags()
                .intersects(TypeFlags::ANY | TypeFlags::NEVER)
            {
                is_assignable(store, source, target, context.global_types)
            } else {
                Ok(false)
            };
        }
        return infer_from_structured_types(store, source, target, context, candidates, session);
    }
    if contains_type_parameter(store, target, &HashSet::new())? {
        Err(ConditionalTypeError::UnsupportedInference { source, target })
    } else {
        is_assignable(store, source, target, context.global_types)
    }
}

fn infer_from_tuple_types(
    store: &mut CanonicalTypeMapperStore,
    source: &InferenceTupleShape,
    target: &InferenceTupleShape,
    context: ConditionalInferenceContext<'_>,
    candidates: &mut [Vec<TypeId>],
    session: &mut InstantiationSession,
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
    let source_len = source.element_types.len();
    let target_len = target.element_types.len();
    if source_len < target.min_length {
        return Ok(false);
    }
    match variable_indices.as_slice() {
        [first, second] => {
            return infer_from_rest_and_variadic_tuple(
                store,
                source,
                target,
                [*first, *second],
                context,
                candidates,
                session,
            );
        }
        [_, _, _, ..] => return Ok(false),
        _ => {}
    }
    let Some(variable) = variable_indices.first().copied() else {
        if source_len > target_len {
            return Ok(false);
        }
        for (source, target) in source.element_types.iter().zip(&target.element_types) {
            if !infer_from_types(store, *source, *target, context, candidates, session)? {
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
            context,
            candidates,
            session,
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
            context,
            candidates,
            session,
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
        if let Some(global_types) = context.global_types {
            request =
                request.with_array_targets(CanonicalArrayTargets::from_global_types(global_types));
        }
        let middle = store.create_canonical_tuple_type(request)?;
        return infer_from_types(
            store,
            middle,
            target.element_types[variable],
            context,
            candidates,
            session,
        );
    }
    for element in middle_types {
        if !infer_from_types(
            store,
            *element,
            target.element_types[variable],
            context,
            candidates,
            session,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn infer_from_rest_and_variadic_tuple(
    store: &mut CanonicalTypeMapperStore,
    source: &InferenceTupleShape,
    target: &InferenceTupleShape,
    variable_indices: [usize; 2],
    context: ConditionalInferenceContext<'_>,
    candidates: &mut [Vec<TypeId>],
    session: &mut InstantiationSession,
) -> Result<bool, ConditionalTypeError> {
    let [first, second] = variable_indices;
    if second != first + 1 {
        return Ok(false);
    }
    let (variadic, rest) = match (
        target.element_infos[first].flags(),
        target.element_infos[second].flags(),
    ) {
        (ElementFlags::VARIADIC, ElementFlags::REST) => (first, second),
        (ElementFlags::REST, ElementFlags::VARIADIC) => (second, first),
        _ => return Ok(false),
    };
    let variadic_type = target.element_types[variadic];
    if !context.infer_parameters.contains(&variadic_type) {
        return Ok(false);
    }
    let Some(constraint) = constraints::get_base_constraint_of_type(store, variadic_type)? else {
        return Ok(false);
    };
    validate_conditional_operand(store, constraint, &mut HashSet::new())?;
    let Some(constraint_shape) = inference_tuple_shape(store, constraint)? else {
        return Ok(false);
    };
    if constraint_shape
        .element_infos
        .iter()
        .chain(&source.element_infos)
        .any(|info| info.flags().intersects(ElementFlags::VARIABLE))
    {
        return Ok(false);
    }

    let prefix_len = first;
    let suffix_len = target.element_types.len() - second - 1;
    let implied_arity = constraint_shape.element_types.len();
    let Some(minimum_len) = prefix_len
        .checked_add(suffix_len)
        .and_then(|length| length.checked_add(implied_arity))
    else {
        return Ok(false);
    };
    if source.element_types.len() < minimum_len {
        return Ok(false);
    }
    for index in 0..prefix_len {
        if !infer_from_types(
            store,
            source.element_types[index],
            target.element_types[index],
            context,
            candidates,
            session,
        )? {
            return Ok(false);
        }
    }
    for index in 0..suffix_len {
        let source_index = source.element_types.len() - suffix_len + index;
        let target_index = second + 1 + index;
        if !infer_from_types(
            store,
            source.element_types[source_index],
            target.element_types[target_index],
            context,
            candidates,
            session,
        )? {
            return Ok(false);
        }
    }

    let middle_end = source.element_types.len() - suffix_len;
    let (variadic_start, rest_start, rest_end) = if variadic == first {
        (prefix_len, prefix_len + implied_arity, middle_end)
    } else {
        (
            middle_end - implied_arity,
            prefix_len,
            middle_end - implied_arity,
        )
    };
    for index in rest_start..rest_end {
        if !infer_from_types(
            store,
            source.element_types[index],
            target.element_types[rest],
            context,
            candidates,
            session,
        )? {
            return Ok(false);
        }
    }

    let variadic_end = variadic_start + implied_arity;
    let mut request = CanonicalTupleTypeRequest::new(
        &source.element_types[variadic_start..variadic_end],
        &source.element_infos[variadic_start..variadic_end],
        false,
    );
    if let Some(global_types) = context.global_types {
        request =
            request.with_array_targets(CanonicalArrayTargets::from_global_types(global_types));
    }
    let captured = store.create_canonical_tuple_type(request)?;
    infer_from_types(store, captured, variadic_type, context, candidates, session)
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
    validate_conditional_operand(store, type_, &mut HashSet::new())?;
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
    context: ConditionalInferenceContext<'_>,
    candidates: &mut [Vec<TypeId>],
    session: &mut InstantiationSession,
) -> Result<bool, ConditionalTypeError> {
    let source_shape = structured_inference_shape(store, source)?;
    let target_shape = structured_inference_shape(store, target)?;
    if target_shape.properties.is_empty()
        && target_shape.call_signatures.is_empty()
        && target_shape.construct_signatures.is_empty()
    {
        return is_assignable(store, source, target, context.global_types);
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
        let source_type = map_type(
            store,
            source_type,
            context.mapped_parameters,
            context.type_arguments,
            context.global_types,
            session,
        )?;
        let target_type = map_type(
            store,
            target_type,
            context.mapped_parameters,
            context.type_arguments,
            context.global_types,
            session,
        )?;
        if !infer_from_types(
            store,
            source_type,
            target_type,
            context,
            candidates,
            session,
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
            let (source_parameters, source_minimum, source_return) =
                base_inference_signature_parts(
                    store,
                    source_signature,
                    context.global_types,
                    session,
                )?;
            let (target_parameters, _, target_return) =
                inference_signature_parts(store, target_signature)?;
            if source_minimum > target_parameters.len() {
                return Ok(false);
            }
            for (source_parameter, target_parameter) in
                source_parameters.into_iter().zip(target_parameters)
            {
                let source_parameter = map_type(
                    store,
                    source_parameter,
                    context.mapped_parameters,
                    context.type_arguments,
                    context.global_types,
                    session,
                )?;
                let target_parameter = map_type(
                    store,
                    target_parameter,
                    context.mapped_parameters,
                    context.type_arguments,
                    context.global_types,
                    session,
                )?;
                let compatible = if contains_mapped_type_parameter(
                    store,
                    target_parameter,
                    context.infer_parameters,
                    &mut HashSet::new(),
                )? {
                    infer_from_types(
                        store,
                        source_parameter,
                        target_parameter,
                        context,
                        candidates,
                        session,
                    )?
                } else {
                    is_assignable(
                        store,
                        target_parameter,
                        source_parameter,
                        context.global_types,
                    )?
                };
                if !compatible {
                    return Ok(false);
                }
            }
            let source_return = map_type(
                store,
                source_return,
                context.mapped_parameters,
                context.type_arguments,
                context.global_types,
                session,
            )?;
            let target_return = map_type(
                store,
                target_return,
                context.mapped_parameters,
                context.type_arguments,
                context.global_types,
                session,
            )?;
            if !infer_from_types(
                store,
                source_return,
                target_return,
                context,
                candidates,
                session,
            )? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

fn inference_signature_parts(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
) -> Result<(Vec<TypeId>, usize, TypeId), ConditionalTypeError> {
    let record = store
        .signature(signature)
        .ok_or(ConditionalTypeError::InvalidSignature(signature))?;
    let minimum = usize::try_from(record.min_argument_count())
        .map_err(|_| ConditionalTypeError::InvalidSignature(signature))?;
    let parameters = match store.callable_signature_parameter_types(signature) {
        Some(parameters) if parameters.len() == record.parameters().len() => parameters.to_vec(),
        None if record.parameters().is_empty() => Vec::new(),
        _ => return Err(ConditionalTypeError::InvalidSignature(signature)),
    };
    if minimum > parameters.len() {
        return Err(ConditionalTypeError::InvalidSignature(signature));
    }
    let return_type = record
        .resolved_return_type()
        .ok_or(ConditionalTypeError::InvalidSignature(signature))?;
    Ok((parameters, minimum, return_type))
}

fn base_inference_signature_parts(
    store: &mut CanonicalTypeMapperStore,
    signature: SignatureId,
    global_types: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
) -> Result<(Vec<TypeId>, usize, TypeId), ConditionalTypeError> {
    let (parameters, minimum, return_type) = inference_signature_parts(store, signature)?;
    let local_parameters = store
        .signature(signature)
        .ok_or(ConditionalTypeError::InvalidSignature(signature))?
        .type_parameters()
        .to_vec();
    if local_parameters.is_empty() {
        return Ok((parameters, minimum, return_type));
    }

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    let (unknown, any, no_constraint, circular_constraint) = (
        bootstrap.unknown_type,
        bootstrap.any_type,
        bootstrap.no_constraint_type,
        bootstrap.circular_constraint_type,
    );
    let mut constraints = Vec::with_capacity(local_parameters.len());
    for parameter in &local_parameters {
        let Some(TypeData::TypeParameter(data)) =
            store.type_payload(*parameter).map(TypeRecord::data)
        else {
            return Err(ConditionalTypeError::InvalidSignature(signature));
        };
        let constraint = data.constraint.unwrap_or(unknown);
        constraints.push(
            if constraint == no_constraint || constraint == circular_constraint {
                unknown
            } else {
                constraint
            },
        );
    }

    for _ in 1..local_parameters.len() {
        let previous = constraints.clone();
        for constraint in &mut constraints {
            *constraint = map_type(
                store,
                *constraint,
                &local_parameters,
                &previous,
                global_types,
                session,
            )?;
        }
    }
    let erased = vec![any; local_parameters.len()];
    for constraint in &mut constraints {
        *constraint = map_type(
            store,
            *constraint,
            &local_parameters,
            &erased,
            global_types,
            session,
        )?;
    }

    let mut base_parameters = Vec::with_capacity(parameters.len());
    for parameter in parameters {
        base_parameters.push(map_type(
            store,
            parameter,
            &local_parameters,
            &constraints,
            global_types,
            session,
        )?);
    }
    let base_return = map_type(
        store,
        return_type,
        &local_parameters,
        &constraints,
        global_types,
        session,
    )?;
    Ok((base_parameters, minimum, base_return))
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
            if let Some((character, _)) = split_first_template_code_point(&current[position..]) {
                (segment, position + character.len())
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

fn union_result_with_alias(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    alias: Option<ConditionalAliasIdentity<'_>>,
) -> Result<TypeId, ConditionalTypeError> {
    let Some(alias) = alias else {
        return union_result(store, types, global_types);
    };
    store
        .literal_union_type_with_alias_and_array_targets(
            types,
            Some((alias.symbol, alias.type_arguments)),
            global_types.map(CanonicalArrayTargets::from_global_types),
        )
        .map_err(Into::into)
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
    } else if matches!(
        store.type_payload(target).map(TypeRecord::data),
        Some(TypeData::TemplateLiteral(_))
    ) && store.type_payload(source).is_some_and(|record| {
        record
            .flags()
            .intersects(TypeFlags::STRING_LITERAL | TypeFlags::TEMPLATE_LITERAL | TypeFlags::UNION)
    }) {
        store
            .is_type_matched_by_template_literal_type(source, target)
            .map_err(Into::into)
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
    let target_suffix_len = target_rest.map_or(0, |rest| target_len - rest - 1);
    if source_len < target_suffix_len {
        return Ok(false);
    }
    let target_suffix_start = source_len - target_suffix_len;
    for (index, source_type) in source.element_types.iter().copied().enumerate() {
        let target_index = if let Some(rest) = target_rest {
            if index < rest {
                index
            } else if index >= target_suffix_start {
                target_len - (source_len - index)
            } else {
                rest
            }
        } else {
            index
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
    use ts_ast::{FileId, NodeData, SyntaxKind, encode_js_string};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName, SymbolData, SymbolFlags,
    };
    use ts_core::JsString;
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerDiagnostics, CanonicalCheckerOptions, DeclaredTypeError, DeclaredTypeHost,
        DeclaredTypeLinks, IntrinsicBootstrapOptions, SemanticStore, ValueSymbolLinks,
        declared::execute_type_parameter,
        mapper::TypeMapper,
        production::GlobalMergeCompletion,
        signatures::IndexFlags,
        type_nodes::CanonicalTypeQuery,
        type_records::RegularLiteralLink,
        types::{AccessFlags, ObjectFlags},
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
            let locals = bound.locals(bound.source_file()).unwrap();
            let mut symbols = store
                .symbol_table(locals)
                .unwrap()
                .iter()
                .map(|(name, symbol)| (name.as_bytes().to_vec(), symbol))
                .collect::<Vec<_>>();
            symbols.sort_unstable_by(|left, right| left.0.cmp(&right.0));
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            for (_, symbol) in symbols {
                store.merge_global_symbol(globals, symbol).unwrap();
            }
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

        fn alias_declaration(&self, expected: &str) -> NodeRef {
            self.parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &self.parsed.arena.get(alias.name)?.data
                    else {
                        return None;
                    };
                    (name.text == expected).then_some(NodeRef::new(
                        self.parsed.arena.id(),
                        self.file,
                        node,
                    ))
                })
                .unwrap_or_else(|| panic!("missing type alias {expected}"))
        }

        fn alias_symbol(&self, expected: &str) -> SemanticSymbolId {
            self.bound
                .symbol(self.alias_declaration(expected))
                .unwrap_or_else(|| panic!("missing type-alias symbol {expected}"))
        }

        fn declared_alias(&mut self, expected: &str) -> TypeId {
            self.try_declared_alias(expected)
                .unwrap_or_else(|error| panic!("type alias {expected} failed: {error:?}"))
        }

        fn try_declared_alias(&mut self, expected: &str) -> Result<TypeId, DeclaredTypeError> {
            let symbol = self.alias_symbol(expected);
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let result = CanonicalTypeQuery::new(
                &mut self.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(symbol);
            assert!(diagnostics.is_empty());
            result
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
                if construct {
                    SignatureFlags::CONSTRUCT
                } else {
                    SignatureFlags::NONE
                },
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
    #[allow(clippy::too_many_lines)] // All trivial bounds share one root and cache identity proof.
    fn trivial_distributive_instantiations_preserve_checked_parameter_identity() {
        #[derive(Clone, Copy)]
        enum Bound {
            Never,
            Checked,
            Any,
            Unknown,
        }

        for (keep_true, bound) in [
            (false, Bound::Never),
            (true, Bound::Checked),
            (true, Bound::Any),
            (true, Bound::Unknown),
        ] {
            let source = if keep_true {
                "type Select<T, U> = T extends U ? T : never; type Caller<Value> = Value;"
            } else {
                "type Select<T, U> = T extends U ? never : T; type Caller<Value> = Value;"
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound_parameter = fixture.type_parameter("U");
            let checked = fixture.type_parameter("Value");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let never = bootstrap.never_type;
            let actual_bound = match bound {
                Bound::Never => never,
                Bound::Checked => checked,
                Bound::Any => bootstrap.any_type,
                Bound::Unknown => bootstrap.unknown_type,
            };
            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound_parameter,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: &[parameter, bound_parameter],
                    alias: None,
                },
                None,
            )
            .unwrap();
            let root = match fixture.store.type_payload(conditional).unwrap().data() {
                TypeData::Conditional(data) => data.root,
                _ => panic!("the generic declaration must retain its conditional root"),
            };
            let mapper_count = fixture.store.mapper_len();
            let arguments = [checked, actual_bound];

            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &arguments,
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(checked),
            );
            assert_eq!(fixture.store.mapper_len(), mapper_count);
            let TypeCacheState::Allocated(cache) = fixture
                .store
                .conditional_root(root)
                .unwrap()
                .instantiations()
            else {
                panic!("the generic conditional root retains its instantiation cache")
            };
            assert_eq!(cache.len(), 2);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture
                    .store
                    .conditional_root(root)
                    .unwrap()
                    .instantiations()
                    .clone(),
            );
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &arguments,
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(checked),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                    fixture
                        .store
                        .conditional_root(root)
                        .unwrap()
                        .instantiations()
                        .clone(),
                ),
                warm,
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Impossible bounds share one root and warm-cache matrix.
    fn trivial_distributive_instantiations_reduce_impossible_branches_to_never() {
        #[derive(Clone, Copy)]
        enum Bound {
            Never,
            Checked,
            Any,
            Unknown,
        }

        for (keep_true, bound) in [
            (true, Bound::Never),
            (false, Bound::Checked),
            (false, Bound::Any),
            (false, Bound::Unknown),
        ] {
            let source = if keep_true {
                "type Select<T, U> = T extends U ? T : never; type Caller<Value> = Value;"
            } else {
                "type Select<T, U> = T extends U ? never : T; type Caller<Value> = Value;"
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound_parameter = fixture.type_parameter("U");
            let checked = fixture.type_parameter("Value");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let never = bootstrap.never_type;
            let actual_bound = match bound {
                Bound::Never => never,
                Bound::Checked => checked,
                Bound::Any => bootstrap.any_type,
                Bound::Unknown => bootstrap.unknown_type,
            };
            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound_parameter,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: &[parameter, bound_parameter],
                    alias: None,
                },
                None,
            )
            .unwrap();
            let mapper_count = fixture.store.mapper_len();

            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[checked, actual_bound],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(never),
            );
            assert_eq!(fixture.store.mapper_len(), mapper_count);
            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            );
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[checked, actual_bound],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(never),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn trivial_conditional_never_reductions_preserve_any_semantics() {
        for (keep_true, use_any_bound, expected_any) in [
            (true, false, true),
            (true, true, true),
            (false, false, true),
            (false, true, false),
        ] {
            let source = if keep_true {
                "type Select<T, U> = T extends U ? T : never;"
            } else {
                "type Select<T, U> = T extends U ? never : T;"
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound = fixture.type_parameter("U");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (any, never) = (bootstrap.any_type, bootstrap.never_type);
            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: &[parameter, bound],
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
                        type_arguments: &[any, if use_any_bound { any } else { never }],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(if expected_any { any } else { never }),
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Literal and primitive constraints share one safety matrix.
    fn constrained_primitive_conditionals_reduce_only_when_domains_are_disjoint() {
        for (keep_true, use_literals) in [(true, false), (false, false), (true, true)] {
            let source = if keep_true {
                concat!(
                    "type Select<T, U> = T extends U ? T : never; ",
                    "type Caller<Value> = Value;",
                )
            } else {
                concat!(
                    "type Select<T, U> = T extends U ? never : T; ",
                    "type Caller<Value> = Value;",
                )
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound = fixture.type_parameter("U");
            let checked = fixture.type_parameter("Value");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, never) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.never_type,
            );
            let (constraint, disjoint_bound, compatible_bound) = if use_literals {
                (
                    fixture
                        .store
                        .regular_string_literal_type("left".to_owned())
                        .unwrap(),
                    fixture
                        .store
                        .regular_string_literal_type("right".to_owned())
                        .unwrap(),
                    string,
                )
            } else {
                (string, number, string)
            };
            assert!(fixture.store.set_type_parameter_resolution(
                checked,
                Some(constraint),
                None,
                None,
                None,
            ));
            assert!(conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                disjoint_bound,
            ));
            assert!(!conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                compatible_bound,
            ));
            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: &[parameter, bound],
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
                        type_arguments: &[checked, disjoint_bound],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(if keep_true { never } else { checked }),
            );
            let unresolved = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[checked, compatible_bound],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            assert!(matches!(
                fixture.store.type_payload(unresolved).map(TypeRecord::data),
                Some(TypeData::Conditional(_))
            ));
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Primitive and literal unions share one bounded proof matrix.
    fn bounded_primitive_union_constraints_reduce_only_disjoint_members() {
        for (keep_true, use_literals) in
            [(true, false), (false, false), (true, true), (false, true)]
        {
            let source = if keep_true {
                concat!(
                    "type Select<T, U> = T extends U ? T : never; ",
                    "type Caller<Value, Other> = Value;",
                )
            } else {
                concat!(
                    "type Select<T, U> = T extends U ? never : T; ",
                    "type Caller<Value, Other> = Value;",
                )
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound = fixture.type_parameter("U");
            let checked = fixture.type_parameter("Value");
            let other = fixture.type_parameter("Other");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, bigint, symbol, never) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.es_symbol_type,
                bootstrap.never_type,
            );
            let (constraint_members, disjoint_members, overlapping_members) = if use_literals {
                let left = fixture
                    .store
                    .regular_string_literal_type("left".to_owned())
                    .unwrap();
                let center = fixture
                    .store
                    .regular_string_literal_type("center".to_owned())
                    .unwrap();
                let right = fixture
                    .store
                    .regular_string_literal_type("right".to_owned())
                    .unwrap();
                let other = fixture
                    .store
                    .regular_string_literal_type("other".to_owned())
                    .unwrap();
                ([left, center], [right, other], [center, right])
            } else {
                ([string, bigint], [number, symbol], [string, number])
            };
            let constraint =
                canonical_anonymous_union(&mut fixture.store, &constraint_members).unwrap();
            let disjoint =
                canonical_anonymous_union(&mut fixture.store, &disjoint_members).unwrap();
            let overlapping =
                canonical_anonymous_union(&mut fixture.store, &overlapping_members).unwrap();
            assert!(fixture.store.set_type_parameter_resolution(
                checked,
                Some(constraint),
                None,
                None,
                None,
            ));
            assert!(fixture.store.set_type_parameter_resolution(
                other,
                Some(disjoint),
                None,
                None,
                None,
            ));
            assert!(conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                disjoint,
            ));
            assert!(conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                other,
            ));
            assert!(conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                constraint,
                disjoint,
            ));
            assert!(!conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                overlapping,
            ));

            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: &[parameter, bound],
                    alias: None,
                },
                None,
            )
            .unwrap();
            for actual_bound in [disjoint, other] {
                assert_eq!(
                    get_conditional_type_instantiation(
                        &mut fixture.store,
                        ConditionalTypeInstantiation {
                            conditional_type: conditional,
                            type_arguments: &[checked, actual_bound],
                            branches: branch_types,
                            alias: None,
                            for_constraint: false,
                        },
                        None,
                        None,
                    ),
                    Ok(if keep_true { never } else { checked }),
                );
            }

            let unresolved = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[checked, overlapping],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            assert!(matches!(
                fixture.store.type_payload(unresolved).map(TypeRecord::data),
                Some(TypeData::Conditional(_))
            ));

            let warm = (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.conditional_root_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[checked, disjoint],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(if keep_true { never } else { checked }),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.mapper_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn primitive_union_disjointness_enforces_constituent_and_comparison_limits() {
        let mut fixture = Fixture::new("type Caller<Value> = Value;");
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let mut strings = Vec::new();
        for index in 0..=MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS {
            strings.push(
                fixture
                    .store
                    .regular_string_literal_type(format!("value-{index}"))
                    .unwrap(),
            );
        }
        let bounded = canonical_anonymous_union(
            &mut fixture.store,
            &strings[..MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS],
        )
        .unwrap();
        let oversized = canonical_anonymous_union(&mut fixture.store, &strings).unwrap();
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            bounded,
            number,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            oversized,
            number,
        ));

        let bounded_comparisons =
            canonical_anonymous_union(&mut fixture.store, &strings[..8]).unwrap();
        let excessive_comparisons =
            canonical_anonymous_union(&mut fixture.store, &strings[..9]).unwrap();
        let mut numbers = Vec::new();
        for value in 0..8 {
            numbers.push(
                fixture
                    .store
                    .regular_number_literal_type(ts_jsnum::Number::new(f64::from(value)))
                    .unwrap(),
            );
        }
        let right = canonical_anonymous_union(&mut fixture.store, &numbers).unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            bounded_comparisons,
            right,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            excessive_comparisons,
            right,
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn primitive_union_disjointness_rejects_forged_union_identities() {
        let mut fixture = Fixture::new("type Caller<Value> = Value;");
        let checked = fixture.type_parameter("Value");
        let left = fixture
            .store
            .regular_string_literal_type("left".to_owned())
            .unwrap();
        let right = fixture
            .store
            .regular_string_literal_type("right".to_owned())
            .unwrap();
        let canonical = canonical_anonymous_union(&mut fixture.store, &[left, right]).unwrap();
        let members = match fixture.store.type_payload(canonical).unwrap().data() {
            TypeData::Union(union) => union.union.types.clone(),
            _ => panic!("two distinct string literals must retain a canonical union"),
        };
        let forged = fixture
            .store
            .alloc_union_type(ObjectFlags::NONE, members)
            .unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(fixture.store.set_type_parameter_resolution(
            checked,
            Some(canonical),
            None,
            None,
            None,
        ));
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            number,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            forged,
            number,
        ));
        assert!(fixture.store.set_type_parameter_resolution(
            checked,
            Some(forged),
            None,
            None,
            None,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            number,
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One proof covers forged literals, owners, and cycles.
    fn disjoint_primitive_conditional_proofs_reject_forged_caches() {
        let mut fixture = Fixture::new("type Caller<Value, Other> = Value;");
        let checked = fixture.type_parameter("Value");
        let other = fixture.type_parameter("Other");
        let left = fixture
            .store
            .regular_string_literal_type("left".to_owned())
            .unwrap();
        let right = fixture
            .store
            .regular_string_literal_type("right".to_owned())
            .unwrap();
        assert!(
            fixture
                .store
                .set_type_parameter_resolution(checked, Some(left), None, None, None,)
        );
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));

        let forged = fixture
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("left".to_owned()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        assert!(fixture.store.set_type_parameter_resolution(
            checked,
            Some(forged),
            None,
            None,
            None,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));
        assert!(
            fixture
                .store
                .set_type_parameter_resolution(checked, Some(left), None, None, None,)
        );

        let owner = cached_ordinary_type_parameter_owner(&fixture.store, checked).unwrap();
        let links = fixture.store.declared_type_links(owner).unwrap().clone();
        assert!(
            fixture
                .store
                .set_declared_type_links(owner, DeclaredTypeLinks::default())
        );
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));
        assert!(fixture.store.set_declared_type_links(owner, links));
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));

        assert!(fixture.store.set_type_parameter_resolution(
            other,
            Some(checked),
            None,
            None,
            None,
        ));
        assert!(fixture.store.set_type_parameter_resolution(
            checked,
            Some(other),
            None,
            None,
            None,
        ));
        let cyclic = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            cyclic,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One root covers identity, keyof, and deferred cases.
    fn templated_conditional_identity_simplifies_only_proven_branches() {
        let mut fixture = Fixture::new(concat!(
            "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
            "Check extends Bound ? WhenTrue : WhenFalse; ",
            "type Caller<Value> = Value;",
        ));
        let node = fixture.conditional();
        let check = fixture.type_parameter("Check");
        let bound = fixture.type_parameter("Bound");
        let when_true = fixture.type_parameter("WhenTrue");
        let when_false = fixture.type_parameter("WhenFalse");
        let checked = fixture.type_parameter("Value");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (never, string, number) = (
            bootstrap.never_type,
            bootstrap.string_type,
            bootstrap.number_type,
        );
        let keys = fixture
            .store
            .alloc_index_type(checked, IndexFlags::NONE)
            .unwrap();
        let branch_types = branches(when_true, when_false);
        let parameters = [check, bound, when_true, when_false];
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: check,
                extends_type: bound,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: &parameters,
                alias: None,
            },
            None,
        )
        .unwrap();
        let root = match fixture.store.type_payload(conditional).unwrap().data() {
            TypeData::Conditional(data) => data.root,
            _ => panic!("the generic declaration must retain its conditional root"),
        };

        for (arguments, expected) in [
            ([checked, never, never, checked], checked),
            ([checked, checked, checked, never], checked),
            ([checked, string, checked, checked], checked),
            ([keys, never, never, keys], keys),
            ([keys, keys, keys, never], keys),
        ] {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &arguments,
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(expected),
            );
        }

        for arguments in [
            [checked, string, checked, never],
            [checked, never, number, number],
        ] {
            let deferred = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &arguments,
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            let TypeData::Conditional(data) = fixture.store.type_payload(deferred).unwrap().data()
            else {
                panic!("an unproven distributive conditional must remain deferred")
            };
            assert_eq!(data.root, root);
            assert!(data.resolved_true_type.is_none());
            assert!(data.resolved_false_type.is_none());
        }

        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[never, string, number, number],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(never),
            "equal non-identity branches must not erase distributive never",
        );
    }

    #[test]
    fn extract_against_any_preserves_the_original_concrete_union() {
        let mut fixture = Fixture::new("type Extract<T, U> = T extends U ? T : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bound = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, any, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.any_type,
            bootstrap.never_type,
        );
        let branch_types = branches(parameter, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: bound,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: &[parameter, bound],
                alias: None,
            },
            None,
        )
        .unwrap();
        let union = canonical_anonymous_union(&mut fixture.store, &[number, string]).unwrap();

        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[union, any],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(union),
        );
    }

    #[test]
    fn trivial_conditional_alias_type_nodes_resolve_to_the_checked_identity() {
        for (source, alias) in [
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value> = Exclude<Value, never>;",
                ),
                "Exclude",
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value> = Extract<Value, Value>;",
                ),
                "Extract",
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value> = Extract<Value, any>;",
                ),
                "Extract",
            ),
            (
                concat!(
                    "type ExcludeWithDefault<T, U, D = never> = T extends U ? D : T; ",
                    "type Result<Value> = ExcludeWithDefault<Value, never>;",
                ),
                "ExcludeWithDefault",
            ),
            (
                concat!(
                    "type ExtractWithDefault<T, U, D = never> = T extends U ? T : D; ",
                    "type Result<Value> = ExtractWithDefault<Value, Value>;",
                ),
                "ExtractWithDefault",
            ),
            (
                concat!(
                    "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                    "Check extends Bound ? WhenTrue : WhenFalse; ",
                    "type Result<Value> = Select<Value, never, never, Value>;",
                ),
                "Select",
            ),
            (
                concat!(
                    "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                    "Check extends Bound ? WhenTrue : WhenFalse; ",
                    "type Result<Value> = Select<Value, Value, Value, never>;",
                ),
                "Select",
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let checked = fixture.type_parameter("Value");
            assert_eq!(fixture.declared_alias("Result"), checked, "{alias}");
            let conditional = fixture.declared_alias(alias);
            let TypeData::Conditional(data) =
                fixture.store.type_payload(conditional).unwrap().data()
            else {
                panic!("{alias} must retain its original deferred declaration")
            };
            assert!(data.resolved_true_type.is_none());
            assert!(data.resolved_false_type.is_none());
            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), checked, "{alias}");
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn impossible_conditional_alias_type_nodes_reduce_to_never() {
        for source in [
            concat!(
                "type Extract<T, U> = T extends U ? T : never; ",
                "type Result<Value> = Extract<Value, never>;",
            ),
            concat!(
                "type Exclude<T, U> = T extends U ? never : T; ",
                "type Result<Value> = Exclude<Value, Value>;",
            ),
            concat!(
                "type Exclude<T, U> = T extends U ? never : T; ",
                "type Result<Value> = Exclude<Value, any>;",
            ),
            concat!(
                "type Exclude<T, U> = T extends U ? never : T; ",
                "type Result<Value> = Exclude<Value, unknown>;",
            ),
            concat!(
                "type ExtractWithDefault<T, U, D = never> = T extends U ? T : D; ",
                "type Result<Value> = ExtractWithDefault<Value, never>;",
            ),
            concat!(
                "type ExcludeWithDefault<T, U, D = never> = T extends U ? D : T; ",
                "type Result<Value> = ExcludeWithDefault<Value, Value>;",
            ),
            concat!(
                "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                "Check extends Bound ? WhenTrue : WhenFalse; ",
                "type Result<Value> = Select<Value, never, Value, never>;",
            ),
            concat!(
                "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                "Check extends Bound ? WhenTrue : WhenFalse; ",
                "type Result<Value> = Select<Value, Value, never, Value>;",
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let never = fixture.store.intrinsic_bootstrap().unwrap().never_type;
            assert_eq!(fixture.declared_alias("Result"), never);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), never);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn constrained_conditional_alias_type_nodes_use_only_disjoint_primitive_proofs() {
        for (source, preserves_parameter) in [
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends string> = Extract<Value, number>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends string> = Exclude<Value, number>;",
                ),
                true,
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends string, Bound extends number> = ",
                    "Extract<Value, Bound>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends string, Bound extends number> = ",
                    "Exclude<Value, Bound>;",
                ),
                true,
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends 'left'> = Extract<Value, 'right'>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends 'left'> = Exclude<Value, 'right'>;",
                ),
                true,
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let checked = fixture.type_parameter("Value");
            let expected = if preserves_parameter {
                checked
            } else {
                fixture.store.intrinsic_bootstrap().unwrap().never_type
            };
            assert_eq!(fixture.declared_alias("Result"), expected);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), expected);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }

        let mut uncertain = Fixture::new(concat!(
            "type Extract<T, U> = T extends U ? T : never; ",
            "type Result<Value extends string> = Extract<Value, string>;",
        ));
        let unresolved = uncertain.declared_alias("Result");
        assert!(matches!(
            uncertain
                .store
                .type_payload(unresolved)
                .map(TypeRecord::data),
            Some(TypeData::Conditional(_))
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Alias resolution covers primitive and literal union proofs.
    fn constrained_conditional_alias_type_nodes_reduce_bounded_disjoint_primitive_unions() {
        for (source, preserves_parameter) in [
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends string | bigint> = ",
                    "Extract<Value, number | symbol>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends string | bigint> = ",
                    "Exclude<Value, number | symbol>;",
                ),
                true,
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends 'a' | 'b'> = ",
                    "Extract<Value, 'c' | 'd'>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends 'a' | 'b'> = ",
                    "Exclude<Value, 'c' | 'd'>;",
                ),
                true,
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends string | bigint, ",
                    "Bound extends number | symbol> = Extract<Value, Bound>;",
                ),
                false,
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let checked = fixture.type_parameter("Value");
            let expected = if preserves_parameter {
                checked
            } else {
                fixture.store.intrinsic_bootstrap().unwrap().never_type
            };
            assert_eq!(fixture.declared_alias("Result"), expected);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), expected);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }

        let mut uncertain = Fixture::new(concat!(
            "type Extract<T, U> = T extends U ? T : never; ",
            "type Result<Value extends string | number> = ",
            "Extract<Value, number | symbol>;",
        ));
        let checked = uncertain.type_parameter("Value");
        let unresolved = uncertain.declared_alias("Result");
        let TypeData::Conditional(data) = uncertain.store.type_payload(unresolved).unwrap().data()
        else {
            panic!("overlapping primitive unions must retain a deferred conditional")
        };
        assert_eq!(data.check_type, checked);
        assert!(data.resolved_true_type.is_none());
        assert!(data.resolved_false_type.is_none());

        let warm = (
            uncertain.store.type_len(),
            uncertain.store.conditional_root_len(),
            uncertain.store.mapper_len(),
            uncertain.store.checker_link_allocated_lengths(),
        );
        assert_eq!(uncertain.declared_alias("Result"), unresolved);
        assert_eq!(
            (
                uncertain.store.type_len(),
                uncertain.store.conditional_root_len(),
                uncertain.store.mapper_len(),
                uncertain.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn nontrivial_conditional_reference_branches_remain_deferred() {
        let mut fixture = Fixture::new(concat!(
            "type OnlyText<Input extends string> = Input; ",
            "type Select<T, U> = T extends U ? OnlyText<number> : T; ",
            "type Result<Value> = Select<Value, never>;",
        ));
        let checked = fixture.type_parameter("Value");
        let result = fixture.declared_alias("Result");
        let TypeData::Conditional(data) = fixture.store.type_payload(result).unwrap().data() else {
            panic!("an unproven conditional branch must remain deferred")
        };
        assert_eq!(data.check_type, checked);
        assert!(data.resolved_true_type.is_none());
        assert!(data.resolved_false_type.is_none());
    }

    #[test]
    fn trivial_conditional_keyof_instantiations_preserve_index_identity() {
        for source in [
            concat!(
                "type Exclude<T, U> = T extends U ? never : T; ",
                "type Result<Value> = Exclude<keyof Value, never>;",
            ),
            concat!(
                "type Extract<T, U> = T extends U ? T : never; ",
                "type Result<Value> = Extract<keyof Value, keyof Value>;",
            ),
            concat!(
                "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                "Check extends Bound ? WhenTrue : WhenFalse; ",
                "type Result<Value> = Select<keyof Value, never, never, keyof Value>;",
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let checked = fixture.type_parameter("Value");
            let result = fixture.declared_alias("Result");
            let TypeData::Index(index) = fixture.store.type_payload(result).unwrap().data() else {
                panic!("the conditional must preserve the generic keyof identity")
            };
            assert_eq!(index.target, checked);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), result);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn trivial_conditional_instantiation_rejects_invalid_root_cache_state() {
        let mut fixture = Fixture::new(concat!(
            "type Exclude<T, U> = T extends U ? never : T; ",
            "type Caller<Value> = Value;",
        ));
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bound = fixture.type_parameter("U");
        let checked = fixture.type_parameter("Value");
        let never = fixture.store.intrinsic_bootstrap().unwrap().never_type;
        let branch_types = branches(never, parameter);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: bound,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: &[parameter, bound],
                alias: None,
            },
            None,
        )
        .unwrap();
        let root = match fixture.store.type_payload(conditional).unwrap().data() {
            TypeData::Conditional(data) => data.root,
            _ => panic!("the generic declaration must retain its conditional root"),
        };
        let valid_cache = fixture
            .store
            .conditional_root(root)
            .unwrap()
            .instantiations()
            .clone();
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(root, TypeCacheState::Unallocated,)
        );
        let before = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
            fixture.store.mapper_len(),
        );

        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[checked, never],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Err(ConditionalTypeError::InvalidInstantiationCache(root)),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            ),
            before,
        );
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(root, valid_cache)
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[checked, never],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(checked),
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

    fn conditional_allocation_counts(
        store: &CanonicalTypeMapperStore,
    ) -> (usize, usize, usize, usize, (usize, usize)) {
        (
            store.type_len(),
            store.conditional_root_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.conditional_production_lengths(),
        )
    }

    fn assert_uncaptured_conditional_remap_is_unsupported(
        fixture: &mut Fixture,
        source: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
    ) {
        let original = conditional_snapshot(&fixture.store, source).unwrap();
        assert!(original.resolved_true_type.is_none());
        assert!(original.resolved_false_type.is_none());
        assert!(original.resolved_inferred_true_type.is_none());
        let cache = fixture
            .store
            .conditional_root(original.root)
            .unwrap()
            .instantiations()
            .clone();
        let nodes = fixture
            .parsed
            .arena
            .iter()
            .map(|(node, _)| NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            .collect::<Vec<_>>();
        let links = |store: &CanonicalTypeMapperStore| {
            nodes
                .iter()
                .map(|node| {
                    (
                        store.type_node_links(*node).cloned(),
                        store.symbol_node_links(*node).cloned(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let before = conditional_allocation_counts(&fixture.store);
        let original_links = links(&fixture.store);
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut session = InstantiationSession::new_recovering(
            &fixture.store,
            InstantiationLimits::default(),
            error_type,
        )
        .unwrap();
        for _ in 0..2 {
            assert_eq!(
                conditional_remap_projection(&fixture.store, source),
                Err(ConditionalTypeError::Instantiation(
                    InstantiationError::UnsupportedType(source)
                ))
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    &fixture.store,
                    source,
                    parameters,
                    arguments,
                    None,
                    None,
                ),
                Err(InstantiationError::UnsupportedType(source))
            );
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    &mut fixture.store,
                    source,
                    parameters,
                    arguments,
                    None,
                    &mut session,
                ),
                Err(InstantiationError::UnsupportedType(source))
            );
            assert_eq!(session.query_count(), 0);
            assert_eq!(session.limit_event_count(), 0);
            assert_eq!(conditional_allocation_counts(&fixture.store), before);
            assert_eq!(
                conditional_snapshot(&fixture.store, source).unwrap(),
                original
            );
            assert_eq!(
                fixture
                    .store
                    .conditional_root(original.root)
                    .unwrap()
                    .instantiations(),
                &cache
            );
            assert_eq!(links(&fixture.store), original_links);
        }
    }

    #[test]
    fn deferred_conditional_remap_rejects_uncaptured_inline_mapped_parameters() {
        let mut fixture = Fixture::new(concat!(
            "interface Validator<Value> {} ",
            "type IsOptional<Value> = Value extends undefined ? true : false; ",
            "type RequiredKeys<Value> = { ",
            "[Key in keyof Value]: Value[Key] extends Validator<infer Item> ",
            "? IsOptional<Item> extends true ? never : Key : never ",
            "}[keyof Value];",
        ));
        let declared = fixture.declared_alias("RequiredKeys");
        let node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ConditionalTypeNode(conditional) = &record.data else {
                    return None;
                };
                (fixture.parsed.arena.get(conditional.check_type)?.kind
                    == SyntaxKind::IndexedAccessType)
                    .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            })
            .unwrap();
        let source = fixture
            .store
            .type_node_links(node)
            .unwrap()
            .resolved_type
            .unwrap();
        let proof = validated_conditional_production(&fixture.store, source).unwrap();
        assert_eq!(proof.definition.node, node);
        assert!(proof.definition.alias.is_none());
        assert!(proof.definition.outer_type_parameters.is_empty());
        let TypeData::IndexedAccess(indexed) = fixture
            .store
            .type_payload(proof.definition.check_type)
            .unwrap()
            .data()
        else {
            unreachable!()
        };
        let parameters = [indexed.object_type, indexed.index_type];
        let target = fixture.type_parameter("Value");
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert_ne!(parameters[0], target);
        assert_ne!(parameters[1], string);
        assert_uncaptured_conditional_remap_is_unsupported(
            &mut fixture,
            source,
            &parameters,
            &[target, string],
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("RequiredKeys"), declared);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn deferred_conditional_remap_rejects_uncaptured_enclosing_parameters() {
        let mut fixture = Fixture::new(concat!(
            "function outer<Outer>() { ",
            "type Select<Own> = Own extends string ? Outer : boolean; ",
            "}",
        ));
        let source = fixture.declared_alias("Select");
        let own = fixture.type_parameter("Own");
        let outer = fixture.type_parameter("Outer");
        let proof = validated_conditional_production(&fixture.store, source).unwrap();
        assert_eq!(proof.definition.outer_type_parameters, [own]);
        assert_eq!(
            proof.definition.alias.as_ref().unwrap().type_arguments,
            [own]
        );
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_uncaptured_conditional_remap_is_unsupported(
            &mut fixture,
            source,
            &[outer],
            &[number],
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Select"), source);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check both formal-node caches against one real warm remap and restore it.
    fn deferred_conditional_remap_keeps_parameter_node_cache_errors_typed() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        for corrupt_symbol in [false, true] {
            let mut fixture = Fixture::new(concat!(
                "type Select<Value> = Value extends string ? number : boolean; ",
                "type Next<Other> = Other;",
            ));
            let source = fixture.declared_alias("Select");
            let owner = fixture.alias_symbol("Select");
            let other_owner = fixture.alias_symbol("Next");
            let parameter = fixture.type_parameter("Value");
            let argument = fixture.type_parameter("Other");
            let parameter_owner =
                cached_ordinary_type_parameter_owner(&fixture.store, parameter).unwrap();
            let parameter_node = fixture
                .store
                .symbol(parameter_owner)
                .unwrap()
                .declarations()
                .unwrap()[0];
            assert!(fixture.store.ensure_type_node_links(parameter_node));
            assert!(fixture.store.ensure_symbol_node_links(parameter_node));
            let original_types = fixture
                .store
                .type_node_links(parameter_node)
                .unwrap()
                .clone();
            let original_symbols = fixture
                .store
                .symbol_node_links(parameter_node)
                .unwrap()
                .clone();
            let result =
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument])
                    .unwrap();
            let original = conditional_snapshot(&fixture.store, source).unwrap();
            let mapped = conditional_snapshot(&fixture.store, result).unwrap();
            let cache = fixture
                .store
                .conditional_root(original.root)
                .unwrap()
                .instantiations()
                .clone();
            let mut types = original_types.clone();
            let mut symbols = original_symbols.clone();
            if corrupt_symbol {
                symbols.resolved_symbol = Some(other_owner);
            } else {
                types.resolved_type =
                    Some(fixture.store.intrinsic_bootstrap().unwrap().number_type);
            }
            assert!(
                fixture
                    .store
                    .set_type_node_links(parameter_node, types.clone())
            );
            assert!(
                fixture
                    .store
                    .set_symbol_node_links(parameter_node, symbols.clone())
            );
            let before = conditional_allocation_counts(&fixture.store);
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            for _ in 0..2 {
                assert_eq!(
                    conditional_remap_projection(&fixture.store, source),
                    Err(ConditionalTypeError::InvalidAliasSymbol(owner))
                );
                assert_eq!(
                    cached_instantiation_with_vector(
                        &fixture.store,
                        source,
                        &[parameter],
                        &[argument],
                        None,
                        None,
                    ),
                    Err(InstantiationError::InvalidType(source))
                );
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        &mut fixture.store,
                        source,
                        &[parameter],
                        &[argument],
                        None,
                        &mut session,
                    ),
                    Err(InstantiationError::InvalidType(source))
                );
                assert_eq!(session.query_count(), 0);
                assert_eq!(session.limit_event_count(), 0);
                assert_eq!(conditional_allocation_counts(&fixture.store), before);
                assert_eq!(fixture.store.type_node_links(parameter_node), Some(&types));
                assert_eq!(
                    fixture.store.symbol_node_links(parameter_node),
                    Some(&symbols)
                );
                assert_eq!(
                    conditional_snapshot(&fixture.store, source).unwrap(),
                    original
                );
                assert_eq!(
                    conditional_snapshot(&fixture.store, result).unwrap(),
                    mapped
                );
                assert_eq!(
                    fixture
                        .store
                        .conditional_root(original.root)
                        .unwrap()
                        .instantiations(),
                    &cache
                );
            }
            assert!(
                fixture
                    .store
                    .set_type_node_links(parameter_node, original_types)
            );
            assert!(
                fixture
                    .store
                    .set_symbol_node_links(parameter_node, original_symbols)
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    &fixture.store,
                    source,
                    &[parameter],
                    &[argument],
                    None,
                    None,
                ),
                Ok(Some(result))
            );
            assert_eq!(
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument]),
                Ok(result)
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), before);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep source order, mapper order, and later branch demand together.
    fn deferred_conditional_remap_keeps_source_order_and_lazy_branch_caches() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        for declaration_first in [false, true] {
            let mut fixture = Fixture::new(concat!(
                "type Select<Check, Value> = Check extends string ? Value : boolean; ",
                "type Forward<Left, Right> = Select<Right, Left>; ",
                "type Next<NewLeft, NewRight> = NewLeft;",
            ));
            if declaration_first {
                fixture.declared_alias("Select");
            }
            let source = fixture.declared_alias("Forward");
            let left = fixture.type_parameter("Left");
            let right = fixture.type_parameter("Right");
            let new_left = fixture.type_parameter("NewLeft");
            let new_right = fixture.type_parameter("NewRight");
            let value = fixture.type_parameter("Value");
            let owner = fixture.alias_symbol("Forward");
            let projection = conditional_remap_projection(&fixture.store, source).unwrap();
            assert_eq!(projection.arguments(), &[right, left]);
            assert_eq!(
                projection.alias(),
                Some(ConditionalAliasIdentity {
                    symbol: owner,
                    type_arguments: &[left, right],
                })
            );
            let source_data = conditional_snapshot(&fixture.store, source).unwrap();
            let source_alias = fixture.store.type_alias_links(owner).cloned();
            let nodes = fixture
                .parsed
                .arena
                .iter()
                .map(|(node, _)| NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
                .collect::<Vec<_>>();
            let node_links = |store: &CanonicalTypeMapperStore| {
                nodes
                    .iter()
                    .map(|node| store.type_node_links(*node).cloned())
                    .collect::<Vec<_>>()
            };
            let original_links = node_links(&fixture.store);
            assert_eq!(
                cached_instantiation_with_vector(
                    &fixture.store,
                    source,
                    &[left, right],
                    &[new_left, new_right],
                    None,
                    None,
                ),
                Ok(None)
            );
            let result = instantiate_type_with_vector(
                &mut fixture.store,
                source,
                &[left, right],
                &[new_left, new_right],
            )
            .unwrap();
            let mapped = conditional_remap_projection(&fixture.store, result).unwrap();
            assert_eq!(mapped.arguments(), &[new_right, new_left]);
            assert_eq!(mapped.parameters(), projection.parameters());
            assert_eq!(
                mapped.production.alias_reference,
                projection.production.alias_reference
            );
            assert_eq!(
                mapped.alias(),
                Some(ConditionalAliasIdentity {
                    symbol: owner,
                    type_arguments: &[new_left, new_right],
                })
            );
            let result_data = conditional_snapshot(&fixture.store, result).unwrap();
            assert_eq!(result_data.root, source_data.root);
            assert_eq!(result_data.check_type, new_right);
            assert_eq!(result_data.extends_type, source_data.extends_type);
            assert!(result_data.resolved_true_type.is_none());
            assert!(result_data.resolved_false_type.is_none());
            assert!(result_data.resolved_inferred_true_type.is_none());
            assert_eq!(
                conditional_snapshot(&fixture.store, source).unwrap(),
                source_data
            );
            assert_eq!(node_links(&fixture.store), original_links);
            assert_eq!(fixture.store.type_alias_links(owner).cloned(), source_alias);
            let warm = conditional_allocation_counts(&fixture.store);
            for _ in 0..2 {
                assert_eq!(fixture.declared_alias("Forward"), source);
                assert_eq!(
                    cached_instantiation_with_vector(
                        &fixture.store,
                        source,
                        &[left, right],
                        &[new_left, new_right],
                        None,
                        None,
                    ),
                    Ok(Some(result))
                );
                assert_eq!(
                    instantiate_type_with_vector(
                        &mut fixture.store,
                        source,
                        &[left, right],
                        &[new_left, new_right],
                    ),
                    Ok(result)
                );
                assert_eq!(conditional_allocation_counts(&fixture.store), warm);
                assert_eq!(node_links(&fixture.store), original_links);
            }

            // A later legitimate source branch demand must not invalidate the
            // remap proof. The raw branch is Value, not a cached mapped result.
            let boolean = fixture.store.intrinsic_bootstrap().unwrap().boolean_type;
            assert_eq!(
                get_true_type_from_conditional_type(
                    &mut fixture.store,
                    result,
                    branches(value, boolean),
                    None,
                    None,
                ),
                Ok(new_left)
            );
            assert_eq!(
                get_false_type_from_conditional_type(
                    &mut fixture.store,
                    result,
                    branches(value, boolean),
                    None,
                    None,
                ),
                Ok(boolean)
            );
            let warm = conditional_allocation_counts(&fixture.store);
            assert_eq!(
                instantiate_type_with_vector(
                    &mut fixture.store,
                    source,
                    &[left, right],
                    &[new_left, new_right],
                ),
                Ok(result)
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), warm);
            assert_eq!(
                conditional_snapshot(&fixture.store, source).unwrap(),
                source_data
            );
        }
    }

    #[test]
    fn deferred_conditional_remap_does_not_use_a_warm_concrete_result() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        for concrete_first in [false, true] {
            let mut fixture =
                Fixture::new("type Select<Value> = Value extends string ? number : boolean;");
            let source = fixture.declared_alias("Select");
            let parameter = fixture.type_parameter("Value");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, boolean) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            );
            if concrete_first {
                assert_eq!(
                    get_conditional_type_instantiation(
                        &mut fixture.store,
                        ConditionalTypeInstantiation {
                            conditional_type: source,
                            type_arguments: &[string],
                            branches: branches(number, boolean),
                            alias: None,
                            for_constraint: false,
                        },
                        None,
                        None,
                    ),
                    Ok(number)
                );
            }
            let root = conditional_snapshot(&fixture.store, source).unwrap().root;
            let root_cache = fixture
                .store
                .conditional_root(root)
                .unwrap()
                .instantiations()
                .clone();
            let before = conditional_allocation_counts(&fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    cached_instantiation_with_vector(
                        &fixture.store,
                        source,
                        &[parameter],
                        &[string],
                        None,
                        None,
                    ),
                    Err(InstantiationError::UnsupportedType(source))
                );
                assert_eq!(
                    instantiate_type_with_vector(
                        &mut fixture.store,
                        source,
                        &[parameter],
                        &[string]
                    ),
                    Err(InstantiationError::UnsupportedType(source))
                );
                assert_eq!(conditional_allocation_counts(&fixture.store), before);
                assert_eq!(
                    fixture
                        .store
                        .conditional_root(root)
                        .unwrap()
                        .instantiations(),
                    &root_cache
                );
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each corruption is restored before replaying the same source request.
    fn deferred_conditional_remap_rejects_and_restores_source_and_result_caches() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        for corruption in 0..10 {
            let mut fixture = Fixture::new(concat!(
                "type Select<Value> = Value extends string ? number : boolean; ",
                "type Forward<Other> = Select<Other>; type Next<After> = After;",
            ));
            let source = fixture.declared_alias("Forward");
            let parameter = fixture.type_parameter("Other");
            let argument = fixture.type_parameter("After");
            let result =
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument])
                    .unwrap();
            let projection = conditional_remap_projection(&fixture.store, source).unwrap();
            let root = projection.production.definition.root;
            let source_owner = projection.alias().unwrap().symbol;
            let root_owner = projection
                .production
                .definition
                .alias
                .as_ref()
                .unwrap()
                .symbol;
            let original_source_alias_links = fixture
                .store
                .type_alias_links(source_owner)
                .unwrap()
                .clone();
            let original_root_alias_links =
                fixture.store.type_alias_links(root_owner).unwrap().clone();
            let key = remap_cache_key(
                &fixture.store,
                &projection,
                &[argument],
                Some(ConditionalAliasIdentity {
                    symbol: projection.alias().unwrap().symbol,
                    type_arguments: &[argument],
                }),
            )
            .unwrap();
            let original_cache = fixture
                .store
                .conditional_root(root)
                .unwrap()
                .instantiations()
                .clone();
            let original_root_alias = fixture.store.conditional_root(root).unwrap().alias();
            let result_data = conditional_snapshot(&fixture.store, result).unwrap();
            let alias = fixture.store.type_payload(result).unwrap().alias().unwrap();
            let original_alias_arguments = fixture
                .store
                .type_alias(alias)
                .unwrap()
                .type_arguments()
                .map(<[TypeId]>::to_vec);
            let reference = projection.production.alias_reference.unwrap();
            let original_reference_links =
                fixture.store.type_node_links(reference).unwrap().clone();
            let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
            match corruption {
                0 | 1 => {
                    let TypeCacheState::Allocated(mut cache) = original_cache.clone() else {
                        unreachable!()
                    };
                    assert_eq!(cache.remove(&key), Some(result));
                    if corruption == 1 {
                        cache.insert(key, source);
                    }
                    assert!(fixture.store.set_conditional_root_instantiations(
                        root,
                        TypeCacheState::Allocated(cache)
                    ));
                }
                2 => {
                    assert!(fixture.store.set_conditional_resolution(
                        result, None, None, None, None, None, None, None,
                    ));
                }
                3 => assert!(
                    fixture
                        .store
                        .set_type_alias_arguments(alias, Some(vec![number]))
                ),
                4 => assert!(fixture.store.set_conditional_root_alias(root, None)),
                5 => {
                    let mut links = original_reference_links.clone();
                    links.resolved_type = Some(number);
                    assert!(fixture.store.set_type_node_links(reference, links));
                }
                6..=8 => {
                    let mut links = original_source_alias_links.clone();
                    match corruption {
                        6 => links.declared_type = Some(number),
                        7 => links.type_parameters = Some(vec![argument]),
                        8 => {
                            let key = super::super::declared::type_list_key(&[parameter]);
                            assert_eq!(
                                links.instantiations.as_mut().unwrap().insert(key, number),
                                Some(source)
                            );
                        }
                        _ => unreachable!(),
                    }
                    assert!(fixture.store.set_type_alias_links(source_owner, links));
                }
                9 => {
                    let mut links = original_root_alias_links.clone();
                    links.declared_type = Some(number);
                    assert!(fixture.store.set_type_alias_links(root_owner, links));
                }
                _ => unreachable!(),
            }
            let before = conditional_allocation_counts(&fixture.store);
            let link_counts = fixture.store.checker_link_allocated_lengths();
            let poisoned_source_alias_links = fixture.store.type_alias_links(source_owner).cloned();
            let poisoned_root_alias_links = fixture.store.type_alias_links(root_owner).cloned();
            let poisoned_cache = fixture
                .store
                .conditional_root(root)
                .unwrap()
                .instantiations()
                .clone();
            for _ in 0..2 {
                assert_eq!(
                    cached_instantiation_with_vector(
                        &fixture.store,
                        source,
                        &[parameter],
                        &[argument],
                        None,
                        None,
                    ),
                    Err(InstantiationError::InvalidType(source)),
                    "corruption {corruption}"
                );
                let mut session = InstantiationSession::new(InstantiationLimits::default());
                let mark = session.limit_event_mark();
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        &mut fixture.store,
                        source,
                        &[parameter],
                        &[argument],
                        None,
                        &mut session,
                    ),
                    Err(InstantiationError::InvalidType(source)),
                    "corruption {corruption}"
                );
                assert_eq!(session.limit_event_mark(), mark);
                assert_eq!(conditional_allocation_counts(&fixture.store), before);
                assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
                assert_eq!(
                    fixture.store.type_alias_links(source_owner).cloned(),
                    poisoned_source_alias_links
                );
                assert_eq!(
                    fixture.store.type_alias_links(root_owner).cloned(),
                    poisoned_root_alias_links
                );
                assert_eq!(
                    fixture
                        .store
                        .conditional_root(root)
                        .unwrap()
                        .instantiations(),
                    &poisoned_cache
                );
            }
            assert!(
                fixture
                    .store
                    .set_conditional_root_instantiations(root, original_cache)
            );
            assert!(
                fixture
                    .store
                    .set_conditional_root_alias(root, original_root_alias)
            );
            assert!(
                fixture
                    .store
                    .set_type_alias_arguments(alias, original_alias_arguments)
            );
            assert!(
                fixture
                    .store
                    .set_type_node_links(reference, original_reference_links)
            );
            assert!(
                fixture
                    .store
                    .set_type_alias_links(source_owner, original_source_alias_links)
            );
            assert!(
                fixture
                    .store
                    .set_type_alias_links(root_owner, original_root_alias_links)
            );
            assert!(fixture.store.set_conditional_resolution(
                result,
                result_data.resolved_true_type,
                result_data.resolved_false_type,
                result_data.resolved_inferred_true_type,
                result_data.resolved_default_constraint,
                result_data.resolved_constraint_of_distributive,
                result_data.mapper,
                result_data.combined_mapper,
            ));
            let warm = conditional_allocation_counts(&fixture.store);
            assert_eq!(
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument]),
                Ok(result)
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), warm);
        }
    }

    #[test]
    fn deferred_conditional_remap_checks_later_alias_publication() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        let mut fixture = Fixture::new(concat!(
            "type Select<Value> = Value extends string ? number : boolean; ",
            "type Next<Other> = Other;",
        ));
        let node = fixture.conditional();
        let owner = fixture.alias_symbol("Select");
        let parameter = fixture.type_parameter("Value");
        let argument = fixture.type_parameter("Other");
        let source = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let source = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(node)
            .unwrap();
            assert!(diagnostics.is_empty());
            source
        };
        assert!(
            fixture
                .store
                .conditional_query_production(ConditionalQueryKey::AliasDeclaration(owner))
                .is_none()
        );
        assert!(
            fixture
                .store
                .type_alias_links(owner)
                .is_none_or(|links| links.declared_type.is_none())
        );
        let result =
            instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument])
                .unwrap();
        assert_eq!(fixture.declared_alias("Select"), source);
        let links = fixture.store.type_alias_links(owner).unwrap().clone();
        assert_eq!(links.declared_type, Some(source));
        let warm = conditional_allocation_counts(&fixture.store);
        for _ in 0..2 {
            assert_eq!(
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument]),
                Ok(result)
            );
            assert_eq!(fixture.store.type_alias_links(owner), Some(&links));
            assert_eq!(conditional_allocation_counts(&fixture.store), warm);
        }
    }

    #[test]
    fn conditional_alias_roots_keep_parentheses_and_unused_local_parameters() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T, Unused> = ((T extends string ? number : boolean)); ",
            "type Reduced = Select<string, never>;",
        ));
        let declared = fixture.declared_alias("Select");
        let parameters = [
            fixture.type_parameter("T"),
            fixture.type_parameter("Unused"),
        ];
        let symbol = fixture.alias_symbol("Select");
        assert_eq!(
            conditional_alias_projection(&fixture.store, declared),
            Ok(Some(ConditionalAliasIdentity {
                symbol,
                type_arguments: &parameters
            })),
        );
        let data = conditional_snapshot(&fixture.store, declared).unwrap();
        let root = fixture.store.conditional_root(data.root).unwrap();
        assert_eq!(root.outer_type_parameters(), Some(parameters.as_slice()));
        assert_eq!(
            root.alias(),
            fixture.store.type_payload(declared).unwrap().alias()
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Select"), declared);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);

        let aliases = fixture.store.type_alias_len();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(fixture.declared_alias("Reduced"), number);
        assert!(
            fixture
                .store
                .type_payload(number)
                .unwrap()
                .alias()
                .is_none()
        );
        assert_eq!(fixture.store.type_alias_len(), aliases);
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Reduced"), number);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn conditional_alias_references_keep_the_requested_owner_and_compose_root_arguments() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T, Unused> = ((T extends string ? number : boolean)); ",
            "type Forward<Value> = Select<Value, never>; ",
            "type Reduced = Forward<string>;",
        ));
        let forwarded = fixture.declared_alias("Forward");
        let parameter = fixture.type_parameter("Value");
        let symbol = fixture.alias_symbol("Forward");
        assert_eq!(
            conditional_alias_projection(&fixture.store, forwarded),
            Ok(Some(ConditionalAliasIdentity {
                symbol,
                type_arguments: &[parameter]
            })),
        );
        let data = conditional_snapshot(&fixture.store, forwarded).unwrap();
        let root = fixture.store.conditional_root(data.root).unwrap();
        let root_alias = stored_alias_identity(&fixture.store, root.alias().unwrap()).unwrap();
        assert_eq!(root_alias.symbol, fixture.alias_symbol("Select"));
        assert_eq!(root_alias.type_arguments.len(), 2);
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(fixture.declared_alias("Reduced"), number);
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Forward"), forwarded);
        assert_eq!(fixture.declared_alias("Reduced"), number);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn conditional_alias_reduced_outer_keeps_inner_identity_on_warm_queries() {
        let mut fixture = Fixture::new(concat!(
            "type Inner<T> = T extends string ? number : boolean; ",
            "type Outer<U> = string extends string ? Inner<U> : never; ",
            "type Result = Outer<string>;",
        ));
        let outer = fixture.declared_alias("Outer");
        let parameter = fixture.type_parameter("U");
        assert_eq!(
            conditional_alias_projection(&fixture.store, outer),
            Ok(Some(ConditionalAliasIdentity {
                symbol: fixture.alias_symbol("Inner"),
                type_arguments: &[parameter],
            }))
        );
        let declaration = fixture.alias_declaration("Outer");
        let NodeData::TypeAliasDeclaration(source) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let node = NodeRef::new(declaration.arena, declaration.file, source.type_);
        let alias = conditional_query_alias(&fixture.store, node)
            .unwrap()
            .unwrap();
        assert_eq!(
            fixture.store.type_alias(alias).unwrap().symbol(),
            Some(fixture.alias_symbol("Outer"))
        );
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(fixture.declared_alias("Result"), number);
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Outer"), outer);
        assert_eq!(fixture.declared_alias("Result"), number);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn conditional_alias_distribution_retains_the_requested_union_alias() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? 1 : 2; ",
            "type Result = Select<string | number>; type Other = boolean;",
        ));
        let result = fixture.declared_alias("Result");
        let record = fixture.store.type_payload(result).unwrap();
        let TypeData::Union(union) = record.data() else {
            panic!("distribution must preserve both literal results");
        };
        assert_eq!(union.union.types.len(), 2);
        let alias = fixture.store.type_alias(record.alias().unwrap()).unwrap();
        assert_eq!(alias.symbol(), Some(fixture.alias_symbol("Result")));
        assert!(alias.type_arguments().unwrap_or_default().is_empty());
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Result"), result);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);

        let declaration = fixture.alias_declaration("Result");
        let NodeData::TypeAliasDeclaration(source) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let reference = NodeRef::new(declaration.arena, declaration.file, source.type_);
        let other = fixture.alias_symbol("Other");
        let alias = fixture.store.alloc_type_alias(Some(other)).unwrap();
        assert!(fixture.store.set_type_alias(result, Some(alias)));
        let before = conditional_allocation_counts(&fixture.store);
        assert!(validate_conditional_reference_result(&fixture.store, reference, result).is_err());
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_projection_rejects_uncached_clones_with_matching_aliases() {
        let mut fixture = Fixture::new("type Select<T> = T extends string ? number : boolean;");
        let original = fixture.declared_alias("Select");
        let data = conditional_snapshot(&fixture.store, original).unwrap();
        let original_alias = fixture.store.type_payload(original).unwrap().alias();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        for check in [data.check_type, number] {
            let clone = fixture
                .store
                .alloc_conditional_type(data.root, check, data.extends_type, None, None)
                .unwrap();
            assert!(fixture.store.set_type_alias(clone, original_alias));
            let before = conditional_allocation_counts(&fixture.store);
            assert!(conditional_alias_projection(&fixture.store, clone).is_err());
            assert!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: clone,
                        type_arguments: &[number],
                        branches: branches(number, number),
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None
                )
                .is_err()
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), before);
        }
        let proof = fixture
            .store
            .conditional_type_production(original)
            .unwrap()
            .clone();
        let before = conditional_allocation_counts(&fixture.store);
        assert!(!fixture.store.publish_conditional_type_production(proof));
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_rejects_unexpected_combined_mapper_without_writes() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? T : never; ",
            "type Forward<U> = Select<U>;",
        ));
        let forwarded = fixture.declared_alias("Forward");
        let parameter = fixture.type_parameter("U");
        let original = conditional_snapshot(&fixture.store, forwarded).unwrap();
        assert!(original.combined_mapper.is_none());
        let root = original.root;
        let checked = fixture.store.conditional_root(root).unwrap().check_type();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (number, never) = (bootstrap.number_type, bootstrap.never_type);
        let unexpected = fixture
            .store
            .new_simple_type_mapper(checked, number)
            .unwrap();
        assert!(fixture.store.set_conditional_resolution(
            forwarded,
            original.resolved_true_type,
            original.resolved_false_type,
            original.resolved_inferred_true_type,
            original.resolved_default_constraint,
            original.resolved_constraint_of_distributive,
            original.mapper,
            Some(unexpected),
        ));
        let forward_symbol = fixture.alias_symbol("Forward");
        let select_symbol = fixture.alias_symbol("Select");
        let snapshot = |store: &CanonicalTypeMapperStore| {
            let TypeData::Conditional(data) = store.type_payload(forwarded).unwrap().data() else {
                panic!("the forwarded type must retain its conditional payload");
            };
            (
                conditional_allocation_counts(store),
                store.checker_link_allocated_lengths(),
                store.type_resolution_len(),
                store.type_resolution_start(),
                data.clone(),
                store
                    .conditional_root(root)
                    .unwrap()
                    .instantiations()
                    .clone(),
                store.type_alias_links(forward_symbol).cloned(),
                store.type_alias_links(select_symbol).cloned(),
            )
        };
        let before = snapshot(&fixture.store);
        assert_eq!(
            conditional_alias_projection(&fixture.store, forwarded),
            Err(ConditionalTypeError::InvalidConditional(forwarded))
        );
        assert_eq!(snapshot(&fixture.store), before);
        assert!(fixture.try_declared_alias("Forward").is_err());
        assert_eq!(snapshot(&fixture.store), before);
        assert_eq!(
            get_inferred_true_type_from_conditional_type(
                &mut fixture.store,
                forwarded,
                branches(checked, never),
                None,
                None,
            ),
            Err(ConditionalTypeError::InvalidConditional(forwarded))
        );
        assert_eq!(snapshot(&fixture.store), before);

        assert!(fixture.store.set_conditional_resolution(
            forwarded,
            original.resolved_true_type,
            original.resolved_false_type,
            original.resolved_inferred_true_type,
            original.resolved_default_constraint,
            original.resolved_constraint_of_distributive,
            original.mapper,
            original.combined_mapper,
        ));
        assert_eq!(fixture.declared_alias("Forward"), forwarded);
        assert_eq!(
            get_inferred_true_type_from_conditional_type(
                &mut fixture.store,
                forwarded,
                branches(checked, never),
                None,
                None,
            ),
            Ok(parameter)
        );
    }

    #[test]
    fn conditional_alias_source_rejects_an_unrelated_owner_and_matching_cache_entry() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? number : boolean; ",
            "type Forward<U> = Select<U>; type Other<V> = V;",
        ));
        let forwarded = fixture.declared_alias("Forward");
        let parameter = fixture.type_parameter("U");
        let root = conditional_snapshot(&fixture.store, forwarded)
            .unwrap()
            .root;
        let other = fixture.alias_symbol("Other");
        let alias = fixture.store.alloc_type_alias(Some(other)).unwrap();
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![parameter]))
        );
        assert!(fixture.store.set_type_alias(forwarded, Some(alias)));
        let key = conditional_type_key(
            &mut fixture.store,
            &[parameter],
            Some(ConditionalAliasIdentity {
                symbol: other,
                type_arguments: &[parameter],
            }),
            false,
        )
        .unwrap();
        let TypeCacheState::Allocated(mut cache) = fixture
            .store
            .conditional_root(root)
            .unwrap()
            .instantiations()
            .clone()
        else {
            unreachable!();
        };
        cache.insert(key, forwarded);
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(root, TypeCacheState::Allocated(cache))
        );
        let before = conditional_allocation_counts(&fixture.store);
        assert!(conditional_alias_projection(&fixture.store, forwarded).is_err());
        assert!(fixture.try_declared_alias("Forward").is_err());
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_source_rejects_swapped_arguments_and_matching_cache_entry() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T, U> = T extends string ? U : boolean; ",
            "type Forward<Left, Right> = Select<Right, Left>;",
        ));
        let forwarded = fixture.declared_alias("Forward");
        let left = fixture.type_parameter("Left");
        let right = fixture.type_parameter("Right");
        let symbol = fixture.alias_symbol("Forward");
        assert_eq!(
            conditional_alias_projection(&fixture.store, forwarded),
            Ok(Some(ConditionalAliasIdentity {
                symbol,
                type_arguments: &[left, right],
            }))
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Forward"), forwarded);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
        let root = conditional_snapshot(&fixture.store, forwarded)
            .unwrap()
            .root;
        let alias = fixture
            .store
            .type_payload(forwarded)
            .unwrap()
            .alias()
            .unwrap();
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![right, left]))
        );
        let key = conditional_type_key(
            &mut fixture.store,
            &[right, left],
            Some(ConditionalAliasIdentity {
                symbol,
                type_arguments: &[right, left],
            }),
            false,
        )
        .unwrap();
        let TypeCacheState::Allocated(mut cache) = fixture
            .store
            .conditional_root(root)
            .unwrap()
            .instantiations()
            .clone()
        else {
            unreachable!();
        };
        cache.insert(key, forwarded);
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(root, TypeCacheState::Allocated(cache))
        );
        let before = conditional_allocation_counts(&fixture.store);
        assert!(conditional_alias_projection(&fixture.store, forwarded).is_err());
        assert!(fixture.try_declared_alias("Forward").is_err());
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_instantiations_map_default_arguments_and_keep_warm_identity() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? number : boolean; ",
            "type Other<U> = U;",
        ));
        let declared = fixture.declared_alias("Select");
        let parameter = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (number, boolean) = (bootstrap.number_type, bootstrap.boolean_type);
        let arguments = [parameter];
        let request = ConditionalTypeInstantiation {
            conditional_type: declared,
            type_arguments: &arguments,
            branches: branches(number, boolean),
            alias: None,
            for_constraint: false,
        };
        let mapped =
            get_conditional_type_instantiation(&mut fixture.store, request, None, None).unwrap();
        assert_eq!(
            conditional_alias_projection(&fixture.store, mapped),
            Ok(Some(ConditionalAliasIdentity {
                symbol: fixture.alias_symbol("Select"),
                type_arguments: &arguments,
            })),
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(
            get_conditional_type_instantiation(&mut fixture.store, request, None, None),
            Ok(mapped)
        );
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn conditional_alias_cache_validation_rejects_changed_arguments_without_allocating() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? number : boolean; ",
            "type Other<U> = U;",
        ));
        let declared = fixture.declared_alias("Select");
        let parameter = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (number, boolean) = (bootstrap.number_type, bootstrap.boolean_type);
        let arguments = [parameter];
        let request = ConditionalTypeInstantiation {
            conditional_type: declared,
            type_arguments: &arguments,
            branches: branches(number, boolean),
            alias: None,
            for_constraint: false,
        };
        let mapped =
            get_conditional_type_instantiation(&mut fixture.store, request, None, None).unwrap();
        let alias = fixture.store.type_payload(mapped).unwrap().alias().unwrap();
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![number]))
        );
        let before = conditional_allocation_counts(&fixture.store);
        assert!(
            get_conditional_type_instantiation(&mut fixture.store, request, None, None).is_err()
        );
        assert!(conditional_alias_projection(&fixture.store, mapped).is_err());
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![parameter]))
        );
        assert_eq!(
            get_conditional_type_instantiation(&mut fixture.store, request, None, None),
            Ok(mapped)
        );
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_requests_reject_foreign_arguments_and_wrong_root_owners_before_allocation()
    {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? number : boolean; ",
            "type Other<U> = U;",
        ));
        let foreign = Fixture::new("type Foreign = number;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, boolean) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
        );
        let wrong_owner = fixture.alias_symbol("Other");
        let alias = fixture.store.alloc_type_alias(Some(wrong_owner)).unwrap();
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![parameter]))
        );
        let before = conditional_allocation_counts(&fixture.store);
        assert!(
            get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: string,
                    branches: branches(number, boolean),
                    infer_type_parameters: &[],
                    outer_type_parameters: &[parameter],
                    alias: Some(alias),
                },
                None
            )
            .is_err()
        );
        assert_eq!(conditional_allocation_counts(&fixture.store), before);

        let declared = fixture.declared_alias("Select");
        let foreign_argument = foreign.store.intrinsic_bootstrap().unwrap().number_type;
        for (conditional_type, argument) in
            [(declared, foreign_argument), (foreign_argument, parameter)]
        {
            let before = conditional_allocation_counts(&fixture.store);
            assert!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type,
                        type_arguments: &[argument],
                        branches: branches(number, boolean),
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None
                )
                .is_err()
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), before);
        }
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
    fn indexed_conditional_operands_preserve_nested_type_parameter_dependencies() {
        let mut fixture =
            Fixture::new("type Result<Object, Key> = Object extends Key ? Object : never;");
        let object = fixture.type_parameter("Object");
        let key = fixture.type_parameter("Key");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, never) = (bootstrap.string_type, bootstrap.never_type);
        let keyof_object = fixture
            .store
            .alloc_index_type(object, IndexFlags::NONE)
            .unwrap();
        let object_access = fixture
            .store
            .alloc_indexed_access_type(object, string, AccessFlags::NONE)
            .unwrap();
        let key_access = fixture
            .store
            .alloc_indexed_access_type(string, key, AccessFlags::NONE)
            .unwrap();
        let nested_access = fixture
            .store
            .alloc_indexed_access_type(keyof_object, key, AccessFlags::NONE)
            .unwrap();

        for (type_, contains_object, contains_key) in [
            (keyof_object, true, false),
            (object_access, true, false),
            (key_access, false, true),
            (nested_access, true, true),
        ] {
            assert_eq!(
                contains_mapped_type_parameter(
                    &fixture.store,
                    type_,
                    &[object],
                    &mut HashSet::new(),
                ),
                Ok(contains_object),
            );
            assert_eq!(
                contains_mapped_type_parameter(&fixture.store, type_, &[key], &mut HashSet::new()),
                Ok(contains_key),
            );
            assert_eq!(
                contains_type_parameter(&fixture.store, type_, &HashSet::from([object])),
                Ok(contains_key),
            );
            assert_eq!(
                contains_type_parameter(&fixture.store, type_, &HashSet::from([key])),
                Ok(contains_object),
            );
            assert_eq!(
                contains_type_parameter(&fixture.store, type_, &HashSet::from([object, key])),
                Ok(false),
            );
            assert_eq!(
                validate_conditional_operand(&fixture.store, type_, &mut HashSet::new()),
                Ok(()),
            );
        }

        let node = fixture.conditional();
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: nested_access,
                extends_type: string,
                branches: branches(string, never),
                infer_type_parameters: &[],
                outer_type_parameters: &[object, key],
                alias: None,
            },
            None,
        )
        .unwrap();
        assert!(matches!(
            fixture.store.type_payload(conditional).map(TypeRecord::data),
            Some(TypeData::Conditional(data)) if data.check_type == nested_access
        ));
    }

    #[test]
    fn indexed_conditional_operands_reject_malformed_nested_signatures() {
        let mut fixture = Fixture::new("type Result<T> = T extends string ? T : never;");
        let parameter = fixture.type_parameter("T");
        let malformed = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let signature = fixture
            .store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();
        assert!(fixture.store.set_structured_type_members(
            malformed,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));

        let keyof_malformed = fixture
            .store
            .alloc_index_type(malformed, IndexFlags::NONE)
            .unwrap();
        let malformed_object = fixture
            .store
            .alloc_indexed_access_type(malformed, parameter, AccessFlags::NONE)
            .unwrap();
        let malformed_index = fixture
            .store
            .alloc_indexed_access_type(parameter, malformed, AccessFlags::NONE)
            .unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
        );

        for type_ in [keyof_malformed, malformed_object, malformed_index] {
            assert_eq!(
                validate_conditional_operand(&fixture.store, type_, &mut HashSet::new()),
                Err(ConditionalTypeError::InvalidSignature(signature)),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len()
                ),
                before,
            );
        }
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
        let surrogate = encode_js_string(&JsString::from_units(vec![0xd800]));
        let surrogate_source = format!("{surrogate}abc");
        for (source, input, expected, selected) in [
            (
                "type Head<T> = T extends `${infer H}${infer R}` ? H : never;",
                "ABC",
                "A",
                "H",
            ),
            (
                "type Head<T> = T extends `${infer H}${infer R}` ? H : never;",
                "\u{3042}\u{3044}\u{3046}",
                "\u{3042}",
                "H",
            ),
            (
                "type Head<T> = T extends `${infer H}${infer R}` ? H : never;",
                "\u{1F600}abc",
                "\u{1F600}",
                "H",
            ),
            (
                "type Head<T> = T extends `${infer H}${infer R}` ? H : never;",
                surrogate_source.as_str(),
                surrogate.as_str(),
                "H",
            ),
            (
                "type Rest<T> = T extends `${infer H}${infer R}` ? R : never;",
                "\u{1F600}abc",
                "abc",
                "R",
            ),
            (
                "type Rest<T> = T extends `${infer H}${infer R}` ? R : never;",
                surrogate_source.as_str(),
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
                .regular_string_literal_type(input.to_owned())
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
    fn conditional_template_assignability_matches_patterns_and_unions() {
        let mut fixture = Fixture::new("type Pattern = `start-${string}`;");
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let target = fixture
            .store
            .get_template_literal_type(&["start-".to_owned(), String::new()], &[string])
            .unwrap();
        let matching = fixture
            .store
            .regular_string_literal_type("start-value".to_owned())
            .unwrap();
        let japanese = fixture
            .store
            .regular_string_literal_type("start-\u{3042}".to_owned())
            .unwrap();
        let mismatch = fixture
            .store
            .regular_string_literal_type("other-value".to_owned())
            .unwrap();
        let matching_union =
            canonical_anonymous_union(&mut fixture.store, &[matching, japanese]).unwrap();
        let mixed_union =
            canonical_anonymous_union(&mut fixture.store, &[matching, mismatch]).unwrap();

        for (source, expected) in [
            (matching, true),
            (japanese, true),
            (mismatch, false),
            (matching_union, true),
            (mixed_union, false),
        ] {
            assert_eq!(
                conditional_check_is_assignable(&mut fixture.store, source, target, None),
                Ok(expected),
                "source={source:?}"
            );
        }
    }

    #[test]
    fn template_inference_preserves_unconstrained_string_placeholders() {
        for (source, input, expected, first) in [
            (
                "type Head<T> = T extends `${infer H}${string}` ? H : never;",
                "ABC",
                "A",
                true,
            ),
            (
                "type Head<T> = T extends `${infer H}${string}` ? H : never;",
                "\u{3042}\u{3044}\u{3046}",
                "\u{3042}",
                true,
            ),
            (
                "type Rest<T> = T extends `${string}${infer R}` ? R : never;",
                "ABC",
                "BC",
                false,
            ),
            (
                "type Rest<T> = T extends `${string}${infer R}` ? R : never;",
                "\u{3042}\u{3044}\u{3046}",
                "\u{3044}\u{3046}",
                false,
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let inferred = fixture.type_parameter(if first { "H" } else { "R" });
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, never) = (bootstrap.string_type, bootstrap.never_type);
            let placeholders = if first {
                [inferred, string]
            } else {
                [string, inferred]
            };
            let template = fixture
                .store
                .get_template_literal_type(
                    &[String::new(), String::new(), String::new()],
                    &placeholders,
                )
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
                .regular_string_literal_type(input.to_owned())
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
    fn conditional_inference_uses_bound_generic_signature_constraints() {
        let mut fixture =
            Fixture::new("type H<X> = (<O extends X>() => O) extends (() => infer R) ? R : never;");
        let node = fixture.conditional();
        let outer = fixture.type_parameter("X");
        let local = fixture.type_parameter("O");
        let inferred = fixture.type_parameter("R");
        assert!(
            fixture
                .store
                .set_type_parameter_resolution(local, Some(outer), None, None, None)
        );

        let source = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let signature = fixture
            .store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                vec![local],
                None,
                Vec::new(),
                Some(local),
                None,
                0,
            )
            .unwrap();
        assert!(fixture.store.set_structured_type_members(
            source,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        let target = callable_object(&mut fixture.store, inferred, false);
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        assert_eq!(
            contains_type_parameter(&fixture.store, source, &HashSet::new()),
            Ok(true),
        );
        assert_eq!(
            contains_type_parameter(&fixture.store, source, &HashSet::from([outer])),
            Ok(false),
        );

        let branch_types = branches(inferred, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: source,
                extends_type: target,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: &[outer],
                alias: None,
            },
            None,
        )
        .unwrap();
        for argument in [string, number] {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[argument],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(argument),
            );
        }

        let original = fixture.store.signature(signature).unwrap();
        assert_eq!(original.type_parameters(), &[local]);
        assert_eq!(original.resolved_return_type(), Some(local));
        let Some(TypeData::TypeParameter(parameter)) =
            fixture.store.type_payload(local).map(TypeRecord::data)
        else {
            panic!("a signature-local generic parameter must remain intact")
        };
        assert_eq!(parameter.constraint, Some(outer));
    }

    #[test]
    fn declared_constructor_inference_maps_alias_arguments_and_checks_signatures() {
        let mut fixture = Fixture::new(concat!(
            "type Strings = { new(value: string): number }; ",
            "type Numbers = { new(value: number): string }; ",
            "type Extra = { new(value: string, extra: number): boolean }; ",
            "type Overloaded = { new(value: number): string; new(value: string): boolean }; ",
            "type Callable = { (value: string): boolean }; ",
            "type Extract<T, Value> = T extends { new(value: Value): infer Result } ",
            "? Result : never;",
        ));
        let strings = fixture.declared_alias("Strings");
        let numbers = fixture.declared_alias("Numbers");
        let extra = fixture.declared_alias("Extra");
        let overloaded = fixture.declared_alias("Overloaded");
        let callable = fixture.declared_alias("Callable");
        let conditional = fixture.declared_alias("Extract");
        let inferred = fixture.type_parameter("Result");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, boolean, any, unknown, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
            bootstrap.any_type,
            bootstrap.unknown_type,
            bootstrap.never_type,
        );
        let branch_types = branches(inferred, never);
        let cases = [
            (strings, string, number),
            (strings, number, never),
            (numbers, number, string),
            (extra, string, never),
            (overloaded, string, boolean),
            (callable, string, never),
            (any, string, unknown),
        ];

        for (source, argument, expected) in cases {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[source, argument],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(expected),
                "source={source:?}, argument={argument:?}",
            );
        }

        let union =
            canonical_anonymous_union(&mut fixture.store, &[strings, numbers, boolean]).unwrap();
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[union, string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(number),
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[union, string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(number),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn constructor_inference_rejects_poisoned_provenance_before_cached_results() {
        for corruption in 0..3 {
            let mut fixture = Fixture::new(concat!(
                "type Source = { new(): string }; ",
                "type Extract<T> = T extends { new(): infer Result } ? Result : never;",
            ));
            let source = fixture.declared_alias("Source");
            let conditional = fixture.declared_alias("Extract");
            let inferred = fixture.type_parameter("Result");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, never) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.never_type,
            );
            let branch_types = branches(inferred, never);
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
            );

            let root = conditional_snapshot(&fixture.store, conditional)
                .unwrap()
                .root;
            let target = fixture.store.conditional_root(root).unwrap().extends_type();
            let poisoned = match corruption {
                0 | 1 => {
                    let owner = if corruption == 0 { source } else { target };
                    let signature = fixture
                        .store
                        .type_payload(owner)
                        .and_then(|record| record.data().structured())
                        .and_then(|structured| structured.signatures.as_deref())
                        .and_then(|signatures| signatures.first())
                        .copied()
                        .unwrap();
                    assert!(
                        fixture
                            .store
                            .set_signature_resolved_return_type(signature, Some(number))
                    );
                    owner
                }
                2 => {
                    let signature = fixture
                        .store
                        .type_payload(source)
                        .and_then(|record| record.data().structured())
                        .and_then(|structured| structured.signatures.as_deref())
                        .and_then(|signatures| signatures.first())
                        .copied()
                        .unwrap();
                    let forged = fixture
                        .store
                        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
                        .unwrap();
                    assert!(fixture.store.set_structured_type_members(
                        forged,
                        None,
                        None,
                        None,
                        Some(vec![signature]),
                        None,
                    ));
                    forged
                }
                _ => unreachable!(),
            };
            let argument = if corruption == 2 { poisoned } else { source };
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture
                    .store
                    .conditional_root(root)
                    .unwrap()
                    .instantiations()
                    .clone(),
            );
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[argument],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Err(ConditionalTypeError::Relation(
                    RelationUnavailable::MalformedFunctionType(poisoned),
                )),
                "corruption case {corruption}",
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                    fixture
                        .store
                        .conditional_root(root)
                        .unwrap()
                        .instantiations()
                        .clone(),
                ),
                before,
                "corruption case {corruption}",
            );
        }
    }

    #[test]
    fn cached_distributive_constructor_constraints_revalidate_their_target() {
        let mut fixture =
            Fixture::new("type Extract<T> = T extends { new(): infer Result } ? Result : never;");
        let conditional = fixture.declared_alias("Extract");
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("Result");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        assert!(fixture.store.set_type_parameter_resolution(
            parameter,
            Some(string),
            None,
            None,
            None,
        ));
        let branch_types = branches(inferred, never);
        assert_eq!(
            get_constraint_of_distributive_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(None),
        );
        let target = conditional_snapshot(&fixture.store, conditional)
            .map(|data| data.extends_type)
            .unwrap();
        let signature = fixture
            .store
            .type_payload(target)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .and_then(|signatures| signatures.first())
            .copied()
            .unwrap();
        assert!(
            fixture
                .store
                .set_signature_resolved_return_type(signature, Some(number))
        );
        let before = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            get_constraint_of_distributive_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Err(ConditionalTypeError::Relation(
                RelationUnavailable::MalformedFunctionType(target),
            )),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
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

    #[test]
    fn tuple_inference_uses_fixed_constraints_for_adjacent_rest_and_variadic_elements() {
        for (declaration, rest_first) in [
            (
                "type Result<T> = T extends [...(infer C)[], ...infer B extends [any, any]] ? B : never;",
                true,
            ),
            (
                "type Result<T> = T extends [...infer A extends [any, any], ...(infer D)[]] ? A : never;",
                false,
            ),
        ] {
            let mut fixture = Fixture::new(declaration);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let rest_parameter = fixture.type_parameter(if rest_first { "C" } else { "D" });
            let variadic_parameter = fixture.type_parameter(if rest_first { "B" } else { "A" });
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (any, never) = (bootstrap.any_type, bootstrap.never_type);
            let required = fixture
                .store
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap();
            let rest = fixture
                .store
                .create_tuple_element_info(ElementFlags::REST, None)
                .unwrap();
            let variadic = fixture
                .store
                .create_tuple_element_info(ElementFlags::VARIADIC, None)
                .unwrap();
            let constraint = fixture
                .store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    &[any, any],
                    &[required, required],
                    false,
                ))
                .unwrap();
            assert!(fixture.store.set_type_parameter_resolution(
                variadic_parameter,
                Some(constraint),
                None,
                None,
                None,
            ));
            let (target_types, target_infos, inferred_parameters) = if rest_first {
                (
                    [rest_parameter, variadic_parameter],
                    [rest, variadic],
                    [rest_parameter, variadic_parameter],
                )
            } else {
                (
                    [variadic_parameter, rest_parameter],
                    [variadic, rest],
                    [variadic_parameter, rest_parameter],
                )
            };
            let target = fixture
                .store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    &target_types,
                    &target_infos,
                    false,
                ))
                .unwrap();
            let branch_types = branches(variadic_parameter, never);
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: target,
                    branches: branch_types,
                    infer_type_parameters: &inferred_parameters,
                    outer_type_parameters: &[parameter],
                    alias: None,
                },
                None,
            )
            .unwrap();

            let mut values = Vec::new();
            for value in [1.0, 2.0, 3.0, 4.0] {
                values.push(
                    fixture
                        .store
                        .regular_number_literal_type(ts_jsnum::Number::new(value))
                        .unwrap(),
                );
            }
            let expected_long = if rest_first {
                &values[2..]
            } else {
                &values[..2]
            };
            let cases: &[(&[TypeId], Option<&[TypeId]>)] = &[
                (&values[..2], Some(&values[..2])),
                (&values[..], Some(expected_long)),
                (&values[..1], None),
            ];
            for (elements, expected) in cases {
                let infos = vec![required; elements.len()];
                let source = fixture
                    .store
                    .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                        elements, &infos, false,
                    ))
                    .unwrap();
                let expected = if let Some(elements) = expected {
                    let infos = vec![required; elements.len()];
                    fixture
                        .store
                        .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                            elements, &infos, false,
                        ))
                        .unwrap()
                } else {
                    never
                };
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
                    Ok(expected),
                    "rest_first={rest_first}, elements={elements:?}",
                );
            }
        }
    }

    #[test]
    fn tuple_assignability_aligns_rest_elements_with_required_suffixes() {
        let mut fixture = Fixture::new("type Target = [...number[], string];");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        let required = fixture
            .store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let rest = fixture
            .store
            .create_tuple_element_info(ElementFlags::REST, None)
            .unwrap();
        let target = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number, string],
                &[rest, required],
                false,
            ))
            .unwrap();

        let cases: &[(&[TypeId], bool)] = &[
            (&[number, number, string], true),
            (&[string], true),
            (&[number, number, number], false),
            (&[string, string], false),
        ];
        for (elements, expected) in cases {
            let infos = vec![required; elements.len()];
            let source = fixture
                .store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    elements, &infos, false,
                ))
                .unwrap();
            assert_eq!(
                conditional_check_is_assignable(&mut fixture.store, source, target, None),
                Ok(*expected),
                "elements={elements:?}"
            );
        }

        let prefixed_target = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string, number, string],
                &[required, rest, required],
                false,
            ))
            .unwrap();
        for elements in [&[string, number, number, string][..], &[string, string][..]] {
            let infos = vec![required; elements.len()];
            let source = fixture
                .store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    elements, &infos, false,
                ))
                .unwrap();
            assert_eq!(
                conditional_check_is_assignable(&mut fixture.store, source, prefixed_target, None),
                Ok(true),
                "elements={elements:?}"
            );
        }
    }
}
